/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author Martin Odersky
 */

package scala.tools.nsc
package transform

import symtab._
import Flags._
import scala.collection._
import scala.language.postfixOps
import scala.reflect.internal.Symbols
import scala.collection.mutable.LinkedHashMap

abstract class Delambdafy extends Transform with TypingTransformers with ast.TreeDSL {
  import global._
  import definitions._
  import CODE._

  /** the following two members override abstract members in Transform */
  val phaseName: String = "delambdafy"

  protected def newTransformer(unit: CompilationUnit): Transformer =
    new DelambdafyTransformer(unit)

  class DelambdafyTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    private val lambdaBodyDefs = new mutable.LinkedHashMap[Symbol, List[Tree]] withDefaultValue Nil
    private val lambdaClassDefs = new mutable.LinkedHashMap[Symbol, List[Tree]] withDefaultValue Nil
    

    override def transform(tree: Tree): Tree = tree match {
      case fun @ Function(_, _) => {
        val (lambdaBodyDef, lambdaClassDef, newExpr) = transformFunction(fun)
        val clazz = lambdaBodyDef.symbol.owner
        val transformedLambdaBodyDef = this.transform(lambdaBodyDef)
        lambdaBodyDefs(clazz) = transformedLambdaBodyDef :: lambdaBodyDefs(clazz)
        val pkg = clazz.owner
        
        // create bridge on the apply method as needed
        val eraser = erasure.newTransformer(unit)
        val erasedLambdaClassDef = enteringPhase(currentRun.erasurePhase){
          eraser.atOwner(lambdaClassDef.symbol)(eraser.transform(lambdaClassDef))
        }
        // erasure can leave behind some artifacts (like nonsense casts and
        // "ErasedValueType") that post erasure cleans up
        val postEraser = postErasure.newTransformer(unit)
        val postErasedLambdaClassDef = enteringPhase(currentRun.posterasurePhase){
          postEraser.atOwner(lambdaClassDef.symbol)(postEraser.transform(erasedLambdaClassDef))
        }
        
        lambdaClassDefs(pkg) = postErasedLambdaClassDef :: lambdaClassDefs(pkg)
        
        val transformedNewExpr = super.transform(newExpr)
        transformedNewExpr
      }
      case _ => super.transform(tree)
    }
   
    /** Transform statements and add lifted definitions to them. */
    override def transformStats(stats: List[Tree], exprOwner: Symbol): List[Tree] = {
      def addLambdaBodies(stat: Tree): Tree = stat match {
        case ClassDef(_, _, _, _) =>
          val lifted = lambdaBodyDefs get stat.symbol match {
            case Some(xs) => xs reverseMap addLambdaBodies
            case _        => Nil
          }
          try deriveClassDef(stat)(impl => deriveTemplate(impl)(_ ::: lifted))
          finally lambdaBodyDefs -= stat.symbol
        case _ =>
          stat
      }
      (super.transformStats(stats, exprOwner) map addLambdaBodies) ++ {
        val classDefs = lambdaClassDefs(exprOwner)
        classDefs
      }
    }

    override def transformUnit(unit: CompilationUnit) {
      afterOwnPhase {
        super.transformUnit(unit)
      }
      assert(lambdaBodyDefs.isEmpty, lambdaBodyDefs.keys mkString ", ")
    }    

    def transformFunction(fun0: Function): (DefDef, ClassDef, Apply) = {
      val targs = fun0.tpe.typeArgs
      val (formals, restpe) = (targs.init, targs.last)
      val clazz = fun0.symbol.enclClass
      
      val freeVarsTraverser = new FreeVarTraverser
      freeVarsTraverser.traverse(fun0)
      val captures = freeVarsTraverser.freeVars
      
      val captureProxies = new LinkedHashMap[Symbol, TermSymbol]
      captureProxies ++= (captures map {capture => 
        val sym = fun0.symbol.owner.newVariable(capture.name.toTermName, capture.pos, 0)
        sym setInfo capture.info
        (capture, sym)
      })

      val decapturify = new DeCapturifyTransformer(captureProxies, unit, clazz, fun0.symbol.owner, fun0.symbol.pos)

      val fun = decapturify.transform(fun0).asInstanceOf[Function]
      val thisProxy = decapturify.thisProxy

      /**
       * Abstracts away the common functionality required to create both
       * the lifted function and the apply method on the anonymous class
       * It creates a method definition with value params cloned from the
       * original lambda. Then it calls a supplied function to create
       * the body and types the result. Finally
       * everything is wrapped up in a MethodDef
       *
       * @param owner The owner for the new method
       * @param name name for the new method
       * @param additionalFlags flags to be put on the method in addition to FINAL
       * @bodyF function that turns the method symbol and list of value params
       *        into a body for the method
       */
      def createMethod(owner: Symbol, name: TermName, additionalParams: List[ValDef], additionalFlags: Long)(bodyF: (Symbol, List[ValDef]) => Tree): DefDef = {
        val methSym = owner.newMethod(name, fun.pos, FINAL | additionalFlags)
        val originalParams = fun.vparams map (_.duplicate)

        val paramSyms = map2(formals, originalParams) {
          (tp, vparam) => methSym.newSyntheticValueParam(tp, vparam.name)
        }
        originalParams zip paramSyms foreach { case (valdef, sym) => valdef.symbol = sym }
        originalParams foreach (_.symbol.owner = methSym)

        additionalParams foreach(_.symbol.owner = methSym)
        val additionalTypes = additionalParams map (_.symbol)
        
        val methodType = MethodType(additionalTypes ++ paramSyms, restpe)
        methSym setInfo methodType
      
        owner.info.decls enter methSym
        
        val body = localTyper.typed(bodyF(methSym, originalParams) setPos fun.pos)
        val vparams = additionalParams ++ originalParams
        val methDef = DefDef(methSym, List(vparams), body)

        // Have to repack the type to avoid mismatches when existentials
        // appear in the result - see SI-4869.
        // TODO probably don't need packedType
        methDef.tpt setType localTyper.packedType(body, methSym)
        methDef

      }

      def createConstructor(clazz: Symbol, members: List[ValDef]): DefDef = {
        val constrSym = clazz.newConstructor(fun.pos, SYNTHETIC)
        
        val (paramTypes, params, assigns) = (members map {member => 
          val paramType = member.symbol.info.typeSymbol
          val paramSymbol = clazz.newVariable(member.symbol.name.toTermName, clazz.pos, 0)
          paramSymbol.setInfo(member.symbol.info)
          val paramVal = ValDef(paramSymbol)
          val paramIdent = Ident(paramSymbol)
          val assign = Assign(Select(gen.mkAttributedQualifier(clazz.thisType), member.symbol), paramIdent)
          
          (paramType, paramVal, assign)
        }).unzip3
        
        val constrType = MethodType(paramTypes, clazz.thisType)
        constrSym setInfo constrType

        clazz.info.decls enter constrSym
        
        val body =
          Block(
            List(
              Apply(Select(Super(gen.mkAttributedThis(clazz), tpnme.EMPTY) setPos clazz.pos, nme.CONSTRUCTOR) setPos clazz.pos, Nil) setPos clazz.pos
            ) ++ assigns,
            Literal(Constant(())): Tree
          ) setPos clazz.pos
        
        localTyper.typed(DefDef(constrSym, List(params), body) setPos clazz.pos).asInstanceOf[DefDef]
      }
      
      val pkg = clazz.owner

      val liftedMethodDef = {
        val additionalParams = (thisProxy.toList ++ captureProxies.values) map ValDef
        // method definition with the return type, and body as the original lambda, with the same arguments plus captured arguments
        val methodName = unit.freshTermName(tpnme.ANON_FUN_NAME.toTermName.decode)
        createMethod(clazz, methodName, additionalParams, STATIC | SYNTHETIC) {
          case (methSym, vparams) =>
            fun.body.substituteSymbols(fun.vparams map (_.symbol), vparams map (_.symbol))
            fun.body changeOwner (fun.symbol -> methSym)
        }
      }

      // anonymous subclass of FunctionN with an apply method
      val anonymousClassDef = {
        val parents = addSerializable(abstractFunctionForFunctionType(fun.tpe))
        // TODO add serialuid
        val name = unit.freshTypeName(clazz.name.decode + tpnme.ANON_FUN_NAME.decode)
        
        val anonClass = pkg newClassSymbol(name, fun.pos, FINAL | SYNTHETIC) addAnnotation serialVersionUIDAnnotation
        anonClass setInfo ClassInfoType(parents, newScope, anonClass)
        
        val members = (thisProxy.toList ++ captures) map {member =>
          val newSymbol = anonClass.newValue(member.name.toTermName, fun.pos, /*PRIVATE | */SYNTHETIC)
          newSymbol.info = member.tpe
          anonClass.info.decls enter newSymbol
          // TODO use mkzero or whatever instead of EmptyTree
          ValDef(newSymbol, localTyper.typed(EmptyTree, member.tpe)) setPos fun.pos
        }
        
        // constructor
        val constr = createConstructor(anonClass, members)
        
        // apply method with same arguments and return type as original lambda.
        val applyMethodDef = createMethod(anonClass, nme.apply, Nil, FINAL | SYNTHETIC) {
          case (methSym, vparams) =>
            val memberIdents = members map {member => Select(gen.mkAttributedThis(anonClass), member.symbol)}
            val args = memberIdents ++ (vparams map { vparam => Ident(vparam.symbol) })
            val select = Select(gen.mkAttributedQualifier(clazz.thisType) setPos fun.pos, liftedMethodDef.symbol) setPos fun.pos setType liftedMethodDef.tpe
            Apply(select.symbol, args: _*) setPos fun.pos
        }
        
        val template = Template(anonClass.info.parents map TypeTree, emptyValDef, members ++ List(constr, applyMethodDef)) setPos fun.pos
        
        // TODO if member fields are private this complains that they're not accessible
        localTyper.typed(ClassDef(anonClass, template) setPos fun.pos).asInstanceOf[ClassDef]
      }
      
      pkg.info.decls enter anonymousClassDef.symbol
      
      val thisArg = thisProxy.toList map (_ => gen.mkAttributedThis(clazz) setPos fun.pos)
      val captureArgs = captures map (capture => Ident(capture) setPos fun.pos)

      val newStat = 
          New(anonymousClassDef.symbol, (thisArg ++ captureArgs): _*) setPos fun.pos

      val typedNewStat = 
          localTyper.typed(newStat, functionType(fun.tpe.typeArgs.init, fun.tpe.typeArgs.last)).asInstanceOf[Apply]

      (liftedMethodDef, anonymousClassDef, typedNewStat)
    }
  } // DelambdafyTransformer
  

  class FreeVarTraverser extends Traverser {
    val freeVars = mutable.LinkedHashSet[Symbol]()
    val declared = mutable.LinkedHashSet[Symbol]()
    
    override def traverse(tree: Tree) = {
      tree match {
        case Function(args, body) => 
          args foreach {arg => declared += arg.symbol}
        case ValDef(_, _, _, _) =>
          declared += tree.symbol
        case _: Bind =>
          declared += tree.symbol
        case Ident(_) =>
          val sym = tree.symbol
          if ((sym != NoSymbol) && sym.isLocal && sym.isTerm && !sym.isMethod && !declared.contains(sym)) freeVars += sym
        case _ =>
      }
      super.traverse(tree)
    }
  }
  
  class DeCapturifyTransformer(captureProxies: Map[Symbol, TermSymbol], unit: CompilationUnit, clazz: Symbol, owner:Symbol, pos: Position) extends TypingTransformer(unit) {
    var thisProxy: Option[Symbol] = None

    override def transform(tree: Tree) = tree match {
      case This(encl) if encl == clazz.name => if (thisProxy == None) {
          val sym = owner.newVariable(nme.FAKE_LOCAL_THIS, pos, 0)
          sym.info = clazz.tpe
          thisProxy = Some(sym)
        }
        localTyper typed Ident(thisProxy.get)
      case Ident(name) if (captureProxies contains tree.symbol) => 
        localTyper typed Ident(captureProxies(tree.symbol))
      case _ => super.transform(tree)
    }
  }

  private lazy val serialVersionUIDAnnotation =
    AnnotationInfo(SerialVersionUIDAttr.tpe, List(Literal(Constant(0))), List())

}
