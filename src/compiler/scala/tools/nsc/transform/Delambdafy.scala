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
    private val lambdaClassDefs = new mutable.LinkedHashMap[Symbol, List[Tree]] withDefaultValue Nil
    
    override def transform(tree: Tree): Tree = tree match {
      case fun @ Function(_, _) => {
        val (lambdaClassDef, newExpr) = transformFunction(fun)
        val pkg = lambdaClassDef.symbol.owner
               
        lambdaClassDefs(pkg) = lambdaClassDef :: lambdaClassDefs(pkg)
        
        val transformedNewExpr = super.transform(newExpr)
        transformedNewExpr
      }
      case _ => super.transform(tree)
    }
   
    /** Transform statements and add lifted definitions to them. */
    override def transformStats(stats: List[Tree], exprOwner: Symbol): List[Tree] = {
      super.transformStats(stats, exprOwner) ++ lambdaClassDefs(exprOwner)
    }

    override def transformUnit(unit: CompilationUnit) {
      afterOwnPhase {
        super.transformUnit(unit)
      }
    }    

    def transformFunction(originalFunction: Function): (ClassDef, Tree) = {
      val targs = originalFunction.tpe.typeArgs
      val (formals, restpe) = (targs.init, targs.last)
      val oldClass = originalFunction.symbol.enclClass
      
      val freeVarsTraverser = new FreeVarTraverser
      freeVarsTraverser.traverse(originalFunction)
      val captures = freeVarsTraverser.freeVars

      /**
       * Creates the apply method for the anonymous subclass of FunctionN
       */
      def createApplyMethod(newClass: Symbol, fun: Function): DefDef = {
        val methSym = newClass.newMethod(nme.apply, fun.pos, FINAL | SYNTHETIC)
        val originalParams = fun.vparams map (_.duplicate)

        val paramSyms = map2(formals, originalParams) {
          (tp, vparam) => methSym.newSyntheticValueParam(tp, vparam.name)
        }
        originalParams zip paramSyms foreach { case (valdef, sym) => valdef.symbol = sym }
        originalParams foreach (_.symbol.owner = methSym)
        
        val methodType = MethodType(paramSyms, restpe)
        methSym setInfo methodType
      
        newClass.info.decls enter methSym

        // the apply method needs to call the lifted method so that lifted method cannot be private
        fun.body match {
          case Apply(meth, _) => 
            meth.symbol resetFlag PRIVATE
            meth.symbol setFlag PROTECTED
          case huh => 
            error(s"expected a function body consisting only of a method application but got $huh")
        }
        
        val vparams = originalParams
        val body = localTyper.typed {
            fun.body.substituteSymbols(fun.vparams map (_.symbol), vparams map (_.symbol))
            fun.body changeOwner (fun.symbol -> methSym)
        } setPos fun.pos
        val methDef = DefDef(methSym, List(vparams), body)

        // Have to repack the type to avoid mismatches when existentials
        // appear in the result - see SI-4869.
        // TODO probably don't need packedType
        methDef.tpt setType localTyper.packedType(body, methSym)
        methDef
      }
      
      def createBridgeMethod(newClass:Symbol, applyMethod: DefDef): Option[DefDef] = {
        def box(tree: Tree, treeTpe: Type): (Tree, Type) = treeTpe.typeSymbol match {
	      case UnitClass  => (BLOCK(tree, REF(BoxedUnit_UNIT)), BoxedUnitClass.toType)
	      case NothingClass => (tree, ObjectClass.tpe)
	      case x =>
            val newTree = (REF(boxMethod.apply(x)) APPLY tree) setPos (tree.pos)
            val newType = boxedClass(x).toType
            (newTree, newType)
        }
        
        def unbox(tree: Tree, expectedTpe: Type): Tree = (REF(unboxMethod(expectedTpe.typeSymbol)) APPLY tree) setPos (tree.pos)
        
        def adapt(tree: Tree, treeTpe: Type, expectedType: Type): (Boolean, Tree) = {
          if (treeTpe =:= expectedType) (false, tree)
          else if (treeTpe <:< expectedType) (true, tree)
          else if (isPrimitiveValueType(treeTpe) && !isPrimitiveValueType(expectedType)) {
            val (boxingTree, boxedType) = box(tree, treeTpe)
            (true, adapt(boxingTree, boxedType, expectedType)._2)
          } else if (isPrimitiveValueType(expectedType) && !isPrimitiveValueType(treeTpe)) (true, unbox(tree, expectedType))          
          else (true, gen.mkAttributedCast(tree, expectedType))
        }
        val methSym = newClass.newMethod(nme.apply, applyMethod.pos, FINAL | SYNTHETIC | BRIDGE)
        val originalParams = applyMethod.vparamss(0)
        val bridgeParams = originalParams map { originalParam =>
          val bridgeSym = methSym.newSyntheticValueParam(ObjectClass.tpe, originalParam.name)
          bridgeSym.owner = methSym
          ValDef(bridgeSym)
        }
        
        val bridgeSyms = bridgeParams map (_.symbol)

        val methodType = MethodType(bridgeSyms, ObjectClass.tpe)
        methSym setInfo methodType
        
        val (neededParams, adaptedParams) = (bridgeSyms zip originalParams map {case (bridgeSym, originalParam) => adapt(Ident(bridgeSym), bridgeSym.tpe, originalParam.symbol.tpe)}).unzip
        val body = Apply(Select(gen.mkAttributedThis(newClass), applyMethod.symbol), adaptedParams)
        val (neededReturn, adaptedBody) = adapt(body, restpe, ObjectClass.tpe)
        if (neededParams.contains(true) || neededReturn) {
          val methDef = (localTyper typed DefDef(methSym, List(bridgeParams), adaptedBody)).asInstanceOf[DefDef]
          newClass.info.decls enter methSym
          Some(methDef)
        } else None
      }

      def createConstructor(newClass: Symbol, members: List[ValDef]): DefDef = {
        val constrSym = newClass.newConstructor(originalFunction.pos, SYNTHETIC)
        
        val (paramSymbols, params, assigns) = (members map {member =>
          val paramSymbol = newClass.newVariable(member.symbol.name.toTermName, newClass.pos, 0)
          paramSymbol.setInfo(member.symbol.info)
          val paramVal = ValDef(paramSymbol)
          val paramIdent = Ident(paramSymbol)
          val assign = Assign(Select(gen.mkAttributedThis(newClass), member.symbol), paramIdent)
          
          (paramSymbol, paramVal, assign)
        }).unzip3
        
        val constrType = MethodType(paramSymbols, newClass.thisType)
        constrSym setInfo constrType

        newClass.info.decls enter constrSym
        
        val body =
          Block(
            List(
              Apply(Select(Super(gen.mkAttributedThis(newClass), tpnme.EMPTY) setPos newClass.pos, nme.CONSTRUCTOR) setPos newClass.pos, Nil) setPos newClass.pos
            ) ++ assigns,
            Literal(Constant(())): Tree
          ) setPos newClass.pos
        
        (localTyper typed DefDef(constrSym, List(params), body) setPos newClass.pos).asInstanceOf[DefDef]
      }
      
      val pkg = oldClass.owner
      
      /** Parent for anonymous class def */
      val abstractFunctionErasedType = {
        val originalFunctionTpe = originalFunction.tpe 
        val functionArity = originalFunctionTpe.typeArgs.init.length
        val abstractFunctionClass = AbstractFunctionClass(functionArity)
        val tpe = abstractFunctionClass.tpe
        // alternatively
        //assert(abstractFunctionClass.owner.isPackageClass)
        //val tpe2 = typeRef(abstractFunctionClass.owner.tpe, abstractFunctionClass, Nil)
        tpe
        //abstractFunctionForFunctionType(originalFunction.tpe)
      }

      // anonymous subclass of FunctionN with an apply method
      val (anonymousClassDef, thisProxy) = {
        val parents = addSerializable(abstractFunctionErasedType)
        // TODO add serialuid
        val name = unit.freshTypeName(oldClass.name.decode + tpnme.ANON_FUN_NAME.decode)
        
        val anonClass = pkg newClassSymbol(name, originalFunction.pos, FINAL | SYNTHETIC) addAnnotation serialVersionUIDAnnotation
        anonClass setInfo ClassInfoType(parents, newScope, anonClass)
        
	    val captureProxies2 = new LinkedHashMap[Symbol, TermSymbol]
	    captureProxies2 ++= (captures map {capture => 
	      val sym = anonClass.newVariable(capture.name.toTermName, capture.pos, SYNTHETIC) // TODO PRIVATE
	      sym setInfo capture.info
	      (capture, sym)
	    })
	
	    val decapturify = new DeCapturifyTransformer(captureProxies2, unit, oldClass, anonClass, originalFunction.symbol.pos)
	
	    val fun = decapturify.transform(originalFunction).asInstanceOf[Function]
	    val thisProxy = decapturify.thisProxy
        
        val members = (thisProxy.toList ++ (captureProxies2 map (_._2))) map {member =>
          anonClass.info.decls enter member
          ValDef(member, gen.mkZero(member.tpe)) setPos fun.pos
        }
        
        // constructor
        val constr = createConstructor(anonClass, members)
        
        // apply method with same arguments and return type as original lambda.
        val applyMethodDef = createApplyMethod(anonClass, fun)
        
        val bridgeMethod = createBridgeMethod(anonClass, applyMethodDef)
        
        val template = Template(anonClass.info.parents map TypeTree, emptyValDef, members ++ List(constr, applyMethodDef) ++ bridgeMethod) setPos fun.pos
        
        // TODO if member fields are private this complains that they're not accessible
        (localTyper.typed(ClassDef(anonClass, template) setPos fun.pos).asInstanceOf[ClassDef], thisProxy)
      }
      
      pkg.info.decls enter anonymousClassDef.symbol
      
      val thisArg = thisProxy.toList map (_ => gen.mkAttributedThis(oldClass) setPos originalFunction.pos)
      val captureArgs = captures map (capture => Ident(capture) setPos originalFunction.pos)

      val newStat = 
          Typed(New(anonymousClassDef.symbol, (thisArg ++ captureArgs): _*) setPos originalFunction.pos, TypeTree(abstractFunctionErasedType))

      val typedNewStat = 
          localTyper.typed(newStat)

      (anonymousClassDef, typedNewStat)
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
  
  class DeCapturifyTransformer(captureProxies: Map[Symbol, TermSymbol], unit: CompilationUnit, oldClass: Symbol, newClass:Symbol, pos: Position) extends TypingTransformer(unit) {
    var thisProxy: Option[Symbol] = None

    override def transform(tree: Tree) = tree match {
      case tree@This(encl) if tree.symbol == oldClass  => if (thisProxy == None) {
          val sym = newClass.newVariable(nme.FAKE_LOCAL_THIS, pos, SYNTHETIC) // TODO PRIVATE
          sym.info = oldClass.tpe
          thisProxy = Some(sym)
        }
        localTyper typed Select(gen.mkAttributedThis(newClass), thisProxy.get)
      case Ident(name) if (captureProxies contains tree.symbol) => 
        localTyper typed Select(gen.mkAttributedThis(newClass), captureProxies(tree.symbol))
      case _ => super.transform(tree)
    }
  }

  private lazy val serialVersionUIDAnnotation =
    AnnotationInfo(SerialVersionUIDAttr.tpe, List(Literal(Constant(0))), List())

}
