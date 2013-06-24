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
    
    val thisReferringMethods = {
      val thisReferringMethodsTraverser = new ThisReferringMethodsTraverser()
      thisReferringMethodsTraverser traverse unit.body
      val methodReferringMap = thisReferringMethodsTraverser.liftedMethodReferences
      val referrers = thisReferringMethodsTraverser.thisReferringMethods
      // recursively find methods that refer to 'this' directly or indirectly via references to other methods
      // for each method found add it to the referrers set
      def refersToThis(symbol: Symbol): Boolean = {
        if (referrers contains symbol) true
        else if (methodReferringMap(symbol) exists refersToThis) {
          // add it early to memoize
          debuglog(s"$symbol indirectly refers to 'this'")
          referrers += symbol
          true
        } else false
      }
      methodReferringMap.keys foreach refersToThis
      referrers
    }
    
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
      val functionTpe = originalFunction.tpe 
      val targs = functionTpe.typeArgs
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
            // if the lifted body method doesn't refer to this then it can be static
            if(!(thisReferringMethods contains meth.symbol)) meth.symbol setFlag STATIC
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
      def makeAnonymousClass = {
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
	
	    val thisProxy = {
          val target = targetMethod(originalFunction)
	      if (thisReferringMethods contains target) {
            val sym = anonClass.newVariable(nme.FAKE_LOCAL_THIS, originalFunction.pos, SYNTHETIC) // TODO PRIVATE
            sym.info = oldClass.tpe
            Some(sym)
	      } else None
	    }
        
	    val decapturify = new DeCapturifyTransformer(captureProxies2, unit, oldClass, anonClass, originalFunction.symbol.pos, thisProxy)
	
	    val fun = decapturify.transform(originalFunction).asInstanceOf[Function]
        
        val members = (thisProxy.toList ++ (captureProxies2 map (_._2))) map {member =>
          anonClass.info.decls enter member
          ValDef(member, gen.mkZero(member.tpe)) setPos fun.pos
        }
        
        // constructor
        val constr = createConstructor(anonClass, members)
        
        // apply method with same arguments and return type as original lambda.
        val applyMethodDef = createApplyMethod(anonClass, fun)
        
        val bridgeMethod = createBridgeMethod(anonClass, originalFunction, applyMethodDef)
        
        val template = Template(anonClass.info.parents map TypeTree, emptyValDef, members ++ List(constr, applyMethodDef) ++ bridgeMethod) setPos fun.pos
        
        // TODO if member fields are private this complains that they're not accessible
        (localTyper.typed(ClassDef(anonClass, template) setPos fun.pos).asInstanceOf[ClassDef], thisProxy)
      }
      
      val (anonymousClassDef, thisProxy) = makeAnonymousClass
            
      pkg.info.decls enter anonymousClassDef.symbol
      
      val thisArg = thisProxy.toList map (_ => gen.mkAttributedThis(oldClass) setPos originalFunction.pos)
      val captureArgs = captures map (capture => Ident(capture) setPos originalFunction.pos)

      val newStat = 
          Typed(New(anonymousClassDef.symbol, (thisArg ++ captureArgs): _*) setPos originalFunction.pos, TypeTree(abstractFunctionErasedType))

      val typedNewStat = 
          localTyper.typed(newStat)

      (anonymousClassDef, typedNewStat)
    }
    
    def createBridgeMethod(newClass:Symbol, originalFunction: Function, applyMethod: DefDef): Option[DefDef] = {
        def box(tree: Tree, treeTpe: Type): (Tree, Type) = treeTpe match {
          case ErasedValueType(tref) =>
            val clazz = tref.sym
            val newTree = New(clazz, tree)
            (newTree, clazz.tpe)
          case _ => treeTpe.typeSymbol match {
	        case UnitClass  => (BLOCK(tree, REF(BoxedUnit_UNIT)), BoxedUnitClass.toType)
	        case NothingClass => (tree, ObjectClass.tpe)
	        case x =>
              val newTree = (REF(boxMethod.apply(x)) APPLY tree) setPos (tree.pos)
              val newType = boxedClass(x).toType
              (newTree, newType)
          }
        }
        
        def unbox(tree: Tree, treeType: Type, expectedTpe: Type): Tree = expectedTpe match {
          case ErasedValueType(tref) =>
            val clazz = tref.sym
            log("not boxed: "+tree)
            Apply(Select(adapt(tree, treeType, clazz.tpe)._2, clazz.derivedValueClassUnbox), List())
          case _ =>
            (REF(unboxMethod(expectedTpe.typeSymbol)) APPLY tree) setPos (tree.pos)
        }
        
        def isErasedValueType(tpe: Type) = tpe.isInstanceOf[ErasedValueType]
        def isDifferentErasedValueType(tpe: Type, other: Type) =
          isErasedValueType(tpe) && (tpe ne other)

        def adapt(tree: Tree, treeTpe: Type, expectedType: Type): (Boolean, Tree) = {
          if (treeTpe =:= expectedType) (false, tree)
          else if (isDifferentErasedValueType(treeTpe, expectedType)) {
            val (newTree, newType) = box(tree, treeTpe)
            (true, adapt(newTree, newType, expectedType)_2)
          }
          else if (isDifferentErasedValueType(expectedType, treeTpe)) (true, unbox(tree, treeTpe, expectedType))
          else if (treeTpe <:< expectedType) (true, tree)
          else if (isPrimitiveValueType(treeTpe) && !isPrimitiveValueType(expectedType)) {
            val (boxingTree, boxedType) = box(tree, treeTpe)
            (true, adapt(boxingTree, boxedType, expectedType)._2)
          } else if (isPrimitiveValueType(expectedType) && !isPrimitiveValueType(treeTpe)) (true, unbox(tree, treeTpe, expectedType))          
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
        
        enteringPhase(currentRun.posterasurePhase) {
	      val liftedBodyDefTpe: MethodType = {
	        val liftedBodySymbol = {
	          val Apply(method, _) = originalFunction.body
	          method.symbol
	        }
	        liftedBodySymbol.info.asInstanceOf[MethodType]
	      }
          val (neededParams, adaptedParams) = (bridgeSyms zip liftedBodyDefTpe.params map {case (bridgeSym, param) => adapt(Ident(bridgeSym), bridgeSym.tpe, param.tpe)}).unzip
          val body = Apply(Select(gen.mkAttributedThis(newClass), applyMethod.symbol), adaptedParams)
          val (neededReturn, adaptedBody) = adapt(body, liftedBodyDefTpe.resultType, ObjectClass.tpe)
          if (neededParams.contains(true) || neededReturn) {
            val methDef = DefDef(methSym, List(bridgeParams), adaptedBody)
            newClass.info.decls enter methSym
            Some(methDef)
          } else None map {x => (localTyper typed x).asInstanceOf[DefDef]}
        }
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
  
  class DeCapturifyTransformer(captureProxies: Map[Symbol, TermSymbol], unit: CompilationUnit, oldClass: Symbol, newClass:Symbol, pos: Position, thisProxy: Option[Symbol]) extends TypingTransformer(unit) {

    override def transform(tree: Tree) = tree match {
      case tree@This(encl) if tree.symbol == oldClass && thisProxy.isDefined => 
        localTyper typed Select(gen.mkAttributedThis(newClass), thisProxy.get)
      case Ident(name) if (captureProxies contains tree.symbol) => 
        localTyper typed Select(gen.mkAttributedThis(newClass), captureProxies(tree.symbol))
      case _ => super.transform(tree)
    }
  }
  
  /**
   * Get the symbol of the target lifted lambad body method from a function. I.e. if
   * the function is {args => anonfun(args)} then this method returns anonfun's symbol 
   */
  private def targetMethod(fun: Function): Symbol = fun match {
    case Function(_, Apply(target, _)) => 
      target.symbol
    case _ => 
      // any other shape of Function is unexpected at this point
      sys.error(s"could not understand function with tree $fun")      
  }

  private lazy val serialVersionUIDAnnotation =
    AnnotationInfo(SerialVersionUIDAttr.tpe, List(Literal(Constant(0))), List())
  
  // finds all methods that reference 'this'
  class ThisReferringMethodsTraverser() extends Traverser {
    private var currentMethod: Option[Symbol] = None
    // the set of methods that refer to this
    val thisReferringMethods = mutable.Set[Symbol]()
    // the set of lifted lambda body methods that each method refers to
    val liftedMethodReferences = mutable.Map[Symbol, Set[Symbol]]().withDefault(_ => mutable.Set())
    override def traverse(tree: Tree) = tree match {
      case DefDef(_, _, _, _, _, _) =>
        // we don't expect defs within defs. At this phase trees should be very flat
        assert(currentMethod.isEmpty)
        currentMethod = Some(tree.symbol)
        super.traverse(tree)
        currentMethod = None
      case fun@Function(_, _) => 
        // we don't drill into functions because at the beginning of this phase they will always refer to 'this'. 
        // They'll be of the form {(args...) => this.anonfun(args...)}
        // but we do need to make note of the lifted body method in case it refers to 'this'
        currentMethod foreach {m => liftedMethodReferences(m) += targetMethod(fun)}
      case This(_) =>
        currentMethod foreach {method =>
          if (tree.symbol == method.enclClass) {
            debuglog(s"$method directly refers to 'this'")
            thisReferringMethods add method
          }
        }
      case _ =>
        super.traverse(tree)
    }
  }

}
