package autoproxy.plugin

import scala.tools._
import nsc.Global
import nsc.Phase
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent
import nsc.transform.Transform
import nsc.transform.InfoTransform
import nsc.transform.TypingTransformers
import nsc.symtab.Flags._
import nsc.util.Position
import nsc.ast.TreeDSL
import nsc.typechecker
import scala.annotation.tailrec


class GenerateSynthetics(plugin: AutoProxyPlugin, val global: Global) extends PluginComponent
      with Transform
      with TypingTransformers
      with TreeDSL
{
  import global._
  import definitions._

  val runsAfter = List[String]("earlytyper")
  val phaseName = "generatesynthetics"

  override def newTransformer(unit: CompilationUnit) = new AutoProxyTransformer(unit)

  class AutoProxyTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    import CODE._

    /**
     *
     * @param owner, where the delegates get added
     * @param tgtMember, the member that has @proxy attached
     * @param tgtMethod, the method in tgtMember that needs to be forwarded
     * @param pos, where the tgtMember is located in code
     *
     */
    private def mkDelegate(owner: Symbol, tgtMember: Symbol, tgtMethod: Symbol, pos: Position) = {
      println("### MAKING DELEGATE: ")
      val delegate = cloneMethod(tgtMethod, owner)

      log("owner=" + This(owner))

      val selectTarget = This(owner) DOT tgtMember DOT tgtMethod
      log("SelectTarget=")
      log(nodeToString(selectTarget))

      val rhs: Tree =
      delegate.info match {
        case MethodType(params, _) => Apply(selectTarget, params.map(Ident(_)))
        case _ => selectTarget
      }

      val delegateDef = localTyper.typed {DEF(delegate) === rhs}

      log(nodePrinters nodeToString delegateDef)

      delegateDef
    }

    private def publicMembersOf(sym: Symbol) =
      sym.tpe.members.filter(_.isPublic).filter(!_.isConstructor)

    //    private def deferredMembersOf(sym: Symbol) =
    //      sym.tpe.members.filter(_.isPublic).filter(!_.isConstructor)

    //Not used
    private def publicMethodsOf(sym: Symbol) =
      publicMembersOf(sym).filter(_.isMethod)


    private def cloneMethod(prototype: Symbol, owner: Symbol) = {
      val newSym = prototype.cloneSymbol(owner)
      newSym setPos owner.pos.focus
      newSym setFlag SYNTHETICMETH
      //Clear the deferred flag otherwise we will get
      // error about the member not being implemented
      newSym resetFlag DEFERRED
      owner.info.decls enter newSym
    }


    /**
     * Will generate a list of methods
     *
     *
     */
    //TODO ? Filter out equals / hashCode / toString?
    def generateDelegates(templ: Template, symbolToProxy: Symbol): List[Tree] = {
      val cls = symbolToProxy.owner //the class owning the symbol
      println("### GENERATING DELEGATES: " + cls + " -> " + symbolToProxy)

      log("proxying symbol: " + symbolToProxy)
      log("owning class: " + cls)


      //      val publicMethods = publicMembersOf(cls)
      //      val deferredMethods = cls.tpe.deferredMembers
      //      val definedMethods = publicMethods.filter(m => !deferredMethods.contains(m))

      //      val definedMethods = cls.tpe.decls.filter(_.isPublic).filter(!_.isConstructor)
      //      def declaresMethod(name : Name) : Boolean = cls.tpe.
      val definedMethods = publicMembersOf(cls).filter(!_.isDeferred)
//      println("### Defined: " + definedMethods)


      //should be called requiredMembers
      //disregard those members that are defined in the that has
      //the proxy-member
      //TODO sophisticate this by allowing mixins to define their appropriate spot in the linearization order
      //TODO this requires finding where type of symbolToProxy is located in the linearization order of the owner class
      //TODO Option#2 simply have a 2nd mixin shadow a first
      //TODO Option#3 punt, not terrible, user just has to resolve the conflict in the class themselves
      // we know that Bar should not override members defined in baz as well
      // not just members in Foo
      // class Foo(@mixin bar : Bar) extends Bar with Baz
      val requiredMethods = publicMembersOf(symbolToProxy).filter(mem => !definedMethods.exists(_.name==mem.name))

      log("defined methods: " + definedMethods.mkString(", "))
      log("missing methods: " + requiredMethods.mkString(", "))

      //finally we have our list of methods that need to be delagated we will now turn that list into synthetics
      val synthetics = for (method <- requiredMethods) yield
        mkDelegate(cls, symbolToProxy, method, symbolToProxy.pos.focus)

      synthetics
    }

    override def transform(tree: Tree): Tree = {

      /**
       * Check to see if this a class member that is an accessor
       *
       */
      def isAccessor(tree: Tree) = tree match {
        case m: MemberDef if m.mods.isAccessor => true
        case _ => false
      }

      def shouldAutoProxySym(sym: Symbol) = {
        if (sym != null) {
          val testSym = if (sym.isModule) sym.moduleClass else sym
          testSym.annotations exists {_.toString == plugin.AutoproxyAnnotationClass}
        } else false
      }

      def shouldAutoProxy(tree: Tree) = {
        //??For debug?
        val nodeStr = nodePrinters.nodeToString(tree)
        //Only autoproxy when we are not looking at
        //an accessor ??
        !isAccessor(tree) && shouldAutoProxySym(tree.symbol)
      }

      val newTree = tree match {
      //We may need to modify the tree if it is a class def
        case ClassDef(mods, name, tparams, impl) =>
          val delegs = for (member <- impl.body if shouldAutoProxy(member)) yield {
            log("found annotated member: " + member)
            generateDelegates(impl, member.symbol)
          }
          //TODO PERHAPS insert the delegates at each autoProxySyms respective position in the class
          //or does position already accomplish that?
          val newImpl = treeCopy.Template(impl, impl.parents, impl.self, delegs.flatten ::: impl.body)
          treeCopy.ClassDef(tree, mods, name, tparams, newImpl)
        case _ => tree
      }
      super.transform(newTree)
    }
  }
}