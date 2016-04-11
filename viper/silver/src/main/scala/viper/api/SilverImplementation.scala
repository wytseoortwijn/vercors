package viper.api

import viper.silver.ast._
import scala.collection.JavaConverters._
import scala.collection.JavaConverters._
import viper.silver.verifier.{Failure, Success, AbortedExceptionally, VerificationError}
import java.util.List
import java.util.Properties
import scala.math.BigInt.int2bigInt
import viper.silver.ast.SeqAppend
import java.nio.file.Path
import viper.silver.parser.PLocalVarDecl

class Prog {
  val domains = new java.util.ArrayList[Domain]()
  val fields = new java.util.ArrayList[Field]()
  val functions = new java.util.ArrayList[Function]()
  val predicates = new java.util.ArrayList[Predicate]()
  val methods = new java.util.ArrayList[Method]()
}

class SilverImplementation[O,Err] extends viper.api.SilverVerifier[O,Err,Type,Exp,Stmt,LocalVarDecl,DomainFunc,DomainAxiom,Prog] {

  /** Type constructors */
  
  def Int() : Type = viper.silver.ast.Int
  def Bool(): Type = viper.silver.ast.Bool
  def Perm(): Type = viper.silver.ast.Perm
  def Ref() : Type = viper.silver.ast.Ref
  def List(t: Type): Type = SeqType(t)
  def Bag(t: Type): Type = MultisetType(t)
  def Set(t: Type): Type = SetType(t)
  def domain_type(name:String):Type = {
    val vars = Seq()
    val pars:Map[viper.silver.ast.TypeVar,viper.silver.ast.Type] = Map()
    DomainType(name,pars)(vars)
  }
  
  /** Expressions */
  
  def Constant(o:O, i:Int): Exp = IntLit(i)(NoPosition,new OriginInfo(o))
  def Constant(o:O, b:Boolean): Exp =
    if(b) TrueLit()(NoPosition,new OriginInfo(o)) else FalseLit()(NoPosition,new OriginInfo(o))
 
  def write_perm(o:O):Exp =  FullPerm()(NoPosition,new OriginInfo(o))
  def read_perm(o:O):Exp =  WildcardPerm()(NoPosition,new OriginInfo(o))
  def no_perm(o:O):Exp =  NoPerm()(NoPosition,new OriginInfo(o))
  
  def field_access(o:O,e1:Exp,e2:Exp):Exp=FieldAccessPredicate(e1.asInstanceOf[FieldAccess],e2)(NoPosition,new OriginInfo(o))
  def scale_access(o:O,e1:Exp,e2:Exp):Exp=PredicateAccessPredicate(e1.asInstanceOf[PredicateAccess],e2)(NoPosition,new OriginInfo(o))
  
  def unfolding_in(o:O,e1:Exp,e2:Exp):Exp=Unfolding(e1.asInstanceOf[PredicateAccessPredicate],e2)(NoPosition,new OriginInfo(o))

  def explicit_set(o:O,elems:List[Exp]): Exp = ExplicitSet(elems.asScala)(NoPosition,new OriginInfo(o))
  def explicit_bag(o:O,elems:List[Exp]): Exp = ExplicitMultiset(elems.asScala)(NoPosition,new OriginInfo(o))
  def explicit_seq(o:O,elems:List[Exp]): Exp = ExplicitSeq(elems.asScala)(NoPosition,new OriginInfo(o))
  def empty_set(o:O,t:Type): Exp = EmptySet(t)(NoPosition,new OriginInfo(o))
  def empty_bag(o:O,t:Type): Exp = EmptyMultiset(t)(NoPosition,new OriginInfo(o))
  def empty_seq(o:O,t:Type): Exp = EmptySeq(t)(NoPosition,new OriginInfo(o))
  def range(o:O,e1:Exp,e2:Exp) :Exp = RangeSeq(e1,e2)(NoPosition,new OriginInfo(o))
  def index(o:O,e1:Exp,e2:Exp) :Exp = SeqIndex(e1,e2)(NoPosition,new OriginInfo(o))
  def take(o:O,e1:Exp,e2:Exp) :Exp = SeqTake(e1,e2)(NoPosition,new OriginInfo(o))
  def drop(o:O,e1:Exp,e2:Exp) :Exp = SeqDrop(e1,e2)(NoPosition,new OriginInfo(o))
  def size(o:O,e1:Exp) :Exp = {
      e1.typ match {
        case SeqType(_) => SeqLength(e1)(NoPosition,new OriginInfo(o))
        case MultisetType(_) => AnySetCardinality(e1)(NoPosition,new OriginInfo(o))
        case SetType(_) => AnySetCardinality(e1)(NoPosition,new OriginInfo(o))
        case _ => throw new Error("cannot convert size for type "+e1.typ);
      }
    }
  def append(o:O,e1:Exp,e2:Exp) :Exp = SeqAppend(e1,e2)(NoPosition,new OriginInfo(o))
  def union(o:O,e1:Exp,e2:Exp) :Exp = AnySetUnion(e1,e2)(NoPosition,new OriginInfo(o))

  def seq_contains(o:O,e1:Exp,e2:Exp):Exp = SeqContains(e1,e2)(NoPosition,new OriginInfo(o))
  def any_set_contains(o:O,e1:Exp,e2:Exp):Exp = AnySetContains(e1,e2)(NoPosition,new OriginInfo(o))
  
  def domain_call(o: O,name:String,args:List[Exp], dpars: java.util.Map[String,Type],rt:Type,pars:List[LocalVarDecl],domain:String) : Exp = {
      val tm : Map[viper.silver.ast.TypeVar,viper.silver.ast.Type] = dpars.entrySet().asScala.map {
        case e:java.util.Map.Entry[String,Type] => (TypeVar(e.getKey()),e.getValue())
      }.toMap
      DomainFuncApp(name,args.asScala.toSeq,tm)(NoPosition,new OriginInfo(o),rt,pars.asScala,domain)
  }

  def if_then_else(o:O,c:Exp,s1:Stmt,s2:Stmt):Stmt =If(c,s1,s2) (NoPosition,new OriginInfo(o))
  
  def write_program(pw:java.io.PrintWriter,prog:Prog):Unit={
    val program = Program(prog.domains.asScala.toList,
              prog.fields.asScala.toList,
              prog.functions.asScala.toList,
              prog.predicates.asScala.toList,
              prog.methods.asScala.toList)()
    pw.write(program.toString())
  }
  
  def function_call(o: O,name:String,args:List[Exp],rt:Type,pars:List[LocalVarDecl]) : Exp = {
    FuncApp(name,args.asScala.toSeq)(NoPosition,new OriginInfo(o),rt,pars.asScala)
  }
  def result(o: O,t:Type) : Exp = Result()(t,null,new OriginInfo(o)) 
  
  def predicate_call(o: O,name:String,args:List[Exp]) : Exp = {
    val e1=PredicateAccess(args.asScala.toSeq,name)(NoPosition,new OriginInfo(o))
    //val e2=FullPerm()(NoPosition,new OriginInfo(o))
    //PredicateAccessPredicate(e1,e2)(NoPosition,new OriginInfo(o))
    e1
  }
  
  def method_call(o:O,name:String,in_args:List[Exp],out_args:List[Exp],pars:List[LocalVarDecl],rets:List[LocalVarDecl]) : Stmt = {
    val m = Method(name, pars.asScala, rets.asScala, Nil, Nil, Nil , null )(NoPosition,new OriginInfo(o))
    val outs = out_args.asScala.map {
      x => x.asInstanceOf[LocalVar]
    }
    MethodCall(m,in_args.asScala,outs)(NoPosition,new OriginInfo(o))
  } 
  
  def FieldAccess(o:O, obj:Exp, field:String, t:Type):Exp = {
    val info=new OriginInfo(o)
    val f=Field(field,t)(null,info)
    viper.silver.ast.FieldAccess(obj,f)(null,info)
  }

  def neq(o:O,e1:Exp,e2:Exp) :Exp = NeCmp(e1,e2)(NoPosition,new OriginInfo(o))
  def eq(o:O,e1:Exp,e2:Exp) :Exp = EqCmp(e1,e2)(NoPosition,new OriginInfo(o))
  
  def gt(o:O,e1:Exp,e2:Exp) :Exp = GtCmp(e1,e2)(NoPosition,new OriginInfo(o))
  def lt(o:O,e1:Exp,e2:Exp) :Exp = LtCmp(e1,e2)(NoPosition,new OriginInfo(o))
  def gte(o:O,e1:Exp,e2:Exp) :Exp = GeCmp(e1,e2)(NoPosition,new OriginInfo(o))
  //def lte(o:O,e1:Exp,e2:Exp) :Exp = LeCmp(e1,e2)(NoPosition,new OriginInfo(o))
  def lte(o:O,e1:Exp,e2:Exp) :Exp = {
    e1 match {
      case LocalVar(n) => if (e1.asInstanceOf[LocalVar].typ==Perm)
          PermLeCmp(e1,e2)(NoPosition,new OriginInfo(o))
        else
          LeCmp(e1,e2)(NoPosition,new OriginInfo(o))
      case e:PermLeCmp => PermDiv(e1,e2)(NoPosition,new OriginInfo(o))
      case _  => LeCmp(e1,e2)(NoPosition,new OriginInfo(o))
    }
  }
    
  def and(o:O,e1:Exp,e2:Exp) :Exp = And(e1,e2)(NoPosition,new OriginInfo(o))
  def or(o:O,e1:Exp,e2:Exp) :Exp = Or(e1,e2)(NoPosition,new OriginInfo(o))
  def implies(o:O,e1:Exp,e2:Exp) :Exp = Implies(e1,e2)(NoPosition,new OriginInfo(o))
  def not(o:O,e1:Exp):Exp = Not(e1)(NoPosition,new OriginInfo(o))
  
  def cond(o:O,e1:Exp,e2:Exp,e3:Exp) :Exp = CondExp(e1,e2,e3)(NoPosition,new OriginInfo(o))

  def mult(o:O,e1:Exp,e2:Exp) :Exp = Mul(e1,e2)(NoPosition,new OriginInfo(o))
  //def div(o:O,e1:Exp,e2:Exp) :Exp = Div(e1,e2)(NoPosition,new OriginInfo(o))
  def div(o:O,e1:Exp,e2:Exp) :Exp = {
    e1 match {
      case LocalVar(n) => if (e1.asInstanceOf[LocalVar].typ==Perm)
          PermDiv(e1,e2)(NoPosition,new OriginInfo(o))
        else
          Div(e1,e2)(NoPosition,new OriginInfo(o))
      case e:PermExp => PermDiv(e1,e2)(NoPosition,new OriginInfo(o))
      case _  => Div(e1,e2)(NoPosition,new OriginInfo(o))
    }
  }
  def frac(o:O,e1:Exp,e2:Exp) :Exp = {
    e1 match {
      case LocalVar(n) => if (e1.asInstanceOf[LocalVar].typ==Perm)
          PermDiv(e1,e2)(NoPosition,new OriginInfo(o))
        else
          FractionalPerm(e1,e2)(NoPosition,new OriginInfo(o))
      case e:PermExp => PermDiv(e1,e2)(NoPosition,new OriginInfo(o))
      case _  => FractionalPerm(e1,e2)(NoPosition,new OriginInfo(o))
    }
  }
  def mod(o:O,e1:Exp,e2:Exp) :Exp = Mod(e1,e2)(NoPosition,new OriginInfo(o))
  def add(o:O,e1:Exp,e2:Exp) :Exp = {
    e1 match {
      case LocalVar(n) => if (e1.asInstanceOf[LocalVar].typ==Perm)
          PermAdd(e1,e2)(NoPosition,new OriginInfo(o))
        else
          Add(e1,e2)(NoPosition,new OriginInfo(o))
      case e:PermExp => PermAdd(e1,e2)(NoPosition,new OriginInfo(o))
      case _  => Add(e1,e2)(NoPosition,new OriginInfo(o))
    }
  }
  def sub(o:O,e1:Exp,e2:Exp) :Exp = Sub(e1,e2)(NoPosition,new OriginInfo(o))
  def neg(o:O,e1:Exp):Exp = Minus(e1)(NoPosition,new OriginInfo(o))
  def minus(o:O,e1:Exp):Exp = Minus(e1)(NoPosition,new OriginInfo(o))
  
  
  def local_name(o:O,name:String,t:Type):Exp = LocalVar(name)(t,null,new OriginInfo(o))
  def null_(o:O):Exp = NullLit()(NoPosition,new OriginInfo(o))
  
  def getOrigin(e : Object) : O = e.asInstanceOf[Infoed].info.asInstanceOf[O]
  
  
  def forall(o:O,vars:List[LocalVarDecl],triggers:List[List[Exp]],e:Exp):Exp = {
    val tmp=triggers.asScala map {
      l => Trigger(l.asScala)(NoPosition,new OriginInfo(o))
    }
    Forall(vars.asScala,tmp,e)(NoPosition,new OriginInfo(o))
  }
  
  def exists(o:O,vars:List[LocalVarDecl],e:Exp):Exp = {
    Exists(vars.asScala,e)(NoPosition,new OriginInfo(o))
  }
  def old(o:O,e:Exp):Exp = Old(e)(NoPosition,new OriginInfo(o))
  
  /* Statements */
  
  def new_object(o:O, v:Exp,names:List[String],types:List[Type]):Stmt={
    val vs = (names.asScala zip types.asScala).map { a => a match { case (n,t) => Field(n,t)(NoPosition,new OriginInfo(o)) } }
    NewStmt(v.asInstanceOf[LocalVar],vs)(NoPosition,new OriginInfo(o))
  }
  def inhale(o:O, e:Exp) : Stmt = Inhale(e)(NoPosition,new OriginInfo(o))
  def exhale(o:O, e:Exp) : Stmt = Exhale(e)(NoPosition,new OriginInfo(o))
  def assert_(o:O, e:Exp) : Stmt = Assert(e)(NoPosition,new OriginInfo(o))
  def refute(o:O, e:Exp) : Stmt = {
    Assert(Not(e)(NoPosition,new RefuteInfo(o)))(NoPosition,new OriginInfo(o))
  }
  
  def fold(o:O, e:Exp) : Stmt = Fold(e.asInstanceOf[PredicateAccessPredicate])(NoPosition,new OriginInfo(o))
  def unfold(o:O, e:Exp) : Stmt = Unfold(e.asInstanceOf[PredicateAccessPredicate])(NoPosition,new OriginInfo(o))
  def goto_(o:O, l:String) : Stmt = Goto(l)(NoPosition,new OriginInfo(o))
  def label(o:O, l:String) : Stmt = Label(l)(NoPosition,new OriginInfo(o))
  def assignment(o:O,loc:Exp,v:Exp) : Stmt = {
    loc match {
        case l : FieldAccess =>
          new FieldAssign(l,v)(NoPosition,new OriginInfo(o))
        case l : LocalVar =>
          new LocalVarAssign(l,v)(NoPosition,new OriginInfo(o))
        case l => 
          throw new Error("failed to map ASTNode of type "+l.getClass());
      }
  }
  def program() : Prog = new Prog 
  
  def while_loop(o:O,cond:Exp,inv:List[Exp],locals:List[LocalVarDecl],body:Stmt):Stmt = {
    val locs=locals.asScala
    //println("locals: "+locs)
    val res=While(cond,inv.asScala,locs,body)(NoPosition,new OriginInfo(o))
    //println(res);
    //res match {
    //  case While(c,i,l,b) => println("stored locals: "+l)
    //}
    res
  }
  
  def block(o: O,stats: List[Stmt]): Stmt = Seqn(stats.asScala)(NoPosition,new OriginInfo(o))
  
  def decl(o:O,name:String,t:Type):LocalVarDecl = LocalVarDecl(name, t)(NoPosition,new OriginInfo(o))
  
  def add_method(p:Prog,o:O,name:String,
      pres:List[Exp],
      posts:List[Exp],
      in:List[LocalVarDecl],
      out:List[LocalVarDecl],
      local:List[LocalVarDecl],
      body:Stmt) {
    p.methods.add(Method(name, in.asScala, out.asScala,
        pres.asScala, posts.asScala, local.asScala , body )(NoPosition,new OriginInfo(o)))
  }
  
  def add_field(p:Prog,o:O,name:String,t:Type)={
    p.fields.add(Field(name,t)(NoPosition,new OriginInfo(o)))
  }
  
  def add_predicate(p:Prog,o:O,name:String,args:List[LocalVarDecl],body:Exp)={
    val b=if(body==null) None else Some(body)
    p.predicates.add(Predicate(name,args.asScala,b)(NoPosition,new OriginInfo(o)))
  }
  
  def add_function(p:Prog,o:O,name:String,args:List[LocalVarDecl],t:Type,pres:List[Exp],posts:List[Exp],body:Exp)={
    val b=if(body==null) None else Some(body)
    p.functions.add(Function(name,args.asScala,t,pres.asScala,posts.asScala,b)(NoPosition,new OriginInfo(o)))
  }
  
  def dfunc(o:O,name:String,args:List[LocalVarDecl],t:Type,domain:String)={
    DomainFunc(name,args.asScala,t,false)(NoPosition,new OriginInfo(o),domain)
  }
  
  def daxiom(o:O,name:String,expr:Exp,domain:String)={
    DomainAxiom(name,expr)(NoPosition,new OriginInfo(o),domain)
  }
  
  def add_adt(p:Prog,o:O,name:String,funcs:List[DomainFunc],axioms:List[DomainAxiom],pars:List[String])={
    val args=pars.asScala map {
      d => viper.silver.ast.TypeVar(d)
    }
    p.domains.add(Domain(name,funcs.asScala,axioms.asScala,args)(NoPosition,new OriginInfo(o)));
  }
  
  private def show(text: String, obj: Any) {
    println(s"$text (${obj.getClass.getSimpleName}): $obj")
  }
 
  def verify(tool_home:Path,settings:Properties,prog:Prog,reachable:java.util.Set[O]) : List[viper.api.ViperError[O]] = {
    val program = Program(prog.domains.asScala.toList,
              prog.fields.asScala.toList,
              prog.functions.asScala.toList,
              prog.predicates.asScala.toList,
              prog.methods.asScala.toList)()
              
    //println("=============\n" + program + "\n=============\n")

    val report = new java.util.ArrayList[viper.api.ViperError[O]]()
    Reachable.reachable.clear()
    val verifier=createVerifier(tool_home,settings)
    //println("verifier: "+ verifier);
    println("running verify");
    val res = verifier.verify(program)
    println("finished verify");
    //println("verifier output: "+ res);
    res match {
      case Success =>
        println("Success!")
      case Failure(errors) =>
        println("Errors! ("+errors.length+")")
        errors foreach { e =>
          if (detail) show("error", e)
          e match {
            case ve: VerificationError =>
              if (detail) {
                show("offending node", ve.offendingNode)
                show("reason", ve.reason.id);
              }
              val err=ve.fullId
              val error = ve.offendingNode match {
                //ve match {
                 case in: viper.silver.ast.Infoed =>
                  //show("offending node's info", in.info)
                  in.info match {
                    case in: OriginInfo[O] => {
                      val loc=in.asInstanceOf[OriginInfo[O]].loc
                      //report.add(error_factory.generic_error(loc,err))
                      new viper.api.ViperErrorImpl[O](loc,err)
                    }
                    case _ => {
                      new viper.api.ViperErrorImpl[O](in.pos+": "+err)
                      //throw new Error("info is not an origin!")
                    }
                  }
                case _ =>
                  new viper.api.ViperErrorImpl[O](err)
              }
              report.add(error);
              val because="because of "+ve.reason.id
              ve.reason.offendingNode match {
                //ve match {
                case in: viper.silver.ast.Infoed =>
                  //show("offending node's info", in.info)
                  
                  in.info match {
                    case in: OriginInfo[O] => {
                      val loc=in.asInstanceOf[OriginInfo[O]].loc
                      
                      //report.add(error_factory.generic_error(loc,err))
                      error.add_extra(loc,because);
                    }
                    case _ => {
                      error.add_extra(in.pos+": "+because)
                      //throw new Error("info is not an origin!")
                    }
                  }
                case _ =>
                  error.add_extra(because)
              }
            case ae : AbortedExceptionally =>{
              if (detail) show("caused by ", ae.cause)
              report.add(new ViperErrorImpl(null.asInstanceOf[O],ae.fullId));
            }
            case x => {
              report.add(new ViperErrorImpl(null.asInstanceOf[O],x.fullId));
            }
              
          }
         }
       
    }
    Reachable.reachable.map(
      o => reachable.add(o.asInstanceOf[OriginInfo[O]].loc)
    )
    report
  }

  var tool_home : Path = null
  
  def set_tool_home(home:Path)={
    tool_home=home
  }
  
  def get_tool_home():Path={
    tool_home
  }
  var detail:Boolean = false
  
  def set_detail(detail:java.lang.Boolean)={
    this.detail=detail.booleanValue()
  }
  
  def get_detail():java.lang.Boolean = { new java.lang.Boolean(detail) }
  
   // Members declared in viper.api.SilverImplementation
  def createVerifier(tool_home: java.nio.file.Path,settings: java.util.Properties): 
   viper.silver.verifier.Verifier = {
     new viper.silver.verifier.NoVerifier
  }
  
  def get_info[OO](x:Info,y:Position,f:OriginFactory[OO]):OO={
    x match {
      case in: OriginInfo[OO] => {
        in.loc
      }
      case _ => y match {
        case SourcePosition(file,start,tmp) =>
          tmp match {
            case None => f.file(file.toString(),start.line,start.column)
            case Some(end) => f.file(file.toString(),start.line,start.column,
                end.line,end.column)
          }
        case _ => null.asInstanceOf[OO]
      }
    }
  }
  // Members declared in viper.api.SilverVerifier
  def convert[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](verifier: 
   viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],in_prog: viper.api.Prog): P2 = {
    val out_prog /*: P2*/ =verifier.program()
    in_prog.domains.asScala.toList foreach {
      x => throw new Error("domains not supported yet.");
    }
    in_prog.fields.asScala.toList foreach {
      x => verifier.add_field(out_prog,get_info(x.info,x.pos,verifier.get_origin_factory()),x.name,map_type(verifier,x.typ))
    }
    in_prog.functions.asScala.toList foreach {
      m => {
        val body : E2 = m.body match {
          case None => null.asInstanceOf[E2]
          case Some(e) => map_expr(verifier,e)
        }
         verifier.add_function(
            out_prog,
            get_info(m.info,m.pos,verifier.get_origin_factory()),
            m.name,
            map_decls(verifier,m.formalArgs),
            map_type(verifier,m.typ),
            map_expr(verifier,m.pres),
            map_expr(verifier,m.posts),
            body)
     }   
    }
    in_prog.methods.asScala.toList foreach {
      m => {
        verifier.add_method(
            out_prog,
            get_info(m.info,m.pos,verifier.get_origin_factory()),
            m.name,
            map_expr(verifier,m.pres),
            map_expr(verifier,m.posts),
            map_decls(verifier,m.formalArgs),
            map_decls(verifier,m.formalReturns),
            map_decls(verifier,m.locals),
            map_stat(verifier,m.body))
      } 
    }
    in_prog.predicates.asScala.toList foreach {
      m => {
        val body : E2 = m.body match {
          case None => null.asInstanceOf[E2]
          case Some(e) => map_expr(verifier,e)
        }
        verifier.add_predicate(
            out_prog,
            get_info(m.info,m.pos,verifier.get_origin_factory()),
            m.name,
            map_decls(verifier,m.formalArgs),
            body)
      } 
    }
    out_prog
  }
  
  def map_stats[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      verifier:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      stats:Seq[Stmt]):List[S2]={
    stats.map {
      e => map_stat(verifier,e)
    }.asJava
  }
  def map_stat[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      verifier:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      S:Stmt):S2={
     val o=get_info(S.info,S.pos,verifier.get_origin_factory())
     S match {
       case Seqn(s) => verifier.block(o,map_stats(verifier,s))
       case Assert(e) => verifier.assert_(o,map_expr(verifier,e))
       case LocalVarAssign(v,e) => verifier.assignment(o, map_expr(verifier,v), map_expr(verifier,e))
       case FieldAssign(v,e) => verifier.assignment(o, map_expr(verifier,v), map_expr(verifier,e))
       case While(c,invs,local,body) =>
         verifier.while_loop(o,map_expr(verifier,c),
             map_expr(verifier,invs),
             map_decls(verifier,local),
             map_stat(verifier,body))
       case Fold(e) => verifier.fold(o,map_expr(verifier,e))
       case Unfold(e) => verifier.fold(o,map_expr(verifier,e))
       case MethodCall(m,in,out) => verifier.method_call(o,m,
           map_expr(verifier,in),
           map_expr(verifier,out),
           null,
           null
       )
       case Fresh(_) => throw new Error("fresh/constraining not implemented"); 
       case Constraining(_, _) => throw new Error("fresh/constraining not implemented");
       case Exhale(e) => verifier.exhale(o,map_expr(verifier,e))
       case Goto(e) => verifier.goto_(o,e)
       case If(c, s1, s2) => verifier.if_then_else(o,
           map_expr(verifier,c),map_stat(verifier,s1),map_stat(verifier,s2))
       case Inhale(e) => verifier.inhale(o,map_expr(verifier,e))
       case Label(e) => verifier.label(o,e)
       case NewStmt(v, fs) => {
         val names=fs map {
           x => x.name
         }
         val types=fs map {
           x => map_type(verifier,x.typ)
         }
         verifier.new_object(o,map_expr(verifier,v),names.asJava,types.asJava)
       }
     }
  }

  def map_expr[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      verifier:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      exps:Seq[Exp]):List[E2]={
    exps.map {
      e => map_expr(verifier,e)
    }.asJava
  }
  def map_expr[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      v:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      exp:Exp):E2={
     val o=get_info(exp.info,exp.pos,v.get_origin_factory())
     exp match {
       case LocalVar(n) => v.local_name(o,n,map_type(v,exp.typ))
       case IntLit(i) => v.Constant(o,i.toInt)
       case TrueLit() => v.Constant(o,true)
       case FalseLit() => v.Constant(o,false)
       case NullLit() => v.null_(o)
       case FractionalPerm(e1,e2) => v.frac(o,map_expr(v,e1),map_expr(v,e2))
       case EqCmp(e1,e2) => v.eq(o,map_expr(v,e1),map_expr(v,e2))
       case NeCmp(e1,e2) => v.neq(o,map_expr(v,e1),map_expr(v,e2))
       case GtCmp(e1,e2) => v.gt(o,map_expr(v,e1),map_expr(v,e2))
       case LtCmp(e1,e2) => v.lt(o,map_expr(v,e1),map_expr(v,e2))
       case GeCmp(e1,e2) => v.gte(o,map_expr(v,e1),map_expr(v,e2))
       case LeCmp(e1,e2) => v.lte(o,map_expr(v,e1),map_expr(v,e2))
       case Mul(e1,e2) => v.mult(o,map_expr(v,e1),map_expr(v,e2))
       case Mod(e1,e2) => v.mod(o,map_expr(v,e1),map_expr(v,e2))
       case PermDiv(e1,e2) => v.div(o,map_expr(v,e1),map_expr(v,e2))
       case Div(e1,e2) => v.div(o,map_expr(v,e1),map_expr(v,e2))
       case Add(e1,e2) => v.add(o,map_expr(v,e1),map_expr(v,e2))
       case Sub(e1,e2) => v.sub(o,map_expr(v,e1),map_expr(v,e2))
       case Minus(e) => v.neg(o,map_expr(v,e))
       case FieldAccess(e,Field(name,t)) =>
         v.FieldAccess(o,map_expr(v,e),name,map_type(v,t))
       case FieldAccessPredicate(e1,e2) =>
         v.field_access(o,map_expr(v,e1),map_expr(v,e2))
       case FullPerm() => v.write_perm(o)
       case WildcardPerm() => v.read_perm(o)
       case NoPerm() => v.no_perm(o)
       case CurrentPerm(e) => v.current_perm(o,map_expr(v,e));
       case And(e1,e2) => v.and(o,map_expr(v,e1),map_expr(v,e2))
       case Or(e1,e2) => v.or(o,map_expr(v,e1),map_expr(v,e2))
       case Implies(e1,e2) => v.implies(o,map_expr(v,e1),map_expr(v,e2))
       case FuncApp(name,args) => v.function_call(o,name,map_expr(v,args),
           map_type(v, exp.asInstanceOf[FuncApp].typ),
           map_decls(v,exp.asInstanceOf[FuncApp].formalArgs))
       case CondExp(e1,e2,e3) => v.cond(o,map_expr(v,e1),map_expr(v,e2),map_expr(v,e3))
       case Unfolding(e1,e2) => v.unfolding_in(o,map_expr(v,e1),map_expr(v,e2))
       case PredicateAccessPredicate(e1,e2) =>  v.scale_access(o,map_expr(v,e1),map_expr(v,e2))
       case PredicateAccess(args,name) => v.predicate_call(o,name,map_expr(v,args))
       case x => throw new Error("missing case in map expr "+x.getClass())
     }
  }

  def current_perm(o:O,e:Exp):Exp=CurrentPerm(e.asInstanceOf[LocationAccess])(NoPosition,new OriginInfo(o))
  
  
  def map_decls[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      verifier:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      decls:Seq[LocalVarDecl])={
    decls.map {
      d => verifier.decl(get_info(d.info,d.pos,verifier.get_origin_factory()),d.name,map_type(verifier,d.typ))
    }.asJava
  }
  def map_type[Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2](
      verifier:viper.api.SilverVerifier[O,Err2,T2,E2,S2,Decl2,DFunc2,DAxiom2,P2],
      t:Type):T2={
    t match {
      case viper.silver.ast.Int => verifier.Int()
      case viper.silver.ast.Perm => verifier.Perm()
      case viper.silver.ast.Ref => verifier.Ref()
      case viper.silver.ast.Bool => verifier.Bool()
      case DomainType(name, args) => verifier.domain_type(name) // TODO: deal with ARGS
      case MultisetType(t) => verifier.Bag(map_type(verifier,t));
      case SeqType(t) => verifier.List(map_type(verifier,t));
      case SetType(t) => verifier.Set(map_type(verifier,t));
      case TypeVar(name) => throw new Error("cannot handle type variables yet");
    }
  
  }

  def parse_program(x$1: String): viper.api.Prog = {
    Parser.parse_sil(x$1)
  }
  
  var of : viper.api.OriginFactory[O] = null
  
  def get_origin_factory(): viper.api.OriginFactory[O] = of
  def set_origin_factory(x$1: viper.api.OriginFactory[O]): Unit = { of = x$1 }

}

object Parser extends viper.silver.frontend.SilFrontend {
  private var silicon: viper.silver.verifier.NoVerifier = new viper.silver.verifier.NoVerifier

  def parse_sil(name:String) = {
    configureVerifier(Nil);
    init(silicon)
    reset(java.nio.file.Paths.get(name))
    parse()         /* Parse into intermediate (mutable) AST */
    typecheck()     /* Resolve and typecheck */
    translate()     /* Convert intermediate AST to final (mainly immutable) AST */
    //System.err.printf("program is %s%n",_program);
    _program match {
      case Some(Program(domains,fields,functions,predicates,methods)) => 
        val prog=new Prog();
          prog.domains.addAll(domains.asJava)
          prog.fields.addAll(fields.asJava)
          prog.functions.addAll(functions.asJava)
          prog.predicates.addAll(predicates.asJava)
          prog.methods.addAll(methods.asJava)
        prog;
      case _ => throw new Error("empty file");
    }
  }

  def configureVerifier(args: Seq[String]): viper.silver.frontend.SilFrontendConfig = {
    null
  }
  
  def createVerifier(fullCmd: String): viper.silver.verifier.Verifier = {
    new viper.silver.verifier.NoVerifier
  }
  
}
