package vct.silver;

import java.io.PrintWriter;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Map;
import java.util.Properties;

import hre.HREError;
import hre.ast.MessageOrigin;
import hre.ast.Origin;
import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.AxiomaticDataType;
import vct.col.ast.BlockStatement;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.ASTFactory;
import vct.error.VerificationError;
import viper.api.OriginFactory;
import viper.api.SilverVerifier;
import viper.api.ViperError;

public class VerCorsVerifier implements
    SilverVerifier<Origin, VerificationError, Type, ASTNode, ASTNode, DeclarationStatement,
    Method, AxiomaticDataType, ProgramUnit> {

  
  private ASTFactory create=new ASTFactory();
  
  @Override
  public ASTNode add(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Plus, e1,e2);
    leave();
    return res;
  }

  @Override
  public void add_adt(ProgramUnit p, Origin o, String name,
      java.util.List<Method> funs, java.util.List<AxiomaticDataType> axioms,
      java.util.List<String> pars) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void add_field(ProgramUnit p, Origin o, String name, Type t) {
    enter(o);
    p.add(create.field_decl(name, t));
    leave();
  }

  @Override
  public void add_function(ProgramUnit p, Origin o, String name,
      java.util.List<DeclarationStatement> args, Type t,
      java.util.List<ASTNode> pres, java.util.List<ASTNode> posts, ASTNode body) {
    enter(o);
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode c:pres){
      cb.requires(c);
    }
    for(ASTNode c:posts){
      cb.ensures(c);
    }
    Method m=create.function_decl(t,cb.getContract(), name, args.toArray(new DeclarationStatement[0]), body);
    m.setStatic(true);
    p.add(m);
    leave();
  }

  @Override
  public void add_method(ProgramUnit p, Origin o, String name,
      java.util.List<ASTNode> pres, java.util.List<ASTNode> posts,
      java.util.List<DeclarationStatement> in,
      java.util.List<DeclarationStatement> out,
      java.util.List<DeclarationStatement> local, ASTNode body) {
    enter(o);
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode c:pres){
      cb.requires(c);
    }
    for(ASTNode c:posts){
      cb.ensures(c);
    }
    ArrayList<DeclarationStatement> args=new ArrayList();
    for(DeclarationStatement d:in){
      d.setFlag(ASTFlags.IN_ARG,true);
      args.add(d);
    }
    for(DeclarationStatement d:out){
      d.setFlag(ASTFlags.OUT_ARG,true);
      args.add(d);
    }
    BlockStatement block=create.block();
    for(DeclarationStatement d:local){
      block.add(d);
    }
    if(body!=null){
      block.append(body);
    }
    Method m=create.method_decl(
        create.primitive_type(PrimitiveType.Sort.Void),
        cb.getContract(),
        name,
        args.toArray(new DeclarationStatement[0]),
        block);
    m.setStatic(true);
    p.add(m);
    leave();
  }

  @Override
  public void add_predicate(ProgramUnit p, Origin o, String name,
      java.util.List<DeclarationStatement> args, ASTNode body) {
    // TODO Auto-generated method stub
    enter(o);
    Method m=create.predicate(name, body, args.toArray(new DeclarationStatement[0]));
    m.setStatic(true);
    p.add(m);
    leave();   
  }

  @Override
  public ASTNode and(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res;
    if (e1.getType()!=null || e2.getType()!=null){
      res=create.expression(StandardOperator.Star, e1,e2);
    } else {
      res=create.expression(StandardOperator.And, e1,e2);
    }
    leave();
    return res;
  }

  @Override
  public ASTNode any_set_contains(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Member, e2,e1);
    leave();
    return res;
  }

  @Override
  public ASTNode append(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode assert_(Origin o, ASTNode expr) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Assert, expr);
    leave();
    return res;
  }

  @Override
  public ASTNode refute(Origin o, ASTNode expr) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Refute, expr);
    leave();
    return res;
  }

  @Override
  public ASTNode assignment(Origin o, ASTNode loc, ASTNode val) {
    enter(o);
    ASTNode res=create.assignment(loc, val);
    leave();
    return res;
  }

  @Override
  public Type Bag(Type t) {
    enter(null);
    Type res=create.primitive_type(Sort.Bag,t);
    leave();
    return res;
  }

  @Override
  public ASTNode block(Origin o, java.util.List<ASTNode> stats) {
    enter(o);
    BlockStatement res=create.block();
    for(ASTNode S : stats){
      res.add(S);
    }
    leave();
    return res;
  }

  @Override
  public Type Bool() {
    enter(null);
    Type res=create.primitive_type(Sort.Boolean);
    leave();
    return res;
  }

  @Override
  public ASTNode cond(Origin o, ASTNode e1, ASTNode e2, ASTNode e3) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.ITE, e1,e2,e3);
    leave();
    return res;
 }

  @Override
  public ASTNode Constant(Origin o, boolean b) {
    enter(o);
    ASTNode res=create.constant(b);
    leave();
    return res;
  }

  @Override
  public ASTNode Constant(Origin o, int i) {
    enter(o);
    ASTNode res=create.constant(i);
    leave();
    return res;
  }

  @Override
  public <Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2> P2 convert(
      SilverVerifier<Origin, Err2, T2, E2, S2, Decl2, DFunc2, DAxiom2, P2> other,
      ProgramUnit program) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode current_perm(Origin o, ASTNode expr){
    enter(o);
    ASTNode res=create.expression(StandardOperator.CurrentPerm,expr);
    res.setType(create.primitive_type(Sort.Resource));
    leave();
    return res;
  }
  
  @Override
  public AxiomaticDataType daxiom(Origin o, String name, ASTNode expr, String domain) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public DeclarationStatement decl(Origin o, String name, Type type) {
    enter(o);
    DeclarationStatement res=create.field_decl(name, type);
    leave();
    return res;
  }

  @Override
  public Method dfunc(Origin o, String name,
      java.util.List<DeclarationStatement> args, Type t, String domain) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode div(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Div, e1,e2);
    leave();
    return res;
 }

  @Override
  public ASTNode domain_call(Origin o, String name,
      java.util.List<ASTNode> args, Map<String, Type> dpars, Type rt,
      java.util.List<DeclarationStatement> pars, String domain) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public Type domain_type(String name) {
    return create.class_type(name);
  }

  @Override
  public ASTNode drop(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode empty_bag(Origin o, Type t) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode empty_seq(Origin o, Type t) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode empty_set(Origin o, Type t) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  private void enter(Origin o){
    create.enter();
    if (o==null){
      hre.System.Warning("missing origin");
      o=new MessageOrigin("unknown origin");
    }
    create.setOrigin(o);    
  }

  @Override
  public ASTNode eq(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.EQ, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode exhale(Origin o, ASTNode expr) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode exists(Origin o, java.util.List<DeclarationStatement> vars,
      ASTNode e) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode explicit_bag(Origin o, java.util.List<ASTNode> elems) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode explicit_seq(Origin o, java.util.List<ASTNode> elems) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode explicit_set(Origin o, java.util.List<ASTNode> elems) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode field_access(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Perm,e1,e2);
    res.setType(create.primitive_type(Sort.Resource));
    leave();
    return res;
  }

  @Override
  public ASTNode FieldAccess(Origin o, ASTNode obj, String field, Type t) {
    enter(o);
    ASTNode res=create.dereference(obj, field);
    leave();
    return res;
  }

  @Override
  public ASTNode fold(Origin o, ASTNode expr) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Fold,expr);
    leave();
    return res;
  }

  @Override
  public ASTNode forall(Origin o, java.util.List<DeclarationStatement> vars,
      java.util.List<java.util.List<ASTNode>> triggers, ASTNode e) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode frac(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Div, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode function_call(Origin o, String name,
      java.util.List<ASTNode> args, Type rt,
      java.util.List<DeclarationStatement> pars) {
    enter(o);
    ASTNode res=create.invokation(null,null,name, args);
    leave();
    return res;
  }

  @Override
  public Boolean get_detail() {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public Path get_tool_home() {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public Origin getOrigin(Object o) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode goto_(Origin o, String l) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode gt(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.GT, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode gte(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.GTE, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode if_then_else(Origin o, ASTNode c, ASTNode s1, ASTNode s2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode implies(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Implies, e1,e2);
    if (e1.getType()!=null || e2.getType()!=null){
      res.setType(create.primitive_type(Sort.Resource));
    }
    leave();
    return res;
  }

  @Override
  public ASTNode index(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode inhale(Origin o, ASTNode expr) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public Type Int() {
    enter(null);
    Type res=create.primitive_type(Sort.Integer);
    leave();
    return res;
  }

  @Override
  public ASTNode label(Origin o, String l) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  private void leave(){
    create.leave();
  }

  @Override
  public Type List(Type t) {
    enter(null);
    Type res=create.primitive_type(Sort.Sequence,t);
    leave();
    return res;
  }

  @Override
  public ASTNode local_name(Origin o, String name, Type t) {
    enter(o);
    ASTNode res=create.local_name(name);
    res.setType(t);
    leave();
    return res;
  }

  @Override
  public ASTNode lt(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.LT, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode lte(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.LTE, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode method_call(Origin o, String name,
      java.util.List<ASTNode> args, java.util.List<ASTNode> outs,
      java.util.List<DeclarationStatement> pars,
      java.util.List<DeclarationStatement> rets) {
    enter(o);
    ArrayList list=new ArrayList();
    list.addAll(args);
    list.addAll(outs);
    ASTNode res=create.invokation(null,null,name,list);
    leave();
    return res;
  }

  @Override
  public ASTNode mod(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Mod, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode mult(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Mult, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode neg(Origin o, ASTNode e1) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.UMinus, e1);
    leave();
    return res;
  }

  @Override
  public ASTNode neq(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.NEQ, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode new_object(Origin o, ASTNode var,
      java.util.List<String> names, java.util.List<Type> types) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode no_perm(Origin o) {
    enter(o);
    ASTNode res=create.reserved_name(ASTReserved.NoPerm);
    leave();
    return res;
  }

  @Override
  public ASTNode not(Origin o, ASTNode e1) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Not, e1);
    leave();
    return res;
  }

  @Override
  public ASTNode null_(Origin o) {
    enter(o);
    ASTNode res=create.reserved_name(ASTReserved.Null);
    leave();
    return res;
  }

  @Override
  public ASTNode old(Origin o, ASTNode e1) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Mult, e1);
    leave();
    return res;
  }

  @Override
  public ASTNode or(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Or, e1,e2);
    leave();
    return res;
  }

  @Override
  public ProgramUnit parse_program(String file) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public Type Perm() {
    enter(null);
    Type res=create.primitive_type(Sort.Fraction);
    leave();
    return res;
  }

  @Override
  public ASTNode predicate_call(Origin o, String name,
      java.util.List<ASTNode> args) {
    enter(o);
    ASTNode res=create.invokation(null, null, name, args);
    leave();
    return res;
  }

  @Override
  public ProgramUnit program() {
    return new ProgramUnit();
  }

  @Override
  public ASTNode range(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode read_perm(Origin o) {
    enter(o);
    ASTNode res=create.reserved_name(ASTReserved.ReadPerm);
    leave();
    return res;
  }

  
  @Override
  public Type Ref() {
    enter(null);
    Type res=create.class_type("Ref");
    leave();
    return res;
  }
  
  @Override
  public ASTNode result(Origin o, Type t) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode scale_access(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Scale, e1,e2);
    leave();
    return res;
 }
  
  @Override
  public ASTNode seq_contains(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Member, e2,e1);
    leave();
    return res;
  }

  @Override
  public Type Set(Type t) {
    enter(null);
    Type res=create.primitive_type(Sort.Set,t);
    leave();
    return res;
  }

  @Override
  public void set_detail(Boolean detail) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void set_tool_home(Path home) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public ASTNode size(Origin o, ASTNode e1) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode sub(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Minus, e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode take(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode unfold(Origin o, ASTNode expr) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Unfold,expr);
    leave();
    return res;
  }

  @Override
  public ASTNode unfolding_in(Origin o, ASTNode e1, ASTNode e2) {
    enter(o);
    ASTNode res=create.expression(StandardOperator.Unfolding,e1,e2);
    leave();
    return res;
  }

  @Override
  public ASTNode union(Origin o, ASTNode e1, ASTNode e2) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public java.util.List<? extends ViperError<Origin>> verify(Path tool_home,
      Properties settings, ProgramUnit program, java.util.Set<Origin> reachable) {
    // TODO Auto-generated method stub
    throw new HREError("missing case");
  }

  @Override
  public ASTNode while_loop(Origin o, ASTNode cond,
      java.util.List<ASTNode> invs,
      java.util.List<DeclarationStatement> locals, ASTNode body) {
    // TODO Auto-generated method stub
    enter(o);
    BlockStatement block=create.block();
    for(DeclarationStatement d:locals){
      block.add(d);
    }
    block.append(body);
    ASTNode loop=create.while_loop(cond, block, invs.toArray(new ASTNode[invs.size()]));
    leave();
    return loop;
  }

  @Override
  public ASTNode write_perm(Origin o) {
    enter(o);
    ASTNode res=create.reserved_name(ASTReserved.FullPerm);
    leave();
    return res;
  }

  @Override
  public void write_program(PrintWriter pw, ProgramUnit program) {
    // TODO Auto-generated method stub
    
  }
  
  private OriginFactory<Origin> of=new HREOrigins();
  
  @Override
  public void set_origin_factory(OriginFactory<Origin> f) {
    of=f;
  }

  @Override
  public OriginFactory<Origin> get_origin_factory() {
    return of;
  }


}
