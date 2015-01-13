package vct.silver;

import java.util.ArrayList;

import hre.HREError;
import hre.ast.Origin;
import vct.col.ast.*;
import vct.col.util.ASTUtils;
import vct.util.Configuration;
import static hre.System.Abort;

public class SilverStatementMap<T,E,S,Decl> implements ASTMapping<S>{

  private SilverVerifier<Origin,?,T,E,S,Decl,?> create;
  private SilverTypeMap<T> type;

  private SilverExpressionMap<T,E,Decl> expr;

  public SilverStatementMap(SilverVerifier<Origin,?,T,E,S,Decl,?> backend,SilverTypeMap<T> type,SilverExpressionMap<T,E,Decl> expr){
    this.create = backend;
    this.type = type;
    this.expr = expr;
  }

  @Override
  public void pre_map(ASTNode n) {
  }

  @Override
  public S post_map(ASTNode n, S res) {
    if (res==null){
      throw new HREError("cannot map %s to statement",n.getClass());
    }
    return res;
  }

  @Override
  public S map(StandardProcedure p) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ConstantExpression e) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(OperatorExpression e) {
    switch(e.getOperator()){
    case Assert: return create.assert_(e.getOrigin(),e.getArg(0).apply(expr));
    case Assume: return create.inhale(e.getOrigin(),e.getArg(0).apply(expr));
    case Fold: return create.fold(e.getOrigin(),e.getArg(0).apply(expr));
    case Unfold: return create.unfold(e.getOrigin(),e.getArg(0).apply(expr));
      
      default:
        throw new HREError("cannot map operator %s to statement",e.getOperator());
    }
  }

  @Override
  public S map(NameExpression e) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ClassType t) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(FunctionType t) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(PrimitiveType t) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(RecordType t) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(MethodInvokation e) {
    Origin o=e.getOrigin();
    Method m=e.getDefinition();
    String name=m.name;
    ArrayList<E> args=new ArrayList();
    ArrayList<E> outs=new ArrayList();
    ArrayList<Decl> pars=new ArrayList();
    ArrayList<Decl> rets=new ArrayList();
    int N=e.getArity();
    DeclarationStatement decl[]=m.getArgs();
    for(int i=0;i<N;i++){
      if (decl[i].isValidFlag(ASTFlags.OUT_ARG) && decl[i].getFlag(ASTFlags.OUT_ARG)){
        outs.add(e.getArg(i).apply(expr));
        rets.add(create.decl(o, decl[i].name, decl[i].getType().apply(type)));
      } else {
        args.add(e.getArg(i).apply(expr));
        pars.add(create.decl(o, decl[i].name, decl[i].getType().apply(type)));
      }
    }
    return create.method_call(o, name, args, outs, pars, rets);
  }

  @Override
  public S map(BlockStatement s) {
    ArrayList<S> stats=new ArrayList();
    for(ASTNode n:s){
      stats.add(n.apply(this));
    }
    return create.block(s.getOrigin(), stats);
  }

  @Override
  public S map(IfStatement s) {
    int i=s.getCount()-1;
    S res;
    if (s.getGuard(i).isConstant(true)){
      res=s.getStatement(i).apply(this);
      i=i-1;
    } else {
      res=create.block(s.getOrigin(),new ArrayList());
    }
    while(i>=0){
      res=create.if_then_else(s.getOrigin(), s.getGuard(i).apply(expr),s.getStatement(i).apply(this),res);
      i=i-1;
    }
    return res;
  }

  @Override
  public S map(ReturnStatement s) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(AssignmentStatement s) {
    if (s.getExpression().isa(StandardOperator.NewSilver)){
      //Configuration.getDiagSyntax().print(System.err, s);
      ArrayList<String> names=new ArrayList();
      ArrayList<T> types=new ArrayList();
      ASTNode args[]=((OperatorExpression)s.getExpression()).getArguments();
      for(int i=0;i<args.length;i++){
        Dereference d=(Dereference)args[i];
        names.add(d.field);
        types.add(d.getType().apply(type));
      }
      return create.new_object(s.getOrigin(),s.getLocation().apply(expr),names,types);
    } else {
      return create.assignment(s.getOrigin(),s.getLocation().apply(expr),s.getExpression().apply(expr));
    }
  }

  @Override
  public S map(DeclarationStatement s) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(LoopStatement s) {
    Origin o=s.getOrigin();
    if (s.getInitBlock()!=null) Abort("not a while loop");
    if (s.getExitGuard()!=null) Abort("not a while loop");
    ArrayList<Decl> locals=new ArrayList();
    ArrayList<S> stats=new ArrayList();
    SilverBackend.split_block(create, type, this, locals,(BlockStatement) s.getBody(), stats);
    ArrayList<E> invs=new ArrayList();
    for(ASTNode inv:ASTUtils.conjuncts(s.getContract().invariant,StandardOperator.Star)){
      invs.add(inv.apply(expr));
    }
    return create.while_loop(o, s.getEntryGuard().apply(expr), invs, locals, create.block(o, stats));
  }

  @Override
  public S map(Method m) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ASTClass c) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ASTWith astWith) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(BindingExpression e) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(Dereference e) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(Lemma lemma) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ParallelBarrier parallelBarrier) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ParallelBlock parallelBlock) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(Contract contract) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ASTSpecial special) {
    switch(special.kind){
    case Goto:
      return create.goto_(special.getOrigin(),special.args[0].toString());
    case Label:
      return create.label(special.getOrigin(),special.args[0].toString());
    default:
      throw new HREError("cannot map special %s",special.kind);
    }
  }

  @Override
  public S map(VariableDeclaration variableDeclaration) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(TupleType tupleType) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(AxiomaticDataType adt) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(Axiom axiom) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(Hole hole) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ActionBlock actionBlock) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public S map(ASTSpecialDeclaration s) {
    switch(s.kind){
    default:
      throw new HREError("cannot map special declaration %s",s.kind);
    }
  }

  @Override
  public S map(TypeExpression t) {
    // TODO Auto-generated method stub
    return null;
  }


}
