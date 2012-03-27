package vct.col.ast;

/**
 * Recursive scanning of an AST.
 *
 * Because the scanner is built on top of the abstract visitor,
 * a node is always visited in pre-order. This class may be
 * extended in order to allow the current node to be visited more often.
 * 
 * @author sccblom
 *
 */
public abstract class AbstractScanner implements ASTVisitor<Boolean> {

  public void setResult(Boolean b){
    abort=b.booleanValue();
  }

  public Boolean getResult(){
    return new Boolean(abort);
  }
  
  /** Return from the current scan if set. */
  public boolean abort=false;

  /** Any overriding method should call this method first. 
   * 
   */
  @Override
  public void pre_visit(ASTNode n) {
    // push state
    // state=enter
  }

  /** Any overriding method should call this method last. 
   * 
   */
  @Override
  public void post_visit(ASTNode n) {
    // pop state
  }

  @Override
  public void visit(StandardProcedure p) {
    // has no children
  }

  @Override
  public void visit(Instantiation i) {
    i.getSort().accept(this);
    int N=i.getArity();
    for(int j=0;j<N && ! abort;j++){
      i.getArg(j).accept(this);
    }
  }

  @Override
  public void visit(ConstantExpression e) {
    // Constants have no children.
  }

  @Override
  public void visit(OperatorExpression e) {
    int N=e.getOperator().arity();
    for(int i=0;i<N && ! abort;i++){
      e.getArg(i).accept(this);
    }
  }

  @Override
  public void visit(NameExpression e) {
    // Names have no children.
  }

  @Override
  public void visit(ArrayType t) {
    // TODO Auto-generated method stub
    throw new Error("missing case in Abstract Scanner: "+t.getClass());
  }

  @Override
  public void visit(ClassType t) {
    // Class types have no children.
  }

  @Override
  public void visit(FunctionType t) {
    // TODO Auto-generated method stub
    throw new Error("missing case in Abstract Scanner: "+t.getClass());
  }

  @Override
  public void visit(PrimitiveType t) {
    // Primitive types have no children.
  }

  @Override
  public void visit(RecordType t) {
    // TODO Auto-generated method stub
    throw new Error("missing case in Abstract Scanner: "+t.getClass());
  }

  @Override
  public void visit(MethodInvokation e) {
    if (e.object!=null) e.object.accept(this);
    e.method.accept(this);
    int N=e.getArity();
    for(int i=0;i<N;i++){
      e.getArg(i).accept(this);
    }
  }

  @Override
  public void visit(BlockStatement s) {
    int N=s.getLength();
    for (int i=0;i<N;i++){
      s.getStatement(i).accept(this);
    }
  }

  @Override
  public void visit(IfStatement s) {
    int N=s.getCount();
    for(int i=0;i<N;i++){
      s.getGuard(i).accept(this);
      s.getStatement(i).accept(this);
    }
  }

  @Override
  public void visit(ReturnStatement s) {
    ASTNode expr=s.getExpression();
    if (expr!=null) expr.accept(this);
  }

  @Override
  public void visit(AssignmentStatement s) {
    s.getLocation().accept(this);
    s.getExpression().accept(this);
  }

  @Override
  public void visit(DeclarationStatement s) {
    Type t=s.getType();
    String name=s.getName();
    ASTNode init=s.getInit();
    if (init != null) init.accept(this);
  }

  @Override
  public void visit(LoopStatement s) {
    for(ASTNode inv:s.getInvariants()){
      inv.accept(this);
    }
    ASTNode tmp;
    tmp=s.getInitBlock();
    if (tmp!=null) tmp.accept(this);
    tmp=s.getEntryGuard();
    if (tmp!=null) tmp.accept(this);
    tmp=s.getBody();
    if (tmp!=null) tmp.accept(this);
    tmp=s.getExitGuard();
    if (tmp!=null) tmp.accept(this);
  }

  @Override
  public void visit(Method m) {
    String name=m.getName();
    int N=m.getArity();
    String args[]=new String[N];
    for(int i=0;i<N;i++){
      args[i]=m.getArgument(i);
    }
    Contract contract=m.getContract();
    if (contract!=null){
      contract.pre_condition.accept(this);
      contract.post_condition.accept(this);
    }
    ASTNode body=m.getBody();
    if (body!=null) body.accept(this);
  }

  @Override
  public void visit(ASTClass c) {
    int N=c.getStaticCount();
    for(int i=0;i<N;i++){
      c.getStatic(i).accept(this);
    }
    int M=c.getDynamicCount();
    for(int i=0;i<M;i++){
      c.getDynamic(i).accept(this);
    }
  }

  @Override
  public void visit(ASTWith w) {
    w.body.accept(this);
  }
  
  public void visit(BindingExpression e){
    e.select.accept(this);
    if (abort) return;
    e.main.accept(this);
  }

}
