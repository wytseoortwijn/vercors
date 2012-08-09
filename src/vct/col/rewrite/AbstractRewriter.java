package vct.col.rewrite;

import java.util.Arrays;

import hre.util.FieldStack;
import hre.util.FrameControl;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTWith;
import vct.col.ast.AbstractVisitor;
import vct.col.ast.MethodInvokation;
import vct.col.ast.ArrayType;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.FunctionType;
import vct.col.ast.IfStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.RecordType;
import vct.col.ast.ReturnStatement;
import vct.col.ast.StandardOperator;
import vct.col.ast.StandardProcedure;
import vct.col.ast.Type;
import vct.col.util.ASTFactory;
import vct.col.util.ASTPermission;
import static hre.System.*;

/**
 * This abstract rewriter copies the AST it is applied to.
 * 
 * @author Stefan Blom
 */ 
public abstract class AbstractRewriter extends AbstractVisitor<ASTNode> {

  /**
   * Refers to the resulting package of the current package being rewritten.
   */
  protected ASTClass currentPackage=null;
  /**
   * Refers to the resulting class of the current class being rewritten.
   */
  protected ASTClass currentClass=null;
  
  /**
   * This variable references an AST factory, whose Origin is set to
   * the origin of the current node being rewritten.
   */
  public final ASTFactory create;
      
  public AbstractRewriter(){
    create=new ASTFactory();
  }
  
  public void pre_visit(ASTNode n){
    super.pre_visit(n);
    for(NameExpression lbl:n.getLabels()){
      Debug("enter %s with label %s",n.getClass(),lbl);
    }
    create.enter();
    create.setOrigin(n.getOrigin());
    result=null;
  }
  
  public void post_visit(ASTNode n){
    if (result==n) Debug("rewriter linked instead of making a copy"); 
    if (result!=null && result!=n) {
      ASTNode tmp=result;
      for(NameExpression lbl:n.getLabels()){
        Debug("leave %s with label %s",n.getClass(),lbl);
        tmp.addLabel(rewrite_and_cast(lbl));
      }
      result=tmp;
      result.copyMissingFlags(n);
    }
    create.leave();
    super.post_visit(n);
  }

  public Contract rewrite(Contract c){
    return new Contract(rewrite_and_cast(c.given),rewrite_and_cast(c.yields),rewrite_nullable(c.modifies),rewrite(c.pre_condition),rewrite(c.post_condition));
  }

  public ASTNode rewrite(ASTNode node){
    return node.apply(this);
  }
  
  public ASTNode[] rewrite(ASTNode array[]){
    ASTNode[] res=new ASTNode[array.length];
    for(int i=0;i<array.length;i++){
      res[i]=array[i].apply(this);
    }
    return res;
  }
  public <E extends ASTNode> E rewrite_and_cast(E node){
    ASTNode tmp=node.apply(this);
    try {
      return (E)tmp;
    } catch (ClassCastException e) {
     throw new Error("Expected "+node.getClass()+ " got " + tmp.getClass()); 
    }
  }
  public <E extends ASTNode> E[] rewrite_and_cast(E node[]){
    E res[]=Arrays.copyOf(node, node.length);
    for(int i=0;i<res.length;i++){
      res[i]=rewrite_and_cast(res[i]);
    }
    return res;
  }
  public <E extends ASTNode> E rewrite_nullable(E node){
    if (node==null) return null;
    return rewrite_and_cast(node);
  }
  public <E extends ASTNode> E[] rewrite_nullable(E node[]){
    if (node==null) return null;
    E res[]=Arrays.copyOf(node, node.length);
    for(int i=0;i<res.length;i++){
      res[i]=rewrite_and_cast(res[i]);
    }
    return res;
  }

  @Override
  public void visit(MethodInvokation e) {
    ASTNode object=rewrite_nullable(e.object);
    NameExpression method=rewrite_and_cast(e.method);
    int N=e.getArity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    result=create.invokation(object,e.guarded,method,args);
  }

  @Override
  public void visit(AssignmentStatement s) {
    ASTNode loc=s.getLocation().apply(this);
    ASTNode val=s.getExpression().apply(this);
    result=create.assignment(loc,val);
  }

  @Override
  public void visit(ASTClass c) {
    //checkPermission(c);
    String name=c.getName();
    if (name==null) {
      Debug("rewriting root class");
      if (c.getDynamicCount()>0) throw new Error("root class with dynamic content");
      ASTClass res=new ASTClass();
      res.setOrigin(c.getOrigin());
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        currentPackage=res;
        res.add_static(c.getStatic(i).apply(this));
      }
      result=res;
    } else {
      Debug("rewriting class "+name);
      ASTClass res=new ASTClass(name,c.kind,c.super_classes,c.implemented_classes);
      res.setOrigin(c.getOrigin());
      if (c.isPackage()) {
        currentPackage.add_static(res);
      } else {
        currentClass=res;
      }
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        if (c.isPackage()) currentPackage=res;
        res.add_static(c.getStatic(i).apply(this));
      }
      int M=c.getDynamicCount();
      for(int i=0;i<M;i++){
        res.add_dynamic(c.getDynamic(i).apply(this));
      }
      if (c.isPackage()){
        result=null;
      } else{
        result=res;
        currentClass=null;
      }
    }
  }

  @Override
  public void visit(ASTWith t){
    ASTNode body=t.body.apply(this);
    result=create.with(t.from,t.kind,t.all,body);
  }
  
  @Override
  public void visit(BlockStatement s) {
    //checkPermission(s);
    Debug("rewriting block");
    BlockStatement res=new BlockStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getLength();
    for (int i=0;i<N;i++){
      ASTNode n=s.getStatement(i).apply(this);
      if (n==null) Abort("Got null rewriting %s at %s",s.getStatement(i).getClass(),s.getStatement(i).getOrigin());
      Debug("adding %s",n.getClass());
      res.add_statement(n);
    }
    result=res; return ;
  }

  public void visit(ClassType t){
    //checkPermission(t);
    ClassType res=new ClassType(t.name);
    res.setOrigin(t.getOrigin());
    result=res; return ;    
  }
  
  @Override
  public void visit(ConstantExpression e) {
    //checkPermission(e);
    result=new ConstantExpression(e.getValue(),e.getType(),e.getOrigin());
  }
  
  @Override
  public void visit(DeclarationStatement s) {
    //checkPermission(s);
    Type t=s.getType();
    ASTNode tmp=t.apply(this);
    if (tmp instanceof Type){
      t=(Type)tmp;
    } else {
      throw new Error("type AST rewrote to non-type AST");
    }
    String name=s.getName();
    ASTNode init=s.getInit();
    if (init!=null) init=init.apply(this);
    DeclarationStatement res=new DeclarationStatement(name,t,init);
    res.setOrigin(s.getOrigin());
    result=res; return ;
  }

  public void visit(FunctionType t){
    //checkPermission(t);
    int N=t.getArity();
    Type args[]=new Type[N];
    for(int i=0;i<N;i++){
      args[i]=(Type)t.getArgument(i).apply(this);
    }
    Type result_type=(Type)t.getResult().apply(this);
    ASTNode res=new FunctionType(args,result_type);
    if (t.getOrigin()!=null) res.setOrigin(t);
    result=res;
  }
  


  @Override
  public void visit(IfStatement s) {
    //checkPermission(s);
    IfStatement res=new IfStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getCount();
    for(int i=0;i<N;i++){
      ASTNode guard=s.getGuard(i);
      if (guard!=IfStatement.else_guard) guard=guard.apply(this);
      ASTNode body=s.getStatement(i);
      body=body.apply(this);
      res.addClause(guard,body);
    }
    result=res; return ;
  }

  @Override
  public void visit(LoopStatement s) {
    //checkPermission(s);
    LoopStatement res=new LoopStatement();
    ASTNode tmp;
    tmp=s.getInitBlock();
    if (tmp!=null) res.setInitBlock(tmp.apply(this));
    tmp=s.getUpdateBlock();
    if (tmp!=null) res.setUpdateBlock(tmp.apply(this));
    tmp=s.getEntryGuard();
    if (tmp!=null) res.setEntryGuard(tmp.apply(this));
    tmp=s.getExitGuard();
    if (tmp!=null) res.setExitGuard(tmp.apply(this));
    for(ASTNode inv:s.getInvariants()){
      res.appendInvariant(inv.apply(this));
    }
    tmp=s.getBody();
    res.setBody(tmp.apply(this));
    res.setOrigin(s.getOrigin());
    result=res; return ;
  }

  @Override
  public void visit(Method m) {
    //checkPermission(m);
    String name=m.getName();
    int N=m.getArity();
    DeclarationStatement args[]=rewrite_and_cast(m.getArgs());
    Contract mc=m.getContract();
    Contract c=null;
    if (mc!=null){
      c=rewrite(mc);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite_and_cast(m.getReturnType());
    ASTNode body=rewrite_nullable(m.getBody());
    Method res=new Method(kind,name,rt,c,args,body);
    res.setOrigin(m.getOrigin());
    result=res;
  }

  @Override
  public void visit(NameExpression e) {
    //checkPermission(e);
    NameExpression res=new NameExpression(e.getName());
    res.setKind(e.getKind());
    res.setOrigin(e.getOrigin());
    result=res;
  }

  @Override
  public void visit(OperatorExpression e) {
    //checkPermission(e);
    StandardOperator op=e.getOperator();
    int N=op.arity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    OperatorExpression res=new OperatorExpression(op,args);
    res.setOrigin(e.getOrigin());
    result=res;
  }

  public void visit(PrimitiveType t){
    //checkPermission(t);
    PrimitiveType res=new PrimitiveType(t.sort);
    res.setOrigin(t);
    result=res;
  }

  public void visit(RecordType t){
    //checkPermission(t);
    throw new Error("missing case in rewriter: "+t.getClass());
  }

  @Override
  public void visit(ReturnStatement s) {
    //checkPermission(s);
    ASTNode val=s.getExpression();
    if(val!=null) val=val.apply(this);
    ReturnStatement res=new ReturnStatement(val);
    res.setOrigin(s.getOrigin());
    result=res;
  }
  @Override
  public void visit(StandardProcedure p) {
    //checkPermission(p);
    StandardProcedure res=new StandardProcedure(p.getOperator());
    res.setOrigin(p.getOrigin());
    result=res;
  }
}
