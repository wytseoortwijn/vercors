package vct.col.rewrite;

import java.util.Arrays;
import java.util.HashSet;

import hre.util.FrameControl;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTWith;
import vct.col.ast.AbstractVisitor;
import vct.col.ast.ContractBuilder;
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
import vct.col.ast.ProgramUnit;
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
public class AbstractRewriter extends AbstractVisitor<ASTNode> {

  private static ThreadLocal<AbstractRewriter> tl=new ThreadLocal<AbstractRewriter>();

  public final AbstractRewriter copy_rw;
  
  private AbstractRewriter(Thread t){
    copy_rw=null;
    create=new ASTFactory();    
  }
  
  public AbstractRewriter(ProgramUnit source,ProgramUnit target){
    super(source,target);
    AbstractRewriter tmp=tl.get();
    if(tmp==null){
      tmp=new AbstractRewriter(Thread.currentThread());
      tl.set(tmp);
    }
    copy_rw=tmp;
    create=new ASTFactory();    
  }

  /**
   * Refers to the resulting class of the current class being rewritten.
   */
  protected ASTClass currentClass=null;
  
  /**
   * Prevent automatic copying of labels.
   */
  protected boolean auto_labels=true;
  
  /**
   * Prevent automatic copying of before and after blocks.
   */
  protected boolean auto_proof=true;
  
  /**
   * This variable references an AST factory, whose Origin is set to
   * the origin of the current node being rewritten.
   */
  public final ASTFactory create;
      
  public AbstractRewriter(ProgramUnit source){
    this(source,new ProgramUnit());
  }
  
  public void pre_visit(ASTNode n){
    super.pre_visit(n);
    for(NameExpression lbl:n.getLabels()){
      Debug("enter %s with label %s",n.getClass(),lbl);
    }
    auto_labels=true;
    create.enter();
    create.setOrigin(n.getOrigin());
    result=null;
  }
  
  public void post_visit(ASTNode n){
    if (result==n) Debug("rewriter linked instead of making a copy"); 
    if (result!=null && result!=n) {
      if (auto_labels){
        ASTNode tmp=result;
        for(NameExpression lbl:n.getLabels()){
          Debug("leave %s with label %s",n.getClass(),lbl);
          NameExpression copy=new NameExpression(lbl.getName());
          copy.setKind(NameExpression.Kind.Label);
          copy.setOrigin(lbl.getOrigin());
          tmp.addLabel(copy);
        }
        result=tmp;
      }
      if (auto_proof){
        if (n.get_before()!=null && result.get_before()==null){
          ASTNode tmp=result;
          tmp.set_before(rewrite(n.get_before()));
          result=tmp;
        }
        if (n.get_after()!=null && result.get_after()==null){
          ASTNode tmp=result;
          tmp.set_after(rewrite(n.get_after()));
          result=tmp;
        }
      }
      result.copyMissingFlags(n);
    }
    auto_proof=true;
    auto_labels=true;
    create.leave();
    super.post_visit(n);
  }

  /** Rewrite contract while adding to a contract builder. */
  public void rewrite(Contract c,ContractBuilder cb){
    cb.given(rewrite(c.given));
    cb.yields(rewrite(c.yields));
    if (c.modifies!=null) cb.modifies(rewrite(c.modifies));
    cb.requires(rewrite(c.pre_condition));
    cb.ensures(rewrite(c.post_condition));
  }
  public Contract rewrite(Contract c){
    if (c==null) return null;
    return new Contract(rewrite(c.given),rewrite(c.yields),rewrite(c.modifies),rewrite(c.pre_condition),rewrite(c.post_condition));
  }

  public <E extends ASTNode> E rewrite(E node){
    if (node==null) return null;
    ASTNode tmp=node.apply(this);
    try {
      return (E)tmp;
    } catch (ClassCastException e) {
     throw new Error("Expected "+node.getClass()+ " got " + tmp.getClass()); 
    }
  }
  
  private final <E extends ASTNode> E[] glue(E... args){
    return args;
  }
  public <E extends ASTNode> E[] rewrite(E head,E[] tail){
    // TODO: figure out how to do it if tail == null.
    E[] res;
    if (tail==null) {
      res=glue(head);
    } else {
      res=Arrays.copyOf(tail, tail.length+1);
    }
    res[0]=rewrite(head);
    for(int i=0;i<tail.length;i++){
      res[i+1]=rewrite(tail[i]);
    }
    return res;
  }
  
  /**
   * Rewrite an array.
   * If the given array is null then this function will return null.
   * If any of the elements of the array is null, the corresponding element will
   * also be null.
   * @param <E> The type of the array elements. 
   * @param node The array to be rewritten.
   * @return A new array with rewritten elements.
   */
  public <E extends ASTNode> E[] rewrite(E node[]){
    if (node==null) return null;
    E res[]=Arrays.copyOf(node, node.length);
    for(int i=0;i<res.length;i++){
      res[i]=rewrite(res[i]);
    }
    return res;
  }
  @Override
  public void visit(MethodInvokation e) {
    ASTNode object=rewrite(e.object);
    NameExpression method=rewrite(e.method);
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
      Abort("illegal class without name");
    } else {
      Debug("rewriting class "+name);
      ASTClass res=new ASTClass(name,c.kind,c.super_classes,c.implemented_classes);
      res.setOrigin(c.getOrigin());
      currentClass=res;
      Contract contract=c.getContract();
      if (contract!=null){
        res.setContract(rewrite(contract));
      }
      int N=c.getStaticCount();
      for(int i=0;i<N;i++){
        res.add_static(c.getStatic(i).apply(this));
      }
      int M=c.getDynamicCount();
      for(int i=0;i<M;i++){
        res.add_dynamic(c.getDynamic(i).apply(this));
      }
        result=res;
        currentClass=null;
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
    ClassType res=new ClassType(t.getNameFull());
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
      Abort("Type %s rewrote to non-type %s",t.getClass(),tmp==null ? "null":tmp.getClass());
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
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract mc=m.getContract();
    Contract c=null;
    if (mc!=null){
      c=rewrite(mc);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    ASTNode body=rewrite(m.getBody());
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

  public ProgramUnit rewriteAll() {
    for(ASTClass cl:source().classes()){
      ASTClass tmp=rewrite(cl);
      if (tmp!=null){
        target().addClass(tmp.getFullName(),tmp);
      }
    }
    return target();
  }
  
  private void rewriteOrdered(HashSet<ASTClass> done,ASTClass cl){
    if (!done.contains(cl)){
      done.add(cl);
      for(ClassType parent:cl.implemented_classes){
        Fail("interfaces are not supported");
      }
      for(ClassType parent:cl.super_classes){
        rewriteOrdered(done,source().find(parent));
      }
      Debug("rewriting %s",cl.getName());
      ASTClass tmp=rewrite(cl);
      if (tmp!=null){
        target().addClass(tmp.getFullName(),tmp);
      }      
    }
  }
  public ProgramUnit rewriteOrdered() {
    HashSet<ASTClass> done=new HashSet();
    for(ASTClass cl:source().classes()){
      rewriteOrdered(done,cl);
    }    
    return target();
  }
 
}
