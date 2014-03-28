package vct.col.rewrite;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import hre.ast.Origin;
import hre.util.FrameControl;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTDeclaration;
import vct.col.ast.ASTFlags;
import vct.col.ast.ASTFrame;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.ASTSpecial;
import vct.col.ast.ASTWith;
import vct.col.ast.AbstractVisitor;
import vct.col.ast.BindingExpression;
import vct.col.ast.CompilationUnit;
import vct.col.ast.ContractBuilder;
import vct.col.ast.Dereference;
import vct.col.ast.Lemma;
import vct.col.ast.MethodInvokation;
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
import vct.col.ast.ParallelBarrier;
import vct.col.ast.ParallelBlock;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.RecordType;
import vct.col.ast.ReturnStatement;
import vct.col.ast.StandardOperator;
import vct.col.ast.StandardProcedure;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;
import vct.col.util.ASTFactory;
import vct.col.util.ASTPermission;
import vct.col.util.ASTUtils;
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
  
  public AbstractRewriter(ASTFrame<ASTNode> shared){
    super(shared);
    AbstractRewriter tmp=tl.get();
    if(tmp==null){
      tmp=new AbstractRewriter(Thread.currentThread());
      tl.set(tmp);
    }
    copy_rw=tmp;
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
   * Refers to the block that is the result of rewriting the current block.
   */
  protected BlockStatement currentBlock=null;
  
  
  protected ASTSequence<?> current_sequence(){
    if (currentBlock!=null) return currentBlock;
    return currentClass;
  }
  
  /**
   * Refer to the contract builder, used for the contract of the current method. 
   */
  protected ContractBuilder currentContractBuilder=null;
  
  /**
   * Prevent automatic copying of labels.
   */
  protected boolean auto_labels=true;
  
  /**
   * This variable references an AST factory, whose Origin is set to
   * the origin of the current node being rewritten.
   */
  public final ASTFactory create;
  
  public final ASTFactory create(Origin origin){
    create.setOrigin(origin);
    return create;
  }
  public final ASTFactory create(ASTNode node){
    create.setOrigin(node.getOrigin());
    return create;
  }
  
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
  public void copy_labels(ASTNode dest,ASTNode source){
    for(NameExpression lbl:source.getLabels()){
      NameExpression copy=new NameExpression(lbl.getName());
      copy.setKind(NameExpression.Kind.Label);
      copy.setOrigin(lbl.getOrigin());
      dest.addLabel(copy);
    }    
  }
  public void post_visit(ASTNode n){
    if (result==n) Debug("rewriter linked instead of making a copy"); 
    if (result!=null && result!=n) {
      if (auto_labels){
        ASTNode tmp=result;
        copy_labels(tmp,n);
        result=tmp;
      }
      result.copyMissingFlags(n);
      if (n.annotated() && !result.annotated()){
        ASTNode tmp=result;
        for(ASTNode ann:n.annotations()){
          tmp.attach(rewrite(ann));
        }
        result=tmp;
      }
    }
    auto_labels=true;
    if (result!=null && result instanceof LoopStatement){
      ((LoopStatement)result).fixate();
    }
    create.leave();
    super.post_visit(n);
  }

  protected boolean in_invariant=false;
  protected boolean in_requires=false;
  protected boolean in_ensures=false;
  
  /** Rewrite contract while adding to a contract builder. */
  public void rewrite(Contract c,ContractBuilder cb){
    if (c==null) return;
    cb.given(rewrite(c.given));
    cb.yields(rewrite(c.yields));
    if (c.modifies!=null) cb.modifies(rewrite(c.modifies)); 
    in_invariant=true;
    for(ASTNode clause:ASTUtils.conjuncts(c.invariant)){
      cb.appendInvariant(rewrite(clause));
    }
    in_invariant=false;
    in_requires=true;
    for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition)){
      cb.requires(rewrite(clause));
    }
    in_requires=false;
    in_ensures=true;
    for(ASTNode clause:ASTUtils.conjuncts(c.post_condition)){
      cb.ensures(rewrite(clause));
    }
    in_ensures=false;
    if (c.signals!=null) for(DeclarationStatement decl:c.signals){
      cb.signals((ClassType)rewrite(decl.getType()),decl.getName(),rewrite(decl.getInit()));      
    }
    //cb.requires(rewrite(c.pre_condition));
    //cb.ensures(rewrite(c.post_condition));
  }
  public Contract rewrite(Contract c){
    if (c==null) return null;
    ContractBuilder cb=new ContractBuilder();
    rewrite(c,cb);
    return cb.getContract();
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
    int N=e.getArity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    MethodInvokation res=create.invokation(object,rewrite(e.dispatch),e.method,args);
    res.set_before(rewrite(e.get_before()));
    res.set_after(rewrite(e.get_after()));
    result=res;
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
      currentContractBuilder=new ContractBuilder();
      if (contract!=null){
        rewrite(contract,currentContractBuilder);
      }
      res.setContract(currentContractBuilder.getContract());
      currentContractBuilder=null;
      for(ASTNode item:c){
        res.add(rewrite(item));
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
    BlockStatement tmp=currentBlock;
    currentBlock=new BlockStatement();
    currentBlock.setOrigin(s.getOrigin());
    int N=s.getLength();
    for (int i=0;i<N;i++){
      ASTNode n=s.getStatement(i).apply(this);
      if (n==null) {
        Debug("Got null rewriting %s at %s",s.getStatement(i).getClass(),s.getStatement(i).getOrigin());
      } else {
        Debug("adding %s",n.getClass());
        currentBlock.add_statement(n);
      }
    }
    result=currentBlock;
    currentBlock=tmp;
  }

  public void visit(ClassType t){
    //checkPermission(t);
    ClassType res=new ClassType(t.getNameFull(),rewrite(t.getArgs()));
    res.setOrigin(t.getOrigin());
    result=res; return ;    
  }
  
  @Override
  public void visit(Contract c){
    result=rewrite(c);
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
    res.appendContract(rewrite(s.getContract()));
    tmp=s.getBody();
    res.setBody(tmp.apply(this));
    res.set_before(rewrite(s.get_before()));
    res.set_after(rewrite(s.get_after()));
    res.setOrigin(s.getOrigin());
    result=res; return ;
  }

  @Override
  public void visit(Method m) {
    //checkPermission(m);
    String name=m.getName();
    int N=m.getArity();
    if (currentContractBuilder==null) currentContractBuilder=new ContractBuilder();
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract mc=m.getContract();
    if (mc!=null){
      rewrite(mc,currentContractBuilder);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    Contract c=currentContractBuilder.getContract();
    currentContractBuilder=null;
    ASTNode body=rewrite(m.getBody());
    result=create.method_kind(kind, rt, c, name, args, m.usesVarArgs(), body);
  }

  @Override
  public void visit(NameExpression e) {
    //checkPermission(e);
    NameExpression res=new NameExpression(e.getKind(),e.reserved(),e.getName());
    res.setOrigin(e.getOrigin());
    result=res;
  }

  @Override
  public void visit(OperatorExpression e) {
    //checkPermission(e);
    StandardOperator op=e.getOperator();
    int N=op.arity();
    if(N<0) N=e.getArguments().length;
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    OperatorExpression res=new OperatorExpression(op,args);
    res.set_before(rewrite(e.get_before()));
    res.set_after(rewrite(e.get_after()));
    res.setOrigin(e.getOrigin());
    result=res;
  }

  public void visit(PrimitiveType t){
    //checkPermission(t);
    PrimitiveType res=new PrimitiveType(t.sort,rewrite(t.getArgs()));
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
    res.set_after(rewrite(s.get_after()));
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
    for(CompilationUnit cu :source().get()){
      CompilationUnit res=new CompilationUnit(cu.getFileName());
      res.attach(target());
      for(ASTNode n:cu.get()){
        ASTNode tmp=rewrite(n);
        if (tmp!=null){
          res.add(tmp);
        }
      }
      if (res.size()>0){
        target().add(res);
      } else {
        Debug("discarding empty unit %s",cu.getFileName());
      }
    }
    return target();
  }

  private void rewriteOrdered(HashSet<ASTClass> done,HashMap<ASTClass,CompilationUnit> target,ASTClass cl){
    if (!done.contains(cl)){
      done.add(cl);
      for(ClassType parent:cl.implemented_classes){
        Fail("interfaces are not supported");
      }
      for(ClassType parent:cl.super_classes){
        rewriteOrdered(done,target,source().find(parent));
      }
      Debug("rewriting %s",cl.getName());
      ASTClass tmp=rewrite(cl);
      if (tmp!=null){
        CompilationUnit res=target.get(cl);
        res.add(tmp);
      }      
    }
  }

  public ProgramUnit rewriteOrdered() {
    HashSet<ASTClass> done=new HashSet();
    HashMap<ASTClass,CompilationUnit> target=new HashMap();
    for(CompilationUnit cu :source().get()){
      CompilationUnit res=new CompilationUnit(cu.getFileName());
      res.attach(target());
      target().add(res);
      for(ASTNode n:cu.get()){
        if (n instanceof ASTClass) {
          target.put((ASTClass)n,res);
          continue;
        }
        ASTNode tmp=rewrite(n);
        if (tmp!=null){
          res.add(tmp);
        }
      }
    }
    for(CompilationUnit cu :source().get()){
      for(ASTNode n:cu.get()){
        if (n instanceof ASTClass) rewriteOrdered(done,target,(ASTClass)n);
      }
    }
    return target();
  }

  @Override
  public void visit(Dereference e) {
    result=create.dereference(e.object.apply(this),e.field);
  }
  
  @Override
  public void visit(BindingExpression e){
    result=create.binder(e.binder,rewrite(e.result_type),rewrite(e.getDeclarations()), rewrite(e.select), rewrite(e.main));
  }
  
  @Override
  public void visit(Lemma l){
    result=create.lemma(rewrite(l.block));
  }
  
  @Override
  public void visit(ParallelBlock pb){
    result=create.parallel_block(rewrite(pb.contract),rewrite(pb.decl),rewrite(pb.count),rewrite(pb.block));
  }
  
  @Override
  public void visit(ParallelBarrier pb){
    result=create.barrier(rewrite(pb.contract),pb.fences);
  }

  @Override
  public void visit(ASTSpecial special) {
    result=create.special(special.kind,rewrite(special.args));
  }
  
  @Override
  public void visit(VariableDeclaration decl) {
    VariableDeclaration res=create.variable_decl(decl.basetype);
    for(DeclarationStatement d:decl.get()){
      res.add(rewrite(d));
    }
    result=res;
  }

}
