package vct.col.ast;

import hre.util.SingleNameSpace;

import java.util.Stack;
import java.util.concurrent.atomic.AtomicReference;

import vct.col.ast.ASTSpecial.Kind;

import static hre.System.Debug;

/**
 * Utility class that provides common functionality for exploring abstract syntax trees.
 * 
 * @author Stefan Blom
 *
 */
public abstract class ASTFrame<T> {
  
  /**
   * Information record for variables.
   * 
   * @author Stefan Blom
   */
  public static class VariableInfo {
    
    /**
     * Reference to the place where the variable was defined.
     */
    public final ASTNode reference;
    
    /**
     * Stores the kind of the variable.
     */
    public final NameExpression.Kind kind;
    
    /**
     * Constructor for a variable info record.
     */
    public VariableInfo(ASTNode reference,NameExpression.Kind kind){
      this.reference=reference;
      this.kind=kind;
    }
  }
  
  public final SingleNameSpace<String,VariableInfo> variables;
  
  /**
   * Field for communicating return value.
   */
  protected T result;
  
  private AtomicReference<T> result_ref;
  
  private Stack<T> result_stack;
  
  public T getResult(){
    return result_ref.get();
  }

  /**
   * Holds the source program unit.
   */
  private ProgramUnit source;
  
  /**
   * Getter form the source program unit.
   * @return source program unit.
   */
  public ProgramUnit source(){
    return source;
  }
  
  /**
   * Holds the target program unit, or null.
   */
  private ProgramUnit target;
  
  /**
   * Getter form the target program unit.
   * @return target program unit.
   */
 public ProgramUnit target(){
    return target;
  }

  /**
   * Create a new frame with just a source program unit.
   * 
   * @param source
   */
  public ASTFrame(ProgramUnit source){
    this(source,null);
  }
  
  /**
   * Create a new frame with both source and target program units.
   * 
   * @param source
   */
  public ASTFrame(ProgramUnit source,ProgramUnit target){
    this.source=source;
    this.target=target;
    node_stack=new Stack<ASTNode>();
    class_stack=new Stack<ASTClass>();
    method_stack=new Stack<Method>();
    result_stack=new Stack<T>();
    result_ref=new AtomicReference<T>();
    variables=new SingleNameSpace<String,VariableInfo>();
  }
  
  /**
   * Create a shared frame.
   * 
   * @param share The frame with which to share information.
   */
  public ASTFrame(ASTFrame<T> share){
    node_stack=share.node_stack;
    class_stack=share.class_stack;
    method_stack=share.method_stack;
    source=share.source;
    target=share.target;
    result_stack=share.result_stack;
    result_ref=share.result_ref;
    variables=share.variables;
  }
  
  /**
   * Stack of current nodes.
   */
  private Stack<ASTNode> node_stack;
  
  /** */
  protected ASTNode getParentNode(){
    return node_stack.get(node_stack.size()-2);
  }

  /**
   * Stack of current classes.
   */
  private Stack<ASTClass> class_stack;
  
  /**
   * Stack of current methods.
   */
  private Stack<Method> method_stack;
  
  public void enter_before(ASTNode node){
    
  }
  public void leave_before(ASTNode node){
    
  }
  public void enter_after(ASTNode node){
    if (node instanceof MethodInvokation){
      MethodInvokation e=(MethodInvokation)node;
      method_stack.push(e.getDefinition());
    }
  }
  public void leave_after(ASTNode node){
    if (node instanceof MethodInvokation){
      MethodInvokation e=(MethodInvokation)node;
      method_stack.pop();
    }
  }

  public void enter(ASTNode node){
    node_stack.push(node);
    Debug("entering %s",node.getClass());
    if (node instanceof AxiomaticDataType){
      variables.enter();
      AxiomaticDataType adt=(AxiomaticDataType)node;
      for(DeclarationStatement decl:adt.getParameters()){
        Warning("ADT: adding %s",decl.getName());
        variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Argument));
      }
    }
    if (node instanceof ASTClass){
      ASTClass cl=(ASTClass)node;
      class_stack.push(cl);
      variables.enter();
      recursively_add_class_info(cl);
      Contract contract=cl.getContract();
      if (contract!=null){
        for (DeclarationStatement decl:contract.given){
          variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Field));
          //Warning("added %s",decl.getName());
        }
      }
    }
    if (node instanceof Method){
      Method m=(Method)node;
      method_stack.push(m);
      variables.enter();
      for(DeclarationStatement decl:m.getArgs()){
        variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Argument));
      }
      add_contract_vars(m);
    }
    if (node instanceof BlockStatement){
      variables.enter();
      if (node.getParent() instanceof MethodInvokation){
        MethodInvokation s=(MethodInvokation)node.getParent();
        Method def=s.getDefinition();
        //if (def==null) {
        //  Warning("definition of method invokation is unknown, expect type errors.");
        //}
        add_contract_vars(def);
      }
      BlockStatement block=(BlockStatement)node;
      int N=block.size();
      for(int i=0;i<N;i++){
        scan_labels(block.getStatement(i));
        //for(NameExpression name:block.getStatement(i).getLabels()){
        //  variables.add(name.getName(),new VariableInfo(node,NameExpression.Kind.Label));
        //}
      }
    }
    if (node instanceof DeclarationStatement){
      DeclarationStatement decl=(DeclarationStatement)node;
      if (decl.getParent() instanceof BlockStatement){
        variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Local));
      }
    }
    if (node instanceof OperatorExpression){
      OperatorExpression expr=(OperatorExpression)node;
      switch(expr.getOperator()){
        case Witness:{
          for(NameExpression name:expr.getArg(0).getLabels()){
            variables.add(name.getName(),new VariableInfo(node,NameExpression.Kind.Label));
          }
          break;
        }
        case Apply:{
          for(NameExpression name:expr.getLabels()){
            variables.add(name.getName(),new VariableInfo(node,NameExpression.Kind.Label));
          }
          break;          
        }
        case BindOutput:{
          ASTNode e=((OperatorExpression) node).getArg(0);
          if (e instanceof NameExpression){
            NameExpression name=(NameExpression) e;
            variables.add(name.getName(),new VariableInfo(node,NameExpression.Kind.Output));
          } else {
            Abort("unexpected output binder argument: %s",e.getClass());
          }
          break;
        }
      }
    }
    if (node instanceof MethodInvokation){
      for(NameExpression label:node.getLabels()){
        variables.add(label.getName(),new VariableInfo(node,NameExpression.Kind.Label));
      }
    }
    if (node instanceof LoopStatement){
      variables.enter();
      LoopStatement loop=(LoopStatement)node;
      for(ASTNode inv:loop.getInvariants()){
        scan_labels(inv);
      }
      if (loop.getInitBlock() instanceof DeclarationStatement){
        DeclarationStatement decl=(DeclarationStatement)loop.getInitBlock();
        variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Local));
      }
      if (loop.getInitBlock() instanceof BlockStatement){
        BlockStatement block=(BlockStatement)loop.getInitBlock();
        int N=block.getLength();
        for(int i=0;i<N;i++){
          if (block.getStatement(i) instanceof DeclarationStatement){
            DeclarationStatement decl=(DeclarationStatement)block.getStatement(i);
            variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Local));
          }         
        }
      }
    }
    if (node instanceof BindingExpression){
      variables.enter();
      for(DeclarationStatement decl:((BindingExpression)node).getDeclarations()){
        variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Local));
      }
    }
    if (node instanceof ParallelBlock){
      ParallelBlock pb=(ParallelBlock)node;
      variables.enter();
      variables.add(pb.decl.getName(),new VariableInfo(pb.decl,NameExpression.Kind.Local));
    }
    result_stack.push(result);
    result=null;
  }
  private void recursively_add_class_info(ASTClass cl) {
    switch(cl.super_classes.length){
      case 0:
        break;
      case 1:{
        if (source != null) {
          ASTClass super_class=source.find(cl.super_classes[0]);
          if (super_class!=null){
            recursively_add_class_info(super_class);
          }
        }
        break;
      }
      default:
        Fail("Multiple inheritance is not supported.");
        break;
    }
    for(DeclarationStatement decl:cl.dynamicFields()){
      variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Field));
    }
    for(DeclarationStatement decl:cl.staticFields()){
      variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Field));
    }
  }

  private void add_contract_vars(Method m) {
    if (m==null) return;
    Contract c=m.getContract();
    if (c==null) return;
    for(DeclarationStatement decl:c.given){
      variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Argument));
    }
    scan_labels(c.pre_condition);
    for(DeclarationStatement decl:c.yields){
      variables.add(decl.getName(),new VariableInfo(decl,NameExpression.Kind.Argument));
    }
    scan_labels(c.post_condition);
  }

  
  private void scan_labels(ASTNode node) {
    //if (node instanceof MethodInvokation){
      for(NameExpression label:node.getLabels()){
        variables.add(label.getName(),new VariableInfo(node,NameExpression.Kind.Label));
      }
      if (node instanceof ASTSpecial){
        ASTSpecial s=(ASTSpecial)node;
        if (s.kind==ASTSpecial.Kind.Label){
          NameExpression label=(NameExpression)s.args[0];
          variables.add(label.getName(),new VariableInfo(node,NameExpression.Kind.Label));
        }
      }
    //}
    if (node instanceof OperatorExpression){
      for(ASTNode arg:((OperatorExpression)node).getArguments()){
        scan_labels(arg);
      }
    }
  }

  public void leave(ASTNode node){
    if (node instanceof AxiomaticDataType){
      variables.leave();
    }
    if (node instanceof ASTClass){
      variables.leave();
      class_stack.pop(); 
    }
    if (node instanceof Method){
      method_stack.pop();
      variables.leave();
    }
    if (node instanceof BlockStatement){
      variables.leave();
    }
    if (node instanceof LoopStatement){
      variables.leave();
    }
    if (node instanceof BindingExpression){
      variables.leave();
    }
    if (node instanceof ParallelBlock){
      variables.leave();
    }
    result_ref.set(result);
    result=result_stack.pop();
    Debug("leaving %s",node.getClass());
    node_stack.pop();
  }

  public ASTNode current_node(){
    if (node_stack.isEmpty()) {
      return null;
    } else {
      return node_stack.peek();
    }
  }

  public ASTClass current_class(){
    if (class_stack.isEmpty()){
      return null;
    } else {
      return class_stack.peek();
    }
  }
  
  public Method current_method(){
    if (method_stack.isEmpty()) {
      return null;
    } else {
      return method_stack.peek();
    }
  }
  
  public void Abort(String format,Object ...args){
    hre.System.Abort("("+this.getClass()+")At "+current_node().getOrigin()+": "+format,args);
  }
  public void Debug(String format,Object ...args){
    ASTNode node=current_node();
    if (node!=null){
      hre.System.Debug("At "+node.getOrigin()+": "+format,args);
    } else {
      hre.System.Debug(format,args);
    }
  }
  public void Fail(String format,Object ...args){
    if (current_node()!=null){
      hre.System.Fail("At "+current_node().getOrigin()+": "+format,args);
    } else {
      hre.System.Fail(format,args);
    }
  }
  public void Warning(String format,Object ...args){
    if (current_node()!=null){
      hre.System.Warning("("+this.getClass()+"):%n  at "+current_node().getOrigin()+":%n    "+format,args);
    } else {
      hre.System.Warning("("+this.getClass()+"):%n  "+format,args);
    }
  }

}
