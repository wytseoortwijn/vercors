package vct.col.ast;

import java.util.Stack;
import java.util.concurrent.atomic.AtomicReference;

import static hre.System.Debug;

/**
 * Utility class that provides common functionality for exploring abstract syntax trees.
 * 
 * @author sccblom
 *
 */
public abstract class ASTFrame<T> {
  
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
  }
  
  /**
   * Stack of current nodes.
   */
  private Stack<ASTNode> node_stack;
  
  /**
   * Stack of current classes.
   */
  private Stack<ASTClass> class_stack;
  
  /**
   * Stack of current methods.
   */
  private Stack<Method> method_stack;
  

  public void enter(ASTNode node){
    node_stack.push(node);
    Debug("entering %s",node.getClass());
    if (node instanceof ASTClass){
      ASTClass cl=(ASTClass)node;
      class_stack.push(cl); 
    }
    if (node instanceof Method){
      method_stack.push((Method)node);
    }
    result_stack.push(result);
    result=null;
  }
  public void leave(ASTNode node){
    if (node instanceof ASTClass){
      class_stack.pop(); 
    }
    if (node instanceof Method){
      method_stack.pop();
    }
    result_ref.set(result);
    result=result_stack.pop();
    Debug("leaving %s",node.getClass());
    node_stack.pop();
  }

  public ASTNode current_node(){
    return node_stack.peek();
  }

  public ASTClass current_class(){
    return class_stack.peek();
  }
  
  public Method current_method(){
    if (method_stack.isEmpty()) {
      return null;
    } else {
      return method_stack.peek();
    }
  }
  
  public void Abort(String format,Object ...args){
    hre.System.Abort("At "+current_node().getOrigin()+": "+format,args);
  }
  public void Debug(String format,Object ...args){
    hre.System.Debug("At "+current_node().getOrigin()+": "+format,args);
  }
  public void Fail(String format,Object ...args){
    hre.System.Fail("At "+current_node().getOrigin()+": "+format,args);
  }
  public void Warning(String format,Object ...args){
    hre.System.Warning("At "+current_node().getOrigin()+": "+format,args);
  }

}
