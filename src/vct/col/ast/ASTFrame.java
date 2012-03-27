package vct.col.ast;

import java.util.Stack;
import static hre.System.Debug;

public abstract class ASTFrame {
  private Stack<ASTNode> node_stack;
  private Stack<ASTClass> class_stack;

  public ASTFrame(){
    node_stack=new Stack<ASTNode>();
    class_stack=new Stack<ASTClass>();
  }
  public ASTFrame(ASTFrame share){
    node_stack=share.node_stack;
    class_stack=share.class_stack;
  }
  
  public void enter(ASTNode node){
    node_stack.push(node);
    if (node instanceof ASTClass){
      ASTClass cl=(ASTClass)node;
      if (!cl.isPackage()){
        Debug("entering frame of class %s%n",cl.getName());
        class_stack.push(cl); 
      }
    }
  }
  public void leave(ASTNode node){
    node_stack.pop();
    if (node instanceof ASTClass){
      ASTClass cl=(ASTClass)node;
      if (!cl.isPackage()){
        Debug("leaving frame of class %s%n",cl.getName());
        class_stack.pop(); 
      }
    }
  }

  public ASTNode current_node(){
    return node_stack.peek();
  }

  public ASTNode current_class(){
    return class_stack.peek();
  }

}
