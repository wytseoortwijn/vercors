// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;
import static hre.System.*;

/**
 * This AST node stores method invokations on objects.
 * A function call is seen as invoking a static method on a class. 
 * 
 * @author sccblom
 *
 */
public class MethodInvokation extends ASTNode {

  public final ASTNode object;
  public final String method;
  private Method definition;
  private ASTNode args[];
  public final boolean guarded;
  
  public MethodInvokation(ASTNode object,String method,ASTNode ... args){
    this.object=object;
    this.method=method;
    this.args=Arrays.copyOf(args,args.length);
    guarded=false;
  }
  
  public MethodInvokation(ASTNode object,boolean guarded,String method,ASTNode ... args){
    this.object=object;
    this.method=method;
    this.args=Arrays.copyOf(args,args.length);
    this.guarded=guarded;
  }

  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }

  public int getArity() { return args.length; }
    
  public ASTNode getArg(int i){ return args[i]; }

  /**
   * Collect the results of visiting the arguments.
   * @param visitor The visitor which must be accepted by the arguments.
   * @param template Any array of the correct type.
   * @return Array of results of visiting the arguments.
   */
  public <E> E[] map_args(ASTVisitor<E> visitor,E[] template) {
    int N=args.length;
    E res[]=Arrays.copyOf(template,N);
    for(int i=0;i<N;i++){
      args[i].accept(visitor);
      res[i]=visitor.getResult();
    }
    return res;
  }

  public ASTNode[] getArgs() {
    return Arrays.copyOf(args,args.length);
  }
  
  public void setDefinition(Method m){
    definition=m;
  }
  public Method getDefinition(){
    return definition;
  }

  /**
   * Check if this invokation is an instantiation.
   */
  public boolean isInstantiation() {
    if (definition==null){
      Abort("invokation of unknown method");
    }
    return definition.kind==Method.Kind.Constructor;
  }

  /** Block of proof hints to be executed just before
   *  evaluating the expression represented by this AST node.
   *  But after any argument has been evaluated.
   */
  private BlockStatement before;
  /** Block of proof hints to be executed after the
   *  current node has been evaluated.
   */
  private BlockStatement after;
  public void set_before(BlockStatement block){
    before=block;
  }
  public BlockStatement get_before(){
    return before;
  }
  public void set_after(BlockStatement block){
    after=block;
  }
  public BlockStatement get_after(){
    return after;
  }

}

