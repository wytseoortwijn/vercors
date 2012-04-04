// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

import vct.col.rewrite.AbstractRewriter;

/**
 * This AST node stores method invokations on objects.
 * A function call is seen as invoking a static method on a class. 
 * 
 * @author sccblom
 *
 */
public class MethodInvokation extends ASTNode {

  public final ASTNode object;
  public final NameExpression method;
  private ASTNode args[];
  public final boolean guarded;
  
  public MethodInvokation(ASTNode object,NameExpression method,ASTNode ... args){
    this.object=object;
    this.method=method;
    this.args=Arrays.copyOf(args,args.length);
    guarded=false;
  }
  
  public MethodInvokation(ASTNode object,boolean guarded,NameExpression method,ASTNode ... args){
    this.object=object;
    this.method=method;
    this.args=Arrays.copyOf(args,args.length);
    this.guarded=guarded;
  }

  public void accept_simple(ASTVisitor visitor){
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
    
}

