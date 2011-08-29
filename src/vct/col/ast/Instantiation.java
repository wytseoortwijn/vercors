// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

/**
 * Instantiation expression should probably be a special case of apply.
 * 
 * @author sccblom
 *
 */
public class Instantiation extends ASTNode {

  private ASTNode sort;
  private ASTNode args[];

  public Instantiation(ASTNode sort,ASTNode ... args){
    this.sort=sort;
    this.args=Arrays.copyOf(args,args.length);
  }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public ASTNode getSort() { return sort; }
    
  public int getArity() { return args.length; }
  
  public ASTNode getArg(int i){ return args[i]; }

}

