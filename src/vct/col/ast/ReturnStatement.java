// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class ReturnStatement extends ASTNode {

  private ASTNode expression;
  
  public ReturnStatement(){
    expression=null;
  }

  public ReturnStatement(ASTNode e){
    expression=e;
  }
  
  public ASTNode getExpression() { return expression; }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  /** Block of proof hints to be executed after callee returns and before caller resumes.
   */
  private BlockStatement after;
  public void set_after(BlockStatement block){
    after=block;
  }
  public BlockStatement get_after(){
    return after;
  }
}

