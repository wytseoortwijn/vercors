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

}

