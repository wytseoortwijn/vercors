// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

/**
  Simple class that wraps a StandardOperator as an ASTNode.
  Included in the design to support a future extension into functional languages:
  
  OperatorExpression(op,args) == ApplyExpression(StandardProcedure(op),args)

 */

public class StandardProcedure extends ASTNode {

  public final StandardOperator op;

  public StandardProcedure(StandardOperator op){
    this.op=op;
  }
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public StandardOperator getOperator(){
    return op;
  }
  
}

