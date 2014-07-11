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
  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

  public StandardOperator getOperator(){
    return op;
  }
  
}

