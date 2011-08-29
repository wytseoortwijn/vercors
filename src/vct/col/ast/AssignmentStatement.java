// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.*;


public class AssignmentStatement extends ASTNode {

  private ASTNode expression;
  private ASTNode location;

  public AssignmentStatement(String name,ASTNode expression){
    location=new NameExpression(name);
    location.setOrigin(new MessageOrigin("parser bug: string location in assignment"));
    this.expression=expression;
  }

  public AssignmentStatement(ASTNode location,ASTNode expression){
    this.location=location;
    this.expression=expression;
  }

  public ASTNode getExpression() { return expression; }

//  public String getName() { return name; }

  public ASTNode getLocation() { return location; }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

}

