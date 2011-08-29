// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class DeclarationStatement extends ASTNode {

  // Type should become part of ASTNode!!
  private Type type;
  private String name;
  private ASTNode expr;

  public DeclarationStatement(String name,Type type){
    this.name=name;
    this.type=type;
    expr=null;
  }

  public DeclarationStatement(String name,Type type,ASTNode expr){
    this.name=name;
    this.type=type;
    this.expr=expr;
  }
  
  public Type getType() { return type; }

  public String getName() { return name; }
  
  public ASTNode getInit() { return expr; }
  
  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

}

