// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

import vct.util.ClassName;

public class DeclarationStatement extends ASTDeclaration {

  // Type should become part of ASTNode!!
  private Type type;
  private ASTNode expr;

  public DeclarationStatement(String name,Type type){
    super(name);
    this.type=type;
    expr=null;
  }

  public DeclarationStatement(String name,Type type,ASTNode expr){
    super(name);
    this.type=type;
    this.expr=expr;
  }
  
  public Type getType() { return type; }

  public String getName() { return name; }
  
  public ASTNode getInit() { return expr; }
  
  @Override
  public ClassName getDeclName() {
    hre.System.Warning("%s.%s",package_name,name);
    return new ClassName(package_name,name);
  }

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

}

