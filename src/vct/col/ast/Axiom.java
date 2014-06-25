package vct.col.ast;

import java.util.ArrayList;

import vct.util.ClassName;

public class Axiom extends ASTDeclaration {
  
  private ASTNode rule;
  
  public Axiom(String name, ASTNode exp) {
    super(name);
    rule=exp;
  }

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }

  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

  @Override
  public ClassName getDeclName() {
    return new ClassName(name);
  }

  public ASTNode getRule(){
    return rule;
  }
}
