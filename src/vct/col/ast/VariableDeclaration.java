package vct.col.ast;

import java.util.ArrayList;

import vct.util.ClassName;

public class VariableDeclaration extends ASTNode {

  public final Type basetype;
  private ArrayList<DeclarationStatement> vars=new ArrayList<DeclarationStatement>();
  
  public VariableDeclaration(Type basetype){
    this.basetype=basetype;
  }
  
  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

  public void add(DeclarationStatement decl){
    vars.add(decl);
  }
  
  public Iterable<DeclarationStatement> get(){
    return vars;
  }
}
