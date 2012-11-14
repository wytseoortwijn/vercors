package vct.col.ast;

public class Dereference extends ASTNode {

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

  public final ASTNode object;
  public final String field;
  
  public Dereference(ASTNode object,String field){
    this.object=object;
    this.field=field;
  }

}
