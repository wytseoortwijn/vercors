package vct.col.ast;

public class Dereference extends ASTNode {

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

  public final ASTNode object;
  public final String field;
  
  public Dereference(ASTNode object,String field){
    this.object=object;
    this.field=field;
  }

}
