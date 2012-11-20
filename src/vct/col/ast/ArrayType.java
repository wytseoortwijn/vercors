package vct.col.ast;

public class ArrayType extends Type {

  public final int dim;
  public final Type base_type;
  
  public ArrayType(Type base,int dim){
    this.base_type=base;
    this.dim=dim;
  }
  
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }

  @Override
  public boolean supertypeof(ProgramUnit context, Type t) {
    // TODO Auto-generated method stub
    return false;
  }

}
