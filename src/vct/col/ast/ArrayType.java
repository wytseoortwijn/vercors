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

  @Override
  public boolean comparableWith(Type t){
    if (t instanceof ArrayType){
      return dim == (((ArrayType)t).dim) && base_type.comparableWith(((ArrayType)t).base_type);
    }
    return t.isNull();
  }
  
  @Override
  public String toString(){
    String res=base_type.toString();
    for(int i=0;i<dim;i++) res=res+"[]";
    return res;
  }
}
