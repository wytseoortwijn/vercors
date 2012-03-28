package vct.col.ast;

public final class PrimitiveType extends Type {
  public static enum Sort {Boolean,Byte,Short,Integer,Long,Float,Double,Char,Fraction,Void, String};
  public final Sort sort;
  public PrimitiveType(Sort sort){
    this.sort=sort;
  }
  public int hashCode(){
    return sort.hashCode();
  }
  public boolean equals(Object o){
    if (o instanceof PrimitiveType) {
      return sort==((PrimitiveType)o).sort;
    } else if (o instanceof Sort) {
      return o==sort;
    } else {
      return false;
    }
  }
  
  public boolean isBoolean() {
    return sort==Sort.Boolean;
  }
  public boolean isInteger() {
    return sort==Sort.Integer;
  }
  public boolean isDouble() {
    return sort==Sort.Double;
  }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public String toString(){
    return sort.toString();
  }
  
  public boolean supertypeof(Type t){
    if (t instanceof PrimitiveType){
      PrimitiveType pt=(PrimitiveType)t;
      switch(this.sort){
      case Fraction:
        switch(pt.sort){
        case Fraction:
        case Integer:
          return true;
        }
        break;
      case Integer:
        switch(pt.sort){
        case Integer:
        case Short:
        case Byte:
          return true;
        }        
        break;
      default:
        break;
      }
    }
    return false;
  }

}
