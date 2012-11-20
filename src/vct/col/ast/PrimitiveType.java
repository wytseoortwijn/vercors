package vct.col.ast;

import static hre.System.Fail;

public final class PrimitiveType extends Type {
  public static enum Sort {Boolean,Byte,Short,Integer,Long,Float,Double,Char,Fraction,Void, String,Class};
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
  public boolean isDouble() {
    return sort==Sort.Double;
  }
  public boolean isInteger() {
    return sort==Sort.Integer;
  }
  public boolean isVoid() {
    return sort==Sort.Void;
  }

  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }

  public String toString(){
    return sort.toString();
  }
  
  public boolean supertypeof(ProgramUnit context, Type t){
    if (t instanceof PrimitiveType){
      PrimitiveType pt=(PrimitiveType)t;
      if (this.sort==pt.sort) return true;
      switch(this.sort){
      case Fraction:
        switch(pt.sort){
        case Integer:
        case Short:
        case Byte:
          return true;
        }
        break;
      case Integer:
        switch(pt.sort){
        case Short:
        case Byte:
          return true;
        }        
        break;
      case Long:
        switch(pt.sort){
        case Integer:
        case Short:
        case Byte:
          return true;
        }        
        break;
      default:
        Fail("missing case in PrimitiveType.supertypeof (%s/%s)",this.sort,pt.sort);
      }
    }
    return false;
  }
  
  public boolean isPrimitive(Sort sort) {
    return this.sort==sort;
  }

  public ASTNode zero(){
    switch(sort){
    case Boolean:
      return new ConstantExpression(false);
    case Integer:
      return new ConstantExpression(0);
    case Long:
      return new ConstantExpression((long)0);
    case Double:
      return new ConstantExpression((double)0);
    default:
      return super.zero();
    }
  }
}
