package vct.col.ast;

import static hre.System.Abort;
import static hre.System.Fail;
import static hre.System.Warning;

public final class PrimitiveType extends Type {
  public static enum Sort {
    Boolean,
    Byte,
    Short,
    Integer,
    Long,
    UByte,
    UShort,
    UInteger,
    ULong,
    Float,
    Double,
    Char,
    /** non-zero fraction */
    Fraction,
    /** possibly zero fraction */
    ZFraction,
    Void,
    String,
    Class,
    Resource,
    Cell,
    Sequence,
    Array};

  public final Sort sort;
  public PrimitiveType(Sort sort,ASTNode ... args){
    super(args);
    int N=args.length;
    switch(sort){
      case Sequence:
      case Cell:
        if (N!=1) Abort("illegal argument count");
        break;
      case Array:
        if (N<1 || N>2) Abort("illegal argument count");
        break;
      default:
        if (N!=0) Abort("illegal argument count");
    }
    this.sort=sort;
  }
  public int hashCode(){
    return sort.hashCode();
  }
  public boolean equals(Object o){
    if (o instanceof PrimitiveType) {
      PrimitiveType t=(PrimitiveType)o;
      if (sort!=t.sort) return false;
      if (args.length != t.args.length) return false;
      for(int i=0;i<args.length;i++){
        if (!args[i].equals(t.args[i])) return false;
      }
      return true;
    } else if (o instanceof Sort) {
      if (args.length>0) return false;
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
    String res=sort.toString();
    if (args.length>0){
      res+="<";
      res+=args[0];
      for(int i=1;i<args.length;i++){
        res+=","+args[i];
      }
      res+=">";
    }
    return res;
  }
  
  public boolean supertypeof(ProgramUnit context, Type t){
    switch(this.sort){
    case Sequence:
    case Array:
    case Cell:
      if (t instanceof ClassType) {
        ClassType ct=(ClassType)t;
        String name[]=ct.getNameFull();
        if (name.length==1 && name[0].equals("<<null>>")) return true;
      }
    }
    if (t instanceof PrimitiveType){
      PrimitiveType pt=(PrimitiveType)t;
      if (equals(t)) return true;
      switch(this.sort){
      case Sequence:
      case Array:
        return false;
      case ZFraction:
        switch(pt.sort){
        case Fraction:
        case Integer:
        case Short:
        case Byte:
          return true;
        }
        break;
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
      case UInteger:
        switch(pt.sort){
        case ULong:
        case UShort:
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
      case ULong:
        switch(pt.sort){
        case Long:
        case Integer:
        case Short:
        case Byte:
          return true;
        }
        break;
      case Float:
        switch(pt.sort){
        case Integer:
        case Short:
        case Byte:
          return true;
        }    
        break;
      case Boolean:
        break;
      case Resource:
        switch(pt.sort){
        case Boolean:
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
    case ZFraction:
      return new ConstantExpression(0);
    case Fraction:
      return new ConstantExpression(0);
    case Integer:
      return new ConstantExpression(0);
    case Long:
      return new ConstantExpression((long)0);
    case Double:
      return new ConstantExpression((double)0);
    case Sequence:
      return new OperatorExpression(StandardOperator.Nil,args[0]);
    default:
      return super.zero();
    }
  }
  public boolean equalSize(Type t2) {
    int tmp=size();
    if (tmp>0 && t2 instanceof PrimitiveType){
      return tmp==((PrimitiveType)t2).size();
    }
    return false;
  }
  private int size() {
    switch(sort){
      case Short:
      case UShort:
        return 16;
      case UInteger:
      case Integer:
        return 32;
      case Long:
      case ULong:
        return 64;
      default: return -1;
    }
    
  }
  
  public boolean isIntegerType() {
    return size()>0;
  }
  
  public boolean isNumeric() {
    return isIntegerType() || isFloatType() || sort==Sort.Fraction || sort==Sort.ZFraction ;
  }
  private boolean isFloatType() {
    switch(sort){
      case Float:
      case Double:
        return true;
      default:
        return false;
    }
  }


}
