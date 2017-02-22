package vct.col.ast;

import static hre.lang.System.Abort;
import static hre.lang.System.Fail;

public final class PrimitiveType extends Type {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
  }

  public final PrimitiveSort sort;
  public PrimitiveType(PrimitiveSort sort,ASTNode ... args){
    super(args);
    int N=args.length;
    switch(sort){
      case Sequence:
      case Set:
      case Bag:
      case Cell:
      case Pointer:
      case Location:
      case Option:
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
      if (getArgCount() != t.getArgCount()) return false;
      for (int i = 0; i < getArgCount(); i++){
        if (!getArg(i).equals(t.getArg(i))) return false;
      }
      return true;
    } else if (o instanceof PrimitiveSort) {
      if (getArgCount() > 0) return false;
      return o==sort;
    } else {
      return false;
    }
  }
  
  public boolean isBoolean() {
    return sort==PrimitiveSort.Boolean;
  }
  public boolean isResource() {
    return sort==PrimitiveSort.Resource || sort==PrimitiveSort.Boolean;
  }
  public boolean isDouble() {
    return sort==PrimitiveSort.Double;
  }
  public boolean isInteger() {
    return sort==PrimitiveSort.Integer;
  }
  public boolean isVoid() {
    return sort==PrimitiveSort.Void;
  }

  
  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    try {
      visitor.visit(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
     }
      throw t;
    }
  }
  
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    try {
      return map.map(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
    }
      throw t;
    }
  }
 
  @Override
  public <T> T accept_simple(TypeMapping<T> map){
    try {
      return map.map(this);
    } catch (Throwable t){
      if (thrown.get()!=t){
        System.err.printf("Triggered by %s:%n",getOrigin());
        thrown.set(t);
     }
      throw t;
    }
  }

  public String toString(){
    String res=sort.toString();
    if (getArgCount() > 0) {
      res+="<";
      res+=getArg(0);
      for(int i = 1; i < getArgCount(); i++) {
        res+=","+getArg(i);
      }
      res+=">";
    }
    return res;
  }
  
  @SuppressWarnings("incomplete-switch")
  public boolean supertypeof(ProgramUnit context, Type t){
    
    switch(this.sort){
    case Option:
    case CVarArgs:
      return true;
    case Array:
      if (t.isPrimitive(this.sort)){
        return getArg(0).equals(((PrimitiveType)t).getArg(0));
      }
    case Sequence:
    case Cell:
      if (t instanceof ClassType) {
        ClassType ct=(ClassType)t;
        String name[]=ct.getNameFull();
        if (name.length==1 && name[0].equals("<<null>>")) return true;
      }
    }
    if (t instanceof PrimitiveType){
      PrimitiveType pt=(PrimitiveType)t;
      //Warning("testing (%s/%s)",this.sort,pt.sort);
      if (equals(t)) return true;
      switch(this.sort){
      case Void:
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
      case Char:
        break;
      case Double:
        break;
      case Pointer:
        if (t.isPrimitive(PrimitiveSort.String)){
          Type tt=((Type)getArg(0));
          if (tt.isPrimitive(PrimitiveSort.Char)) return true;
          if (tt instanceof TypeExpression){
            TypeExpression te=(TypeExpression)tt;
            if (te.operator() == TypeOperator.Const && te.firstType().isPrimitive(PrimitiveSort.Char)) return true;
          }
          Fail("missing case in PrimitiveType.supertypeof (%s/%s)",this.sort,pt.sort);
        }
        break;
      default:
        Fail("missing case in PrimitiveType.supertypeof (%s/%s)",this.sort,pt.sort);
      }
    }
    return false;
  }
  
  @Override
  public boolean isPrimitive(PrimitiveSort sort) {
    if(sort==PrimitiveSort.String && this.sort==PrimitiveSort.Pointer && ((Type)getArg(0)).isPrimitive(PrimitiveSort.Char)) return true;
    return this.sort==sort;
  }

  public ASTNode zero(){
    switch(sort){
    case Array:
      return new NameExpression(ASTReserved.Null);
    case Boolean:
    case Resource:
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
    case Set:
    case Bag:
      return new StructValue(this,null);
    case Option:
      return new NameExpression(ASTReserved.OptionNone);
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
    return isIntegerType() || isFloatType() || sort==PrimitiveSort.Fraction || sort==PrimitiveSort.ZFraction ;
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
