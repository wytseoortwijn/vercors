package vct.silver;

import hre.HREError;
import hre.ast.Origin;
import vct.col.ast.*;
import viper.api.*;

public class SilverTypeMap<T> implements TypeMapping<T> {

  private SilverVerifier<Origin,?,T,?,?,?,?,?,?> create;
  
  public SilverTypeMap(SilverVerifier<Origin,?,T,?,?,?,?,?,?> backend){
    this.create=backend;
  }
  
  @Override
  public void pre_map(Type t) {
  }

  @Override
  public T post_map(Type t, T res) {
    return res;
  }

  @Override
  public T map(ClassType t) {
    if (t.getName().equals("Ref")){
      return create.Ref();
    } else {
      ASTNode args[]=t.getArgs();
      if (args.length==0){
        return create.domain_type(t.getName());
      }
      throw new HREError("cannot convert class type %s",t.getFullName()); 
    }
  }

  @Override
  public T map(FunctionType t) {
    throw new HREError("function types are not supported"); 
  }

  private T map(ASTNode n){
    if (n instanceof Type){
      return ((Type)n).apply(this);
    } else {
      throw new HREError("cannot type map %s",n.getClass());
    }
  }
  @Override
  public T map(PrimitiveType t) {
    switch(t.sort){
      case Integer:
        return create.Int();
      case Boolean:
        return create.Bool();
      case ZFraction:
      case Fraction:
        return create.Perm();
      case Sequence:
        return create.List(map(t.getArg(0)));
      case Set:
        return create.Set(map(t.getArg(0)));
      case Bag:
        return create.Bag(map(t.getArg(0)));
      case String:
        return create.List(create.Int());
      default:
        throw new HREError("primitive type %s unsupported",t.sort);
    }
  }

  @Override
  public T map(RecordType t) {
    throw new HREError("record types are not supported");
  }

  @Override
  public T map(TupleType t) {
    throw new HREError("tuple types are not supported");
  }

  @Override
  public T map(TypeExpression t) {
    throw new HREError("type expressions are not supported");
  }

}
