package vct.col.ast;

import java.util.Arrays;

public class TupleType extends Type {

  public final Type types[];
  
  public TupleType(Type ... t) {
    types=Arrays.copyOf(t,t.length);
  }

  @Override
  public boolean supertypeof(ProgramUnit context, Type t) {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }
  @Override
  public <T> T accept_simple(TypeMapping<T> map){
    return map.map(this);
  }

}
