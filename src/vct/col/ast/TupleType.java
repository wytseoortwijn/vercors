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
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}
