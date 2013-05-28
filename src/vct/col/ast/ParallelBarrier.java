package vct.col.ast;

public class ParallelBarrier extends ASTNode {

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

  public static Contract contract;
  
  public ParallelBarrier(Contract contract){
    this.contract=contract;
  }

}
