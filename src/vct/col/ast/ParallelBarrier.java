package vct.col.ast;

import java.util.EnumSet;

public class ParallelBarrier extends ASTNode {

  public enum Fence {
    /** fence global memory */
    Global,
    /** fence work group memory */
    Local
  }

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

  public final Contract contract;
  
  public final EnumSet<Fence> fences;
  
  public ParallelBarrier(Contract contract, EnumSet<Fence> fences){
    this.contract=contract;
    this.fences=EnumSet.copyOf(fences);
  }

}
