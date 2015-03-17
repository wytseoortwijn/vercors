package vct.col.ast;

import java.util.EnumSet;

public class ParallelBarrier extends ASTNode {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
  }

  public enum Fence {
    /** fence global memory */
    Global,
    /** fence work group memory */
    Local
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
 

  public final Contract contract;
  
  public final EnumSet<Fence> fences;
  
  public final BlockStatement body;
  
  public ParallelBarrier(Contract contract, EnumSet<Fence> fences, BlockStatement body){
    this.contract=contract;
    this.fences=EnumSet.copyOf(fences);
    this.body=body;
  }

}
