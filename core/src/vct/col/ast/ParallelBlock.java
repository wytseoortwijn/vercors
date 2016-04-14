package vct.col.ast;

import java.util.Arrays;

public class ParallelBlock extends ASTNode {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
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
 
  public final String label;
  public final Contract contract;
  public final DeclarationStatement iters[];
  public final BlockStatement block; 
  
  public ParallelBlock(
      String label,
      Contract contract,
      DeclarationStatement iters[],
      BlockStatement block)
  {
    this.label=label;
    this.contract=contract;
    this.iters=Arrays.copyOf(iters,iters.length);
    this.block=block;
  }

}
