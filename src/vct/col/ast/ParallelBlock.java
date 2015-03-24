package vct.col.ast;

import java.util.Arrays;

public class ParallelBlock extends ExpressionNode {

  public enum Mode {
    /** batch mode execution means that the scheduler is not obliged to run all threads at once. */
    Batch,
    /** asynchronous mode execution means that all tasks run at once with no restrictions. */
    Async,
    /** synchronous mode execution means that all tasks run at once in lockstep. */
    Sync
  }

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
 
  public final Mode mode;
  public final Contract contract;
  public final DeclarationStatement iters[];
  public final DeclarationStatement decls[];
  public final BlockStatement block; 
  public final ASTNode inv;
  
  public ParallelBlock(
      Mode mode,
      Contract contract,
      DeclarationStatement iters[],
      DeclarationStatement decls[],
      ASTNode inv,
      BlockStatement block)
  {
    this.mode=mode;
    this.contract=contract;
    this.decls=Arrays.copyOf(decls,decls.length);
    this.iters=Arrays.copyOf(iters,iters.length);
    this.block=block;
    this.inv=inv;
  }

}
