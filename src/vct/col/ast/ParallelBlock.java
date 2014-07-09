package vct.col.ast;

public class ParallelBlock extends ASTNode {

  
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
  public final DeclarationStatement decl;
  public final ASTNode count;
  public final BlockStatement block; 
  
  public ParallelBlock(Contract contract,DeclarationStatement decl,ASTNode count,BlockStatement block){
    this.contract=contract;
    this.decl=decl;
    this.count=count;
    this.block=block;
  }

}
