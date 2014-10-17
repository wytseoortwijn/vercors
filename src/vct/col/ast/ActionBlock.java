package vct.col.ast;

public class ActionBlock extends ASTNode {

  public final ASTNode process;
  public final ASTNode action;
  public final ASTNode block;
  
  public ActionBlock(ASTNode process,ASTNode action,ASTNode block){
    this.process=process;
    this.action=action;
    this.block=block;
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
 

}
