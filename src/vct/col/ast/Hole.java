package vct.col.ast;

public class Hole extends ASTNode {

  private ThreadLocal<ASTNode> match=new ThreadLocal<ASTNode>();
  
  
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
 
 
  public ASTNode get(){
    return match.get();
  }

  public boolean match(ASTNode n){
    match.set(n);
    return true;
  }
}
