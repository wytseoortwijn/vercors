package vct.col.ast;

import java.util.Arrays;


public class ASTWith extends ASTNode {

  @Override
  public <R,A> R accept_simple(ASTMapping1<R,A> map,A arg){
    return map.map(this,arg);
  }

  public static enum Kind{Static,Classes};
  public final String from[];
  public final Kind kind;
  public final boolean all;
  public final ASTNode body;
  
  public ASTWith(String from[],Kind kind,boolean all,ASTNode body){
    this.from=Arrays.copyOf(from,from.length);
    this.kind=kind;
    this.all=all;
    this.body=body;
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
 

  public String fromString() {
    String res=from[0];
    for(int i=1;i<from.length;i++) res+="."+from[i];
    if (all) res+=".*";
    return res;
  }
 
}
