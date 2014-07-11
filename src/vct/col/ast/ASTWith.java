package vct.col.ast;

import java.util.Arrays;


public class ASTWith extends ASTNode {

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
  
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

  public String fromString() {
    String res=from[0];
    for(int i=1;i<from.length;i++) res+="."+from[i];
    if (all) res+=".*";
    return res;
  }
 
}
