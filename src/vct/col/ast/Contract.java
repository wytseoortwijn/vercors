// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

public class Contract {
  public final ASTNode pre_condition;
  public final ASTNode post_condition;
  public final ASTNode modifies[];
  
  public final int modifiers;
  public Contract(ASTNode pre_condition,ASTNode post_condition){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    this.modifiers=0;
    modifies=null;
  }

  public Contract(ASTNode pre_condition,ASTNode post_condition,int modifiers){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    this.modifiers=modifiers;
    modifies=null;
  }
  
  public Contract(ASTNode modifies[],ASTNode pre_condition,ASTNode post_condition,
      int modifiers
    ){
      this. pre_condition= pre_condition;
      this.post_condition=post_condition;
      this.modifiers=modifiers;
      this.modifies=modifies;
    }
  
}

