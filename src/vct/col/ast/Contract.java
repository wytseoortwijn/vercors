// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

public class Contract {
  public final ASTNode pre_condition;
  public final ASTNode post_condition;
  public final DeclarationStatement given[];
  public final DeclarationStatement yields[];
  public final int modifiers;
  public Contract(ASTNode pre_condition,ASTNode post_condition){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    this.modifiers=0;
    this.given=new DeclarationStatement[0];
    this.yields=new DeclarationStatement[0];
  }

  public Contract(ASTNode pre_condition,ASTNode post_condition,int modifiers){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    this.modifiers=modifiers;
    this.given=new DeclarationStatement[0];
    this.yields=new DeclarationStatement[0];
  }
  
  public Contract(ASTNode pre_condition,ASTNode post_condition,
    DeclarationStatement given[],DeclarationStatement yields[],int modifiers
  ){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    this.modifiers=modifiers;
    this.given=given;
    this.yields=yields;
  }
  
}

