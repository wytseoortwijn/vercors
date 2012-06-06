// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.HashSet;

import vct.col.util.ASTUtils;

public class Contract {
  public final ASTNode pre_condition;
  public final ASTNode post_condition;
  public final ASTNode modifies[];
  
  private HashSet<String> labels=new HashSet<String>();
    
  public Contract(ASTNode pre_condition,ASTNode post_condition){
    this. pre_condition= pre_condition;
    this.post_condition=post_condition;
    modifies=null;
    build_labels();
  }
  
  public Contract(ASTNode modifies[],ASTNode pre_condition,ASTNode post_condition){
      this. pre_condition= pre_condition;
      this.post_condition=post_condition;
      this.modifies=modifies;
      build_labels();
    }

  public void build_labels(){
    for(ASTNode part:ASTUtils.conjuncts(pre_condition)){
      for(NameExpression lbl:part.getLabels()){
        labels.add(lbl.getName());
      }
    }
    for(ASTNode part:ASTUtils.conjuncts(post_condition)){
      for(NameExpression lbl:part.getLabels()){
        labels.add(lbl.getName());
      }     
    }
  }
  public boolean hasLabel(String name) {
     return labels.contains(name);
  }
  
}

