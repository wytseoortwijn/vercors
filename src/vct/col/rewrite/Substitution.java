package vct.col.rewrite;

import java.util.Map;

import vct.col.ast.ASTNode;
import vct.col.ast.NameExpression;

public class Substitution extends AbstractRewriter {
  Map<NameExpression,ASTNode> map;
  
  private AbstractRewriter copy_rw=new AbstractRewriter(){};
  
  public Substitution(Map<NameExpression,ASTNode> map){
   this.map=map;
  }
  
  public void visit(NameExpression e) {
    ASTNode res=map.get(e);
    if (res==null){
      super.visit(e);
    } else {
      result=res.apply(copy_rw);
    }
  }
}
