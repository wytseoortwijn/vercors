package vct.col.util;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTVisitor;
import vct.col.ast.AbstractScanner;

public class PostVisit extends AbstractScanner {

  ASTVisitor post;
  
  public PostVisit(ASTVisitor post){
    this.post=post;
  }
  @Override
  public void post_visit(ASTNode n) {
    n.accept(post);
    super.post_visit(n);
  }

  
}
