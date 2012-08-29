package vct.col.util;

import javax.swing.JTable.PrintMode;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTWith;
import vct.col.ast.AbstractScanner;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.Type;

public class FeatureScanner extends AbstractScanner {

  private boolean has_statics=false;
  private boolean has_dynamics=false;
  private boolean has_doubles=false;
  private boolean has_longs=false;

  public boolean usesDoubles(){
    return has_doubles;
  }
  
  public boolean usesLongs(){
    return has_longs;
  }
  
  public boolean hasStaticItems(){
    return has_statics;
  }

  public boolean hasDynamicItems(){
    return has_dynamics;
  }

  public void pre_visit(ASTNode node){
    super.pre_visit(node);
    Type t=node.getType();
    if (t!=null){
      if (t.isDouble()) has_doubles=true;
      if (t.isPrimitive(Sort.Long)) has_longs=true;
    }
  }

  public void visit(ASTClass c) {
    int N=c.getStaticCount();
    for(int i=0;i<N;i++){
      ASTNode node=c.getStatic(i);
      if (!(node instanceof ASTClass)) {
        has_statics=true;
      }
      node.accept(this);
    }    
    N=c.getDynamicCount();
    if (N>0) has_statics=true;
    for(int i=0;i<N;i++){
      c.getDynamic(i).accept(this);
    }
  }
}
