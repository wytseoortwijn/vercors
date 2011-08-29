package vct.col.util;

import java.io.PrintStream;

import vct.col.ast.ASTNode;
import vct.col.ast.AbstractScanner;

public class XMLDump extends AbstractScanner {

  private PrintStream out;
  protected int depth=0;
  
  private void prefix(){
    for(int i=0;i<depth;i++) out.print("  ");
  }
  
  public XMLDump(PrintStream out){
    this.out=out;
  }
  public void pre_visit(ASTNode n) {
    super.pre_visit(n);
    prefix();
    out.printf("<%s>\n",n.getClass().getSimpleName());
    depth++;
  }

  /** Any overriding method should call this method last. 
   * 
   */
  @Override
  public void post_visit(ASTNode n) {
    depth--;
    prefix();
    out.printf("</%s>\n",n.getClass().getSimpleName());
    super.post_visit(n);
  }

}
