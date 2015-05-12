package vct.col.rewrite;

import vct.col.ast.*;
import vct.col.ast.ASTSpecial.Kind;
import static vct.col.ast.ASTSpecial.Kind.*;

public class FilterSpecIgnore extends AbstractRewriter {

  public FilterSpecIgnore(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(BlockStatement block){
    BlockStatement res=create.block();
    int level=0;
    for(ASTNode S:block){
      if (level==0){
        if(S.isSpecial(SpecIgnoreEnd)){
          Fail("specification ignore end without begin");
        } else if (S.isSpecial(SpecIgnoreStart)){
          level++;
        } else {
          res.add(rewrite(S));
        }
      } else {
        if(S.isSpecial(SpecIgnoreEnd)){
          level--;
        } else if (S.isSpecial(SpecIgnoreStart)){
          level++;
        } 
      }
    }
    if (level!=0){
      Fail("specification ignore begin without end");
    }
    result=res;
  }

}
