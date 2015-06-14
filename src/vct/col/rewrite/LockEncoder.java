package vct.col.rewrite;

import vct.col.ast.ASTSpecial;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;

public class LockEncoder extends AbstractRewriter {

  private static String INV="lock_invariant";

  public LockEncoder(ProgramUnit source) {
    super(source);
  }
  
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Lock:
      currentBlock.add(create.special(ASTSpecial.Kind.Inhale,create.invokation(rewrite(s.args[0]),null,INV)));
      currentBlock.add(create.expression(StandardOperator.Unfold,create.invokation(rewrite(s.args[0]),null,INV)));
      result=null;
      break;
    case Unlock:
      currentBlock.add(create.expression(StandardOperator.Fold,create.invokation(rewrite(s.args[0]),null,INV)));
      currentBlock.add(create.special(ASTSpecial.Kind.Exhale,create.invokation(rewrite(s.args[0]),null,INV)));
      result=null;
      break;
    default:
      super.visit(s);
    }
  }


}
