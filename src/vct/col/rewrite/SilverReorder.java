package vct.col.rewrite;

import vct.col.ast.*;

public class SilverReorder extends AbstractRewriter {

  public SilverReorder(ProgramUnit source) {
    super(source);
  }

  private BlockStatement main_block=null;
  
  @Override
  public void visit(IfStatement s){
    Warning("rewriting if");
    BlockStatement tmp=main_block;
    main_block=currentBlock;
    super.visit(s);
    main_block=tmp;
  }
  
  @Override
  public void visit(DeclarationStatement d){
    super.visit(d);
    if (main_block!=null){
      Warning("rewriting if: moving decl");
      main_block.prepend(result);
      result=null;
    }
  }
  
  @Override
  public void visit(ASTSpecialDeclaration s){
    switch(s.kind){
    case Comment:
      result=null;
      return;
    default:
      super.visit(s);
    }

  }
  
}
