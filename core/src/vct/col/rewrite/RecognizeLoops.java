package vct.col.rewrite;

import vct.col.ast.*;

public class RecognizeLoops extends AbstractRewriter {

  public RecognizeLoops(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(LoopStatement loop){
    ASTNode tmp=loop.getInitBlock();
    if (tmp instanceof BlockStatement){
      BlockStatement block=(BlockStatement)tmp;
      if (block.getLength()==1){
        tmp=block.get(0);
      }
    }
    if (tmp instanceof DeclarationStatement) {
      Debug("declaration found");
      DeclarationStatement decl=(DeclarationStatement)tmp;
      tmp=loop.getUpdateBlock();
      if (tmp instanceof BlockStatement){
        BlockStatement block=(BlockStatement)tmp;
        if (block.getLength()==1){
          tmp=block.get(0);
        }
      }
      if (tmp.isa(StandardOperator.PostIncr)||tmp.isa(StandardOperator.PreIncr)){
        Debug("increment found");
        tmp=((OperatorExpression)tmp).getArg(0);
        if (tmp.isName(decl.name)){
          Debug("match");
          result=create.foreach(
              new DeclarationStatement[]{create.field_decl(decl.name,rewrite(decl.getType()))},
              create.expression(StandardOperator.And,
                  create.expression(StandardOperator.LTE,rewrite(decl.getInit()),create.local_name(decl.name)),
                  rewrite(loop.getEntryGuard())
              ),
              rewrite(loop.getBody())).setContract(rewrite(loop.getContract()));
          return;
        }
      }
    }
    super.visit(loop);
  }


}
