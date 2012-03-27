package vct.col.rewrite;

import java.util.Stack;

import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.IfStatement;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static hre.System.Abort;

public class Flatten extends AbstractRewriter {

  /* TODO check for pure expression while copying! */
  private AbstractRewriter copy_pure=new AbstractRewriter(){};
  
  private Stack<BlockStatement> block_stack=new Stack<BlockStatement>();
  private BlockStatement current_block=null;
  private long counter=0;
  
  public void visit(BlockStatement s){
    int N=s.getLength();
    block_stack.push(current_block);
    current_block=create.block();
    visit_body(s);
    result=current_block;
    current_block=block_stack.pop();
  }
  
  public void visit(OperatorExpression e){
    if (e.getType()==null) Abort("untyped operator %s in clause at %s",e.getOperator(),e.getOrigin());
    switch(e.getOperator()){
    case PreIncr:
    case PreDecr:
    {
      StandardOperator op=e.getOperator()==StandardOperator.PreIncr?StandardOperator.Plus:StandardOperator.Minus;
      ASTNode arg=e.getArg(0);
      ASTNode arg_out=arg.apply(this);
      String name="__flatten_"+(++counter);
      current_block.add_statement(create.field_decl(name,e.getType(),null));
      current_block.add_statement(create.assignment(arg_out,create.expression(op,arg_out,create.constant(1))));
      current_block.add_statement(create.assignment(create.local_name(name),arg_out));
      result=create.local_name(name);
      return;
    }
    case PostIncr:
    case PostDecr:
    {
      StandardOperator op=e.getOperator()==StandardOperator.PostIncr?StandardOperator.Plus:StandardOperator.Minus;
      ASTNode arg=e.getArg(0);
      ASTNode arg_out=arg.apply(this);
      String name="__flatten_"+(++counter);
      current_block.add_statement(create.field_decl(name,e.getType(),null));
      current_block.add_statement(create.assignment(create.local_name(name),arg_out));
      current_block.add_statement(create.assignment(arg_out,create.expression(op,arg_out,create.constant(1))));
      result=create.local_name(name);
      return;
    }
    case Assert:
    case Fold:
    case HoareCut:
    case Unfold:
    {
      result=e.apply(copy_pure);
      return;      
    }
    default:
      super.visit(e);
      return;
    }
  }
  
  public void visit(DeclarationStatement s){
    Type t=s.getType();
    ASTNode tmp=t.apply(this);
    if (tmp instanceof Type){
      t=(Type)tmp;
    } else {
      throw new Error("type AST rewrote to non-type AST");
    }
    String name=s.getName();
    ASTNode init=s.getInit();
    if (init!=null) {
      current_block.add_statement(create.field_decl(name,t,null));
      init=init.apply(this);
      result=create.assignment(create.local_name(name),init);
    } else {
      result=create.field_decl(name,t,null);
    }
  }
  
  private void visit_body(ASTNode body){
    if (body instanceof BlockStatement){
      BlockStatement s=(BlockStatement)body;
      int N=s.getLength();
      for(int i=0;i<N;i++){
        visit_body(s.getStatement(i));
      }
    } else {
      current_block.add_statement(body.apply(this));
    }
  }
  
  public void visit(IfStatement s) {
    IfStatement res=new IfStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getCount();
    for(int i=0;i<N;i++){
      ASTNode guard=s.getGuard(i);
      if (guard!=IfStatement.else_guard) guard=guard.apply(copy_pure);
      block_stack.push(current_block);
      current_block=create.block();
      visit_body(s.getStatement(i));
      res.addClause(guard,current_block);
      current_block=block_stack.pop();
    }
    result=res; return ;
  }
  
  
}
