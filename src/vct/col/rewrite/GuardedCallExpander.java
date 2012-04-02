package vct.col.rewrite;

import hre.ast.MessageOrigin;
import vct.col.ast.ASTNode;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;

public class GuardedCallExpander extends AbstractRewriter {

  public void visit(MethodInvokation e) {
    if (!e.guarded) {
      super.visit(e);    
    } else {
      ASTNode object=e.object.apply(this);
      NameExpression method=rewrite_and_cast(e.method);
      int N=e.getArity();
      ASTNode args[]=new ASTNode[N];
      for(int i=0;i<N;i++){
        args[i]=e.getArg(i);
      }
      ASTNode null_expression=create.reserved_name("null");
      null_expression.setType(object.getType());
      OperatorExpression guard=new OperatorExpression(StandardOperator.NEQ,object,null_expression);
      guard.setOrigin(e.getOrigin());
      
      ASTNode call=new MethodInvokation(object,method,args);
      call.setOrigin(e.getOrigin());
      
      result=new OperatorExpression(StandardOperator.Implies,guard,call);
      result.setOrigin(e.getOrigin());
    }
  }

}

