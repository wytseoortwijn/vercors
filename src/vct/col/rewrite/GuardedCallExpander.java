package vct.col.rewrite;

import hre.ast.MessageOrigin;
import vct.col.ast.ASTNode;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;

public class GuardedCallExpander extends AbstractRewriter {

  public GuardedCallExpander(ProgramUnit source) {
    super(source);
  }

  public void visit(MethodInvokation e) {
    if (!e.guarded) {
      super.visit(e);    
    } else {
      ASTNode object=e.object.apply(this);
      int N=e.getArity();
      ASTNode args[]=new ASTNode[N];
      for(int i=0;i<N;i++){
        args[i]=e.getArg(i);
      }
      ASTNode null_expression=create.reserved_name("null");
      null_expression.setType(object.getType());
      OperatorExpression guard=new OperatorExpression(StandardOperator.NEQ,object,null_expression);
      guard.setOrigin(e.getOrigin());
      
      ASTNode call=create.invokation(object,false,e.method,args);
      for(NameExpression lbl:e.getLabels()){
        call.addLabel(rewrite(lbl));
      }

      result=new OperatorExpression(StandardOperator.Implies,guard,call);
      result.setOrigin(e.getOrigin());
      auto_labels=false;
    }
  }

}

