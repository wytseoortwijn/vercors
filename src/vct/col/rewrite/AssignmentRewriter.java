package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import static hre.System.Debug;

/**
 * This rewriter changes assignment expressions to assignment statements.
 * 
 * @author Stefan Blom
 */ 
public class AssignmentRewriter extends AbstractRewriter {

  public AssignmentRewriter(ProgramUnit source) {
    super(source);
  }

  public void visit(BlockStatement s) {
    Debug("rewriting block");
    BlockStatement res=new BlockStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getLength();
    for (int i=0;i<N;i++){
      ASTNode statement=s.getStatement(i);
      if (statement instanceof OperatorExpression) {
        OperatorExpression e=(OperatorExpression)statement;
        switch(e.getOperator()){
        case Assign:
        {
          ASTNode var=e.getArg(0).apply(this);
          ASTNode val=e.getArg(1).apply(this);
          AssignmentStatement assignment=new AssignmentStatement(var,val);
          assignment.setOrigin(e.getOrigin());
          res.add_statement(assignment);
          break;
        }
        default:
          res.add_statement(statement.apply(this));
          break;
        }
      } else {
        res.add_statement(statement.apply(this));
      }
    }
    result=res;
  }

}
