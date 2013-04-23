package vct.col.util;

import java.util.EnumSet;
import java.util.ArrayList;

import vct.col.ast.ASTNode;
import vct.col.ast.BooleanValue;
import vct.col.ast.ConstantExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;

public class ASTUtils {

  public static Iterable<ASTNode> conjuncts(ASTNode e){
    ArrayList<ASTNode> res=new ArrayList<ASTNode>();
    EnumSet<StandardOperator> ops=EnumSet.of(StandardOperator.And,StandardOperator.Star);
    scan_ops(res,ops,e);
    return res;
  }

  private static void scan_ops(ArrayList<ASTNode> res, EnumSet<StandardOperator> ops,ASTNode n) {
    if (n instanceof OperatorExpression){
      OperatorExpression e=(OperatorExpression)n;
      if (ops.contains(e.getOperator())) {
        int N=e.getOperator().arity();
        for (int i=0;i<N;i++){
          scan_ops(res,ops,e.getArg(i));
        }
      } else {
        res.add(e);
      }
    } else {
      if (n instanceof ConstantExpression){
        ConstantExpression ce=(ConstantExpression)n;
        if (ce.value instanceof BooleanValue && ((BooleanValue)ce.value).value){
          // skip true.
          return;
        }
      }
      res.add(n); 
    }
  }
}
