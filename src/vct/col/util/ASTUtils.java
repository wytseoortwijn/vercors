package vct.col.util;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

import vct.col.ast.ASTNode;
import vct.col.ast.OperatorExpression;
import vct.col.ast.StandardOperator;

public class ASTUtils {

  public static Set<ASTNode> conjuncts(ASTNode e){
    HashSet<ASTNode> res=new HashSet<ASTNode>();
    EnumSet<StandardOperator> ops=EnumSet.of(StandardOperator.And,StandardOperator.Star);
    scan_ops(res,ops,e);
    return res;
  }

  private static void scan_ops(HashSet<ASTNode> res, EnumSet<StandardOperator> ops,ASTNode n) {
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
      res.add(n); 
    }
  }
}
