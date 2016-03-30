package vct.col.rewrite;

import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;

public class VerCorsDesugar extends AbstractRewriter {

  public VerCorsDesugar(ProgramUnit source) {
    super(source);
  }

  private AtomicInteger count=new AtomicInteger();
  
  @Override
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case Perm:{
      ArrayList<String> vars=new ArrayList();
      ArrayList<ASTNode> range=new ArrayList();
      ASTNode loc=desugar_loc(vars,range,e.getArg(0));
      ASTNode frac=rewrite(e.getArg(1));
      ASTNode res=create.expression(StandardOperator.Perm,loc,frac);
      int N=vars.size();
      for(int i=N-1;i>=0;i--){
        String name=vars.get(i);
        res=create.starall(
              create.expression(StandardOperator.Member,create.local_name(name),range.get(i)),
              res,
              create.field_decl(name, create.primitive_type(PrimitiveType.Sort.Integer)));
      }
      result=res;
      break;
    }
    default:
      super.visit(e);
      break;
    }
  }

  private ASTNode desugar_loc(ArrayList<String> vars, ArrayList<ASTNode> range, ASTNode loc) {
    if (loc.isa(StandardOperator.Subscript)){
      OperatorExpression e=(OperatorExpression)loc;
      ASTNode base=desugar_loc(vars,range,e.getArg(0));
      ASTNode idx=e.getArg(1);
      if (idx.isa(StandardOperator.RangeSeq)){
        String iter="idx_"+count.incrementAndGet();
        vars.add(iter);
        range.add(rewrite(idx));
        idx=create.local_name(iter);
      } else {
        idx=rewrite(idx);
      }
      return create.expression(StandardOperator.Subscript, base,idx);
    } else {
      return rewrite(loc);
    }
  }
}
