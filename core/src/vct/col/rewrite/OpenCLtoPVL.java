package vct.col.rewrite;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;

public class OpenCLtoPVL extends AbstractRewriter {

  public OpenCLtoPVL(ProgramUnit source) {
    super(source);
  }

  @Override
  public void visit(Method m){
    Type t=m.getReturnType();
    if (t instanceof TypeExpression){
      TypeExpression te=(TypeExpression)t;
      if (te.op == TypeOperator.Kernel){
        t=te.types[0];
        DeclarationStatement range=create.field_decl("opencl_iter",
            create.primitive_type(Sort.Integer),
            create.expression(StandardOperator.RangeSeq,create.constant(0),create.unresolved_name("NUM_TRHEADS")));
        ParallelBlock pblock=create.parallel_block("opencl_main", null ,new DeclarationStatement[]{ range },rewrite((BlockStatement)m.getBody()));
        result=create.method_decl(t,null, m.name, rewrite(m.getArgs()),create.block(pblock));
        return;
      }
    }
    super.visit(m);
  }
  
}
