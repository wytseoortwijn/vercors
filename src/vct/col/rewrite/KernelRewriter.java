package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.ParallelBlock;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.util.ASTUtils;

public class KernelRewriter extends AbstractRewriter {

  private int kernel_no;
  
  public KernelRewriter(ProgramUnit source) {
    super(source);
  }
  
  public void visit(ParallelBlock pb){
    kernel_no++;
    String name="__auto_kernel_"+kernel_no;
    DeclarationStatement decl[]=rewrite(current_method().getArgs());
    ASTNode args[]=new ASTNode[decl.length];
    for(int i=0;i<decl.length;i++){
      args[i]=create.local_name(decl[i].getName());
    }
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.pre_condition)){
      if(clause.getType().isPrimitive(Sort.Resource)){
        if (clause.isa(StandardOperator.Perm)){
          
        } else {
          Fail("unsupported resource in kernel contract");
        }
      } else {
        cb.requires(create.forall(
            create.expression(StandardOperator.And,
                create.expression(StandardOperator.LTE,create.constant(0),create.local_name(pb.decl.getName())),
                create.expression(StandardOperator.LT,create.local_name(pb.decl.getName()),rewrite(pb.count))
            ),
            rewrite(clause),
            rewrite(pb.decl)
        ));        
      }
    }
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.post_condition)){
      cb.ensures(create.forall(
          create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name(pb.decl.getName())),
              create.expression(StandardOperator.LT,create.local_name(pb.decl.getName()),rewrite(pb.count))
          ),
          rewrite(clause),
          rewrite(pb.decl)
      ));
    }
    currentClass.add_dynamic(create.method_decl(
        create.primitive_type(Sort.Void),
        cb.getContract(),
        name,
        decl,
        null
    ));
    result=create.invokation(null,null,name,args);
  }

}
