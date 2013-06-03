package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
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
    String main_name="__auto_kernel_main_"+kernel_no;
    String thread_name="__auto_kernel_thread_"+kernel_no;
    DeclarationStatement decl[]=rewrite(current_method().getArgs());
    ASTNode args[]=new ASTNode[decl.length];
    for(int i=0;i<decl.length;i++){
      args[i]=create.local_name(decl[i].getName());
    }
    ContractBuilder main_cb=new ContractBuilder();
    ContractBuilder thread_cb=new ContractBuilder();
    thread_cb.requires(create.expression(StandardOperator.And,
        create.expression(StandardOperator.LTE,create.constant(0),create.local_name(pb.decl.getName())),
        create.expression(StandardOperator.LT,create.local_name(pb.decl.getName()),rewrite(pb.count))
    ));
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.pre_condition)){
      thread_cb.requires(clause);
      if(clause.getType().isPrimitive(Sort.Resource)){
        thread_cb.ensures(clause);
        if (clause.isa(StandardOperator.Perm)){
          OperatorExpression e=(OperatorExpression)clause;
          if (e.getArg(0).isa(StandardOperator.Subscript)){
            OperatorExpression var=(OperatorExpression)e.getArg(0);
            if ((var.getArg(1) instanceof NameExpression)
                && ((NameExpression)var.getArg(1)).getName().equals(pb.decl.getName())
            ){/*
              cb.requires(create.expression(StandardOperator.ArrayPerm,
                  rewrite(var.getArg(0)),
                  create.constant(0),
                  create.constant(1),
                  rewrite(pb.count),
                  rewrite(e.getArg(1))
              ));
              cb.ensures(create.expression(StandardOperator.ArrayPerm,
                  rewrite(var.getArg(0)),
                  create.constant(0),
                  create.constant(1),
                  rewrite(pb.count),
                  rewrite(e.getArg(1))
              ));
              */
              main_cb.requires(create.expression(StandardOperator.Perm,
                  create.expression(StandardOperator.Subscript,
                      rewrite(var.getArg(0)),
                      create.reserved_name("*")),
                  rewrite(e.getArg(1))
              ));    
              main_cb.ensures(create.expression(StandardOperator.Perm,
                  create.expression(StandardOperator.Subscript,
                      rewrite(var.getArg(0)),
                      create.reserved_name("*")),
                  rewrite(e.getArg(1))
              ));    
              continue;
            }
          }
        }
        Fail("unsupported resource in kernel contract");
      } else {
        if(ASTUtils.find_name(clause,pb.decl.getName())){
          main_cb.requires(create.forall(
              create.expression(StandardOperator.And,
                  create.expression(StandardOperator.LTE,create.constant(0),create.local_name(pb.decl.getName())),
                  create.expression(StandardOperator.LT,create.local_name(pb.decl.getName()),rewrite(pb.count))
              ),
              rewrite(clause),
              rewrite(pb.decl)
          ));
        } else {
          main_cb.requires(rewrite(clause));
        }
      }
    }
    for(ASTNode clause:ASTUtils.conjuncts(pb.contract.post_condition)){
      thread_cb.ensures(clause);
      if(ASTUtils.find_name(clause,pb.decl.getName())){
        main_cb.ensures(create.forall(
            create.expression(StandardOperator.And,
                create.expression(StandardOperator.LTE,create.constant(0),create.local_name(pb.decl.getName())),
                create.expression(StandardOperator.LT,create.local_name(pb.decl.getName()),rewrite(pb.count))
            ),
            rewrite(clause),
            rewrite(pb.decl)
        ));
      } else {
        main_cb.ensures(rewrite(clause));
      }
    }
    currentClass.add_dynamic(create.method_decl(
        create.primitive_type(Sort.Void),
        main_cb.getContract(),
        main_name,
        decl,
        null
    ));
    currentClass.add_dynamic(create.method_decl(
        create.primitive_type(Sort.Void),
        thread_cb.getContract(),
        thread_name,
        rewrite(pb.decl,current_method().getArgs()),
        rewrite(pb.block)
    ));
    result=create.invokation(null,null,main_name,args);
  }

}
