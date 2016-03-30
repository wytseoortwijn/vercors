package vct.col.rewrite;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.util.FeatureScanner;

public class ForkJoinEncode extends AbstractRewriter {

  public ForkJoinEncode(ProgramUnit source) {
    super(source);
  }
  
  
  @Override
  public void visit(Method m){
    if(m.name.equals("run")){
      Contract c=m.getContract();
      FeatureScanner features=new FeatureScanner();
      c.post_condition.accept(features);
      if(features.usesOperator(StandardOperator.Old)){
        Fail("The post-condition of a run method is not allowed to use the \\old operator.");
      }
      ContractBuilder cb=new ContractBuilder();
      cb.requires(rewrite(c.pre_condition));
      cb.ensures(create.invokation(null,null,"joinToken"));
      Method fork=create.method_decl(
          create.primitive_type(Sort.Void),
          cb.getContract(),
          "forkOperator",
          new DeclarationStatement[0],
          null
      );
      currentTargetClass.add_dynamic(fork);
      cb=new ContractBuilder();
      cb.requires(create.invokation(null,null,"joinToken"));
      cb.ensures(rewrite(c.post_condition));
      Method join=create.method_decl(
          create.primitive_type(Sort.Void),
          cb.getContract(),
          "joinOperator",
          new DeclarationStatement[0],
          null
      );
      currentTargetClass.add_dynamic(join);
      Method token=create.predicate("joinToken",null);
      currentTargetClass.add_dynamic(token);
    }
    super.visit(m);
  }
  
  @Override
  public void visit(ASTSpecial e){
    switch(e.kind){
    case Fork:
      result=create.invokation(rewrite(e.args[0]),null,"forkOperator");
      break;
    case Join:
      result=create.invokation(rewrite(e.args[0]),null,"joinOperator");
      break;      
    default:
      super.visit(e);
      break;
    }
  }

}
