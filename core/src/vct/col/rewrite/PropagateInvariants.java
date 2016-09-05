package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Stack;

import vct.col.ast.*;

public class PropagateInvariants extends AbstractRewriter {

  public PropagateInvariants(ProgramUnit source) {
    super(source);
  }
  
  private Stack<ASTNode> invariants=new Stack();
  
  @Override
  public void visit(Method m){
    Contract c=m.getContract();
    if (c!=null){
      invariants.push(c.invariant);
    }
    super.visit(m);
    if(c!=null){
      invariants.pop();
    }
  }
  
  @Override
  public void visit(LoopStatement l){
    super.visit(l);
    LoopStatement res=(LoopStatement)result;
    if (l.getContract()!=null && !l.getContract().isEmpty()){
      for(ASTNode inv:invariants){
        res.prependInvariant(inv);
      }
    }
    result=res;
  }
  
  /*
  @Override
  public void visit(ParallelRegion region){
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode inv:invariants) { cb.prependInvariant(inv); }
    rewrite(region.contract,cb);
    result=create.region(cb.getContract(),rewrite(region.blocks));
  }
  */
  
  @Override
  public void visit(ParallelBarrier pb){
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode inv:invariants) { cb.prependInvariant(inv); }
    rewrite(pb.contract,cb);
    result=create.barrier(pb.label,cb.getContract(),pb.invs,rewrite(pb.body));
  }
  
  @Override
  public void visit(ParallelInvariant inv){
    ArrayList <ASTNode> invs=new ArrayList();
    for(ASTNode n:invariants) { invs.add(rewrite(n)); }
    invs.add(rewrite(inv.inv));
    result=create.invariant_block(inv.label,create.fold(StandardOperator.Star,invs),rewrite(inv.block));
  }
  @Override
  public void visit(ParallelBlock pb){
    ContractBuilder cb=new ContractBuilder();
    for(ASTNode inv:invariants) { cb.prependInvariant(inv); }
    rewrite(pb.contract,cb);
    ParallelBlock res=create.parallel_block(
        pb.label,
        cb.getContract(),
        rewrite(pb.iters),
        rewrite(pb.block),
        rewrite(pb.deps)
    );
    result=res;

  }

}
