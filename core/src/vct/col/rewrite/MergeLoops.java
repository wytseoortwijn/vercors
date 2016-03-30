package vct.col.rewrite;

import java.util.ArrayList;

import hre.ast.Origin;
import vct.col.ast.*;
import vct.col.util.ASTUtils;
import vct.util.Configuration;

public class MergeLoops extends AbstractRewriter {

  public MergeLoops(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(ForEachLoop loop){
    ArrayList<DeclarationStatement> decls=new ArrayList();
    ArrayList<ASTNode> guard=new ArrayList();
    ASTNode body=null;
    ContractBuilder cb=new ContractBuilder();
    while(body==null){
      for(DeclarationStatement d:loop.decls){
        decls.add(rewrite(d));
      }
      guard.add(rewrite(loop.guard));
      body=loop.body;
      if (body instanceof BlockStatement){
        BlockStatement block = (BlockStatement)body;
        if (block.getLength()==1){
          body=block.get(0);
        }
      }
      rewrite(loop.getContract(),cb);
      if (body instanceof ForEachLoop){
        Warning("detect nested loop");
        ForEachLoop nested=(ForEachLoop) body;
        if (cb.isEmpty() || nested.getContract().isEmpty()){
          Warning("merging");
          loop=nested;
          body=null;
        } else {
          body=rewrite(loop.body);
        }
      } else {
        body=rewrite(loop.body);
      }
    }
    ForEachLoop res=create.foreach(
        decls.toArray(new DeclarationStatement[0]),
        create.fold(StandardOperator.And,guard),
        body);
    res.setContract(cb.getContract());
    result=res;
  }

}
