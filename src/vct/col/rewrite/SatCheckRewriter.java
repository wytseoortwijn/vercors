package vct.col.rewrite;

import hre.ast.BranchOrigin;
import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.OriginWrapper;

public class SatCheckRewriter extends AbstractRewriter {

	public SatCheckRewriter(ProgramUnit source) {
	  super(source);
  }

  @Override
  public void visit(Method m) {
    //checkPermission(m);
    String name=m.getName();
    int N=m.getArity();
    if (currentContractBuilder==null) currentContractBuilder=new ContractBuilder();
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract mc=m.getContract();
    if (mc!=null){
      rewrite(mc,currentContractBuilder);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    Contract c=currentContractBuilder.getContract();
    currentContractBuilder=null;
    ASTNode body=rewrite(m.getBody());
    if (body!=null) switch(kind){
    case Plain:
    case Constructor:
      ASTNode refute=create.expression(StandardOperator.Refute,create.constant(false));
    	BranchOrigin branch=new BranchOrigin("Contract Unsatisfiability Check",null);
      OriginWrapper.wrap(null,refute, branch);
	    if (body instanceof BlockStatement){
	    	((BlockStatement)body).prepend(refute);
	    } else {
	    	body=create.block(refute,body);
	    }
    }
    result=create.method_kind(kind, rt, c, name, args, m.usesVarArgs(), body);
  }

}
