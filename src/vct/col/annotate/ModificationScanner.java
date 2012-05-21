package vct.col.annotate;

import java.util.Hashtable;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.AbstractScanner;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.OperatorExpression;
import vct.col.ast.Type;

import static hre.System.Abort;
import static hre.System.Fail;

public class ModificationScanner extends AbstractScanner {

  private ContractBuilder builder;
  private Hashtable<String, Contract> cache;
  public ModificationScanner(Hashtable<String, Contract> cache, ContractBuilder builder) {
    this.builder=builder;
    this.cache=cache;
  }

  public void visit(AssignmentStatement s){
    builder.modifies(s.getLocation());
  }
  
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    if (m==null) Abort("definition is null at %s",e.getOrigin());
    Contract c=m.getContract();
    if (c!=null && c.modifies!=null) {
      for (ASTNode loc : c.modifies) {
        builder.modifies(loc);
      }
    }
  }
  
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case PreIncr:
    case PostIncr:
    case PreDecr:
    case PostDecr:
      builder.modifies(e.getArg(0));
    }
  }
  
}
