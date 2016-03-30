package vct.col.annotate;

import java.util.Hashtable;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.Dereference;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.RecursiveVisitor;
import vct.col.ast.Type;
import static hre.System.Abort;
import static hre.System.Fail;

public class ModificationScanner extends RecursiveVisitor<Object> {

  private ContractBuilder builder;
  private Hashtable<String, Contract> cache;
  public ModificationScanner(Hashtable<String, Contract> cache, ContractBuilder builder) {
    super(null,null);
    this.builder=builder;
    this.cache=cache;
  }

  private void modifies_loc(ASTNode n){
    if (n instanceof NameExpression){
      NameExpression name=(NameExpression)n;
      if (name.getSite() instanceof ASTClass){
        builder.modifies(n);
      }
    } else if (n instanceof Dereference){
      builder.modifies(n);
    } else {
      Abort("unimplemented location type %s",n.getClass());
    }
  }
  
  public void visit(AssignmentStatement s){
    modifies_loc(s.getLocation());
  }
  
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    if (m==null) Abort("definition is null at %s",e.getOrigin());
    Contract c=m.getContract();
    if (c!=null && c.modifies!=null) {
      for (ASTNode loc : c.modifies) {
        modifies_loc(loc);
      }
    }
  }
  
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case PreIncr:
    case PostIncr:
    case PreDecr:
    case PostDecr:
      modifies_loc(e.getArg(0));
    }
  }
  
}
