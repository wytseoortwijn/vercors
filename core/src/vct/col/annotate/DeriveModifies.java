package vct.col.annotate;

import java.util.HashSet;
import java.util.Hashtable;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTVisitor;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.Method;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.RecursiveVisitor;
import vct.col.rewrite.AbstractRewriter;

import static hre.System.Debug;
import static hre.System.Fail;

/**
 * This rewriter adds modifies clauses to all method contracts.
 * 
 * @author Stefan Blom
 */ 
public class DeriveModifies extends RecursiveVisitor<Object> {

  public DeriveModifies(){
    super(null,null);
  }
  
  private Hashtable<String,Contract>cache=new Hashtable<String, Contract>();
  /** We copy everything except Method declarations.
   *  Therefore this is the only visitor that must be overridden. 
   */

  private boolean dirty;
  
  public void visit(Method m) {
    Contract c=m.getContract();
    if (c==null){
      c=ContractBuilder.emptyContract();
    }
    HashSet<ASTNode> old_mods=new HashSet();
    if (c.modifies!=null) for(ASTNode n:c.modifies) old_mods.add(n);
    ContractBuilder builder=new ContractBuilder();
    builder.requires(c.pre_condition);
    builder.ensures(c.post_condition);
    builder.modifies();
    ASTVisitor<Object> mod=new ModificationScanner(cache,builder);
    m.accept(mod);
    // change contract in result.
    c=builder.getContract();
    cache.put(m.getName(),c);
    m.setContract(c);
    for(ASTNode n:c.modifies) {
      if (!old_mods.contains(n)) dirty=true;
      break;
    }
  }

  public void annotate(ASTClass program) {
    dirty=true;
    int pass=0;
    while(dirty){
      pass++;
      dirty=false;
      System.err.printf("modifies annotation pass %d%n",pass);
      program.accept(this);
    }
  }

  public void annotate(ProgramUnit arg) {
    for(ASTClass cl:arg.classes()){
      annotate(cl);
    }
  }

}
