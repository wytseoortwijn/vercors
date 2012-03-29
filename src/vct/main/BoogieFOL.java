package vct.main;

import vct.boogie.BoogieReport;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.AbstractScanner;
import vct.col.ast.BlockStatement;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.StandardOperator;
import vct.col.rewrite.AbstractRewriter;
import vct.col.util.ASTFactory;

/**
 * This class scans a given AST for assertions and checks each assertion as if it were
 * a First Order Logic formula using Boogie.
 * 
 * @author Stefan Blom
 *
 */
public class BoogieFOL {

  /**
   * This class extends the abstract scanner to scan for methods.
   * It will then scan those methods for assertions.
   *  
   * @author Stefan Blom
   *
   */
  private static class MethodFinder extends AbstractScanner {
    
    /** 
     * Executed when the abstract scanner finds a method.
     */
    public void visit(Method m){
      ASTNode body=m.getBody();
      if (body instanceof BlockStatement){
        /* In Java the body of a method always is a block.
         * However, the AST also allows expressions as Method bodies.
         */
        BlockStatement block=(BlockStatement)body;
        int N=block.getLength();
        for(int i=0;i<N;i++){
          if (block.getStatement(i) instanceof OperatorExpression){
            OperatorExpression e=(OperatorExpression)block.getStatement(i);
            System.err.printf("checking formula at %s%n",e.getOrigin());
            if (e.getOperator()==StandardOperator.Assert);
            DeclarationStatement args[]=m.getArgs();
            ASTNode formula=e.getArg(0);
            BoogieReport res=check_boogie(args,formula);
            System.err.printf("formula at %s:%s%n",e.getOrigin(),res);
          }
        }
      } else {
        System.err.printf("skipping non-block body of method %s at %s%n",m.getName(),m.getOrigin());
      }
    }
  }
  /** find all assertions in the given program and check them 
   * with Boogie as if they were first order logic formulas.
   * @param program The program to scan for assertions.
   */
  public static void main(ASTClass program) {
    MethodFinder finder=new MethodFinder();
    program.accept(finder);
  }

  /**
   * Check a formula using Boogie.
   * @param args The variables used in the formula. These are implicitly universally quantified.
   * @param formula The formula to be checked.
   */
  public static BoogieReport check_boogie(DeclarationStatement args[],ASTNode formula){
    ASTFactory create=new ASTFactory();
    create.setOrigin(formula.getOrigin());
    
    AbstractRewriter copy_rw=new AbstractRewriter(){};
    
    ASTClass program=create.ast_class("dummy");
    for (ASTNode n:args){
      program.add_static(n.apply(copy_rw));
    }
    ASTNode assertion=create.expression(StandardOperator.Assert,formula.apply(copy_rw));
    BlockStatement body=create.block(assertion);
    program.add_static(create.method_decl(
        create.primitive_type(PrimitiveType.Sort.Void),
        null,
        "formula",
        new DeclarationStatement[0],
        body));
    //hre.debug.HeapDump.tree_dump(new hre.io.PrefixPrintStream(System.err),program,ASTNode.class);
    return vct.boogie.Main.TestBoogie(program);
  }
}
