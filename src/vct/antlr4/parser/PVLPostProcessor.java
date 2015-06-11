package vct.antlr4.parser;


import hre.ast.BranchOrigin;
import hre.ast.WrappingOrigin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSpecial;
import vct.col.ast.BeforeAfterAnnotations;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.rewrite.AbstractRewriter;

/**
 * Rewrite a PVL AST, produced by parsing, to conform to the COL AST standard.  
 */
public class PVLPostProcessor extends AbstractRewriter {

  private static String INV="lock_invariant";
  
  public PVLPostProcessor(ProgramUnit source) {
    super(source);
  }
  
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Lock:
      currentBlock.add(create.special(ASTSpecial.Kind.Inhale,create.invokation(rewrite(s.args[0]),null,INV)));
      currentBlock.add(create.expression(StandardOperator.Unfold,create.invokation(rewrite(s.args[0]),null,INV)));
      result=null;
      break;
    case Unlock:
      currentBlock.add(create.expression(StandardOperator.Fold,create.invokation(rewrite(s.args[0]),null,INV)));
      currentBlock.add(create.special(ASTSpecial.Kind.Exhale,create.invokation(rewrite(s.args[0]),null,INV)));
      result=null;
      break;
    default:
      super.visit(s);
    }
  }
  
  @Override
  public void visit(ASTClass c){
    super.visit(c);
    if (c.kind==ClassKind.Kernel) return;
    ASTClass decl=(ASTClass)result;
    boolean withlock=false;
    for(Method m:decl.dynamicMethods()){
      System.err.printf("%s %s%n",m.kind,m.name);
      if (m.kind==Method.Kind.Predicate && m.name.equals("lock_invariant")){
        if (withlock){
          m.getOrigin().report("error","second declaration of lock_invariant.");
          throw new Error();
        }
        if (m.getArity()>0){
          m.getOrigin().report("error","predicate lock_invariant cannot have arguments");
          throw new Error();
        }
        withlock=true;
      }
    }
    int N=0;
    for(Method m:decl.dynamicMethods()){
      if (m.kind==Method.Kind.Constructor) {
        if (withlock) {
          BranchOrigin branch=new BranchOrigin("Commit lock invariant during construction",m.getOrigin());
          create.enter();
          create.setOrigin(branch);
          ASTNode S=create.special(ASTSpecial.Kind.Exhale,create.invokation(null,null,"lock_invariant"));
          create.leave();
          ((BlockStatement)m.getBody()).append(S);
        }
        N++;
      }
    }
    if (N==0) {
      if (withlock){
        c.getOrigin().report("error","cannot generate implicit constructor for class with lock invariant");
        throw new Error();
      } else {
        create.addZeroConstructor(decl);
      }
    }
  }

}
