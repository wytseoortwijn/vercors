package vct.col.rewrite;

import vct.col.ast.*;

public class PVLCompiler extends AbstractRewriter {

  private static String INV="lock_invariant";

  public PVLCompiler(ProgramUnit source) {
    super(source);
  }
  
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Lock:
      result=create.invokation(rewrite(s.args[0]), null, "lock");
      break;
    case Unlock:
      result=create.invokation(rewrite(s.args[0]), null, "unlock");
      break;
    case Wait:
      result=create.invokation(rewrite(s.args[0]), null, "lock_wait");
      break;
    case Notify:
      result=create.invokation(rewrite(s.args[0]), null, "lock_notify");
      break;
    case Fork:
      result=create.invokation(rewrite(s.args[0]), null, "fork");
      break;
    case Join:
      result=create.invokation(rewrite(s.args[0]), null, "join");
      break;
    default:
      super.visit(s);
    }
  }

  public void visit(ASTClass cl){
    switch(cl.kind){
    case Abstract:
      return;
    case Plain:
      break;
    default:
      Abort("class kind %s not implemented",cl.kind);
    }
    if (cl.parameters.length!=0){
      Fail("cannot compile classes with parameters");
    }
    DeclarationStatement parameters[]=new DeclarationStatement[0];
    if (cl.implemented_classes.length!=0){
      Fail("cannot compile classes that implement interfaces");
    }
    ClassType supports[]=new ClassType[0];
    if (cl.super_classes.length!=0){
      Fail("cannot compile classes that extends others");
    }    
    ClassType bases[]=new ClassType[]{create.class_type(new String[]{"col","lang","Object"})};
    currentTargetClass=create.ast_class(cl.name,ASTClass.ClassKind.Plain, parameters, bases, supports);
    for(ASTNode node:cl){
      node=rewrite(node);
      node.setFlag(ASTFlags.PUBLIC,true);
      currentTargetClass.add(node);
    }
    result=currentTargetClass;
    currentTargetClass=null;
  }
}
