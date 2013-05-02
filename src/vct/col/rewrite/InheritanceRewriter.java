package vct.col.rewrite;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;
import static hre.System.*;

public class InheritanceRewriter extends AbstractRewriter {

  public InheritanceRewriter(ProgramUnit source) {
    super(source);
  }

  private AbstractRewriter copy_abstract=new AbstractRewriter(source()){
    @Override
    public void visit(Method m){
      result=create.method_kind(m.kind,rewrite(m.getReturnType()), rewrite(m.getContract()), m.getName(), rewrite(m.getArgs()) , null);
    }
  };
  
  ASTClass super_class=null;
  
  @Override
  public void visit(ASTClass cl){
    ASTClass res=create.ast_class(cl.name, cl.kind, new ClassType[0], new ClassType[0]);
    switch(cl.super_classes.length){
      case 0:
        super_class=null;
        break;
      case 1:
        super_class=target().find(cl.super_classes[0]);
        break;
      default:
        Fail("Multiple inheritance is not supported.");
    }
    if (cl.implemented_classes.length>0) Fail("interfaces are future work");
    for(ASTNode node:cl.staticMembers()){
      res.add_static(rewrite(node));
    }
    for(ASTNode node:cl.dynamicMembers()){
      res.add_dynamic(rewrite(node));
    }
    if (super_class!=null){
      for(Method m:super_class.dynamicMethods()){
        switch(m.kind){
          case Predicate:
          case Plain:{
            Type type[]=m.getArgType();
            if (res.find(m.getName(),null,type)==null){
              Warning("method %s of kind %s in class %s will be copied",m.getName(),m.kind,cl.name);
              res.add_dynamic(copy_abstract.rewrite(m));
            } else {
              Warning("method %s of kind %s in class %s is an override",m.getName(),m.kind,cl.name);
            }
            break;
          }
          default:{
            Warning("ignoring method %s of kind %s in class %s",m.getName(),m.kind,cl.name);
          }
        }
      }
      for(DeclarationStatement decl:super_class.dynamicFields()){
        String name=decl.getName();
        if (cl.find_field(name)==null){
          res.add_dynamic(copy_abstract.rewrite(decl));
        }
      }
      super_class=null;
    }
    result=res;
  }
  
  @Override
  public void visit(Method m){
    super.visit(m);
    if (super_class!=null){
      switch(m.kind){
        case Plain:{
          Method override=super_class.find(m.getName(),null,m.getArgType());
          Contract c=m.getContract();
          if (override==null) return;
          if (c!=null && override!=null){
            Fail("alternate contracts are not supported at %s",m.getOrigin());
          }
          Method res=(Method)result;
          
          res.setContract(rewrite(override.getContract()));
          
          result=res;
          break;
        }
        default:{
          Warning("check the case of %s in InheritanceRewriter.visit(Method)",m.kind);
          break;
        }
      }
    }
  }
}
