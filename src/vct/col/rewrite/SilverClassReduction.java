package vct.col.rewrite;

import hre.ast.MessageOrigin;

import java.util.ArrayList;
import java.util.Stack;

import vct.col.ast.*;

/**
 * This rewriter converts a program with classes into
 * a program with records.
 * 
 * 
 * @author Stefan Blom
 *
 */
public class SilverClassReduction extends AbstractRewriter {

  private static final String SEP="__";
      
  private ASTClass ref_class;
  
  public SilverClassReduction(ProgramUnit source) {
    super(source);
    create.setOrigin(new MessageOrigin("collected class Ref"));
    ref_class=create.ast_class("Ref", ASTClass.ClassKind.Record, null, null);
    target().add(ref_class);
  }

  @Override
  public void visit(ASTClass cl){
    if (cl.getStaticCount()>0){
      Fail("class conversion cannot be used for static entries yet.");
    }
    for(DeclarationStatement decl:cl.dynamicFields()){
      create.enter();
      create.setOrigin(decl.getOrigin());
      DeclarationStatement res=create.field_decl(cl.name+SEP+decl.name,
          rewrite(decl.getType()),rewrite(decl.getInit()));
      create.leave();
      ref_class.add(res);
    }
  }
  
  @Override
  public void visit(ClassType t){
    result=create.class_type("Ref");
  }
  @Override
  public void visit(Dereference e){
    result=create.dereference(rewrite(e.object),((ClassType)e.object.getType()).getName()+SEP+e.field);
  }
  
  @Override
  public void visit(OperatorExpression e){
    if (e.getOperator()==StandardOperator.New){
      ClassType t=(ClassType)e.getArg(0);
      ASTClass cl=source().find(t);
      ArrayList<ASTNode>args=new ArrayList();
      //NameExpression f=create.field_name("A__x");
      //f.setSite(ref_class);
      for(DeclarationStatement field:cl.dynamicFields()){
        args.add(create.dereference(create.class_type("Ref"),cl.name+SEP+field.name));
      }
      result=create.expression(StandardOperator.NewSilver,args.toArray(new ASTNode[0]));
    } else {
      super.visit(e);
    }
  }
}
