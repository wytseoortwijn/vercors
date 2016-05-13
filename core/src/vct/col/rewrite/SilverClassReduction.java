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
      
  private static final String ILLEGAL_CAST="possibly_illegal_cast";
  
  private ASTClass ref_class;
  
  public SilverClassReduction(ProgramUnit source) {
    super(source);
    create.setOrigin(new MessageOrigin("collected class Ref"));
    ref_class=create.ast_class("Ref", ASTClass.ClassKind.Record,null, null, null);
    target().add(ref_class);
  }

  @Override
  public void visit(AxiomaticDataType adt){
    super.visit(adt);
    if (adt.name.equals("TYPE")){
      AxiomaticDataType res=(AxiomaticDataType)result;
      res.add_cons(create.function_decl(
          create.class_type("TYPE"),
          null,
          "type_of",
          new DeclarationStatement[]{create.field_decl("val",create.class_type("Ref"))},
          null
      ));
      ref_class.add(create.field_decl(ILLEGAL_CAST,create.class_type("Ref")));
    }
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
    if (source().find(t.getNameFull())==null){
      // ADT type
      super.visit(t);
    } else {
      result=create.class_type("Ref");
    }
  }
  @Override
  public void visit(Dereference e){
    if (e.object.getType()==null){
      Warning("untyped object %s",e.object.getOrigin());
      result=create.dereference(rewrite(e.object),"????"+SEP+e.field);
      return;
    }
    result=create.dereference(rewrite(e.object),((ClassType)e.object.getType()).getName()+SEP+e.field);
  }
  
  @Override
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
    case New:{
      ClassType t=(ClassType)e.getArg(0);
      ASTClass cl=source().find(t);
      ArrayList<ASTNode>args=new ArrayList();
      //NameExpression f=create.field_name("A__x");
      //f.setSite(ref_class);
      for(DeclarationStatement field:cl.dynamicFields()){
        args.add(create.dereference(create.class_type("Ref"),cl.name+SEP+field.name));
      }
      result=create.expression(StandardOperator.NewSilver,args.toArray(new ASTNode[0]));
      break;
    }
    case TypeOf:{
      result=create.domain_call("TYPE","type_of",rewrite(e.getArg(0)));
      break;
    }
    case Cast:{
      ASTNode object=rewrite(e.getArg(1));
      Type t=(Type)e.getArg(0);
      ASTNode condition=create.invokation(null, null,"instanceof",
          create.domain_call("TYPE","type_of",object),
          //create.invokation(null,null,"type_of",object));
          create.domain_call("TYPE","class_"+t));
          
      ASTNode illegal=create.dereference(object,ILLEGAL_CAST);
      result=create.expression(StandardOperator.ITE,condition,object,illegal);
      break;
    }
    default:
      super.visit(e);
    }
  }
}
