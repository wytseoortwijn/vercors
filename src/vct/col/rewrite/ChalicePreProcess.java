package vct.col.rewrite;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.CompilationUnit;
import vct.col.ast.Dereference;
import vct.col.ast.MethodInvokation;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import hre.ast.MessageOrigin;

import java.util.Hashtable;
import java.util.Map.Entry;

public class ChalicePreProcess extends AbstractRewriter {

  private Hashtable<Type,String>cell_types=new Hashtable();
  
  public ChalicePreProcess(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public ProgramUnit rewriteAll(){
    ProgramUnit res=super.rewriteAll();
    for(Entry<Type,String> entry : cell_types.entrySet()){
      create.setOrigin(new MessageOrigin("added by ChalicePreProcess"));
      ASTClass cl=create.ast_class(entry.getValue(), ASTClass.ClassKind.Plain , null,null);
      cl.add_dynamic(create.field_decl("item",entry.getKey()));
      res.add(new CompilationUnit(entry.getValue()).add(cl));
    }
    return res;
  }
  
  @Override
  public void visit(MethodInvokation e){
    if (e.method.equals("length") && e.object.getType().isPrimitive(PrimitiveType.Sort.Sequence)){
      result=create.expression(StandardOperator.Size,rewrite(e.object));
    } else {
      super.visit(e);
    }
  }
  
  @Override
  public void visit(Dereference e){
    if (e.field.equals("length") && e.object.getType().isPrimitive(PrimitiveType.Sort.Sequence)){
      result=create.expression(StandardOperator.Size,rewrite(e.object));
    } else {
      super.visit(e);
    }    
  }
  
  @Override
  public void visit(PrimitiveType t){
    if (t.sort==PrimitiveType.Sort.Cell){
      String sort="cell_of_"+t.getArg(0);
      cell_types.put((Type)t.getArg(0),sort);
      result=create.class_type(sort);
    } else {
      super.visit(t);
    }
  }
  
  @Override
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
      case Minus:{
        super.visit(e);
        if (e.getArg(0).getType().isPrimitive(Sort.Fraction) ||
            e.getArg(0).getType().isPrimitive(Sort.ZFraction) ||
            e.getArg(1).getType().isPrimitive(Sort.Fraction) ||
            e.getArg(1).getType().isPrimitive(Sort.ZFraction) )
        {
          ASTNode temp=result;
          result=create.expression(StandardOperator.ITE,
              create.expression(StandardOperator.LT,rewrite(e.getArg(0)),rewrite(e.getArg(1))),
              create.constant(0),
              temp
          );
          result.setType(new PrimitiveType(Sort.ZFraction));
        }
        break;
      }
      case Plus:{
        if (e.getType().isPrimitive(Sort.Sequence)){
          result=create.expression(StandardOperator.Append,rewrite(e.getArguments()));
        } else {
          super.visit(e);
        }
        break;
      }
      default:
        super.visit(e);
        break;
    }
  }
     
}
