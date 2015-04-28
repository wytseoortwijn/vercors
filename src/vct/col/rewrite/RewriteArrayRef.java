package vct.col.rewrite;

import hre.ast.MessageOrigin;

import java.util.ArrayList;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.BindingExpression;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.Hole;
import vct.col.ast.IntegerValue;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.Type;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;

public class RewriteArrayRef extends AbstractRewriter {

  public enum Target { Cell, Ref };
  
  public final Target target;
  
	public RewriteArrayRef(ProgramUnit source,Target target) {
	  super(source);
	  this.target=target;
  }
	
	@Override
	public void visit(OperatorExpression e){
		switch (e.getOperator()){
		  case Subscript:
		  	super.visit(e);
			  if (e.getArg(0).getType().isPrimitive(Sort.Array)){
			    switch(target){
			    case Ref:{
  			  	ASTNode res=result;
  			  	String field=e.getArg(0).getType().getArg(0).toString()+"_value";
  			  	result=create.dereference(res,field);
  			  	break;
			    }
			    case Cell:{
            ASTNode res=result;
            result=create.dereference(res,"item");
            break;
          }}
			  }
			  break;
		  case Length:
		    result=create.expression(StandardOperator.Size,rewrite(e.getArguments()));
		    break;
			default:
				super.visit(e);
		}
	}
	
	@Override
	public void visit(Dereference e){
	  if (e.field.equals("length")){
	    result=create.expression(StandardOperator.Size,rewrite(e.object));
	  } else {
	    super.visit(e);
	  }
	}
	
	@Override
	public void visit(PrimitiveType t){
		switch(t.sort){
		case Array:
		  switch(target){
		  case Ref:
		    result=create.primitive_type(Sort.Sequence,create.class_type("Ref"));
		    break;
		  case Cell:
  			result=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t.getArg(0))));
  			break;
		  }
			break;
		  default:
		  	super.visit(t);
		}
	}
	
  @Override
  public ProgramUnit rewriteAll(){
    ProgramUnit res=super.rewriteAll();
    if (target==Target.Ref){
      ASTClass ref=res.find("Ref");
      create.setOrigin(new MessageOrigin("Rewrite arrays to sequences"));
      if (ref==null){
        ref=create.ast_class("Ref",ASTClass.ClassKind.Plain,null,null,null);
        ref.add_dynamic(create.field_decl("Integer_value",create.primitive_type(Sort.Integer)));
        ref.add_dynamic(create.field_decl("Boolean_value",create.primitive_type(Sort.Boolean)));
        res.add(ref);
      }
    }
    return res;
  }

  @Override
  public void visit(ASTClass cl){
    super.visit(cl);
    if (target==Target.Ref){
      ASTClass res=(ASTClass)result;
      res.add_dynamic(create.field_decl("Integer_value",create.primitive_type(Sort.Integer)));
      res.add_dynamic(create.field_decl("Boolean_value",create.primitive_type(Sort.Boolean)));
      result=res;
    }
  }

}

