package vct.col.rewrite;

import hre.ast.MessageOrigin;

import java.util.ArrayList;
import java.util.HashSet;

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
import vct.util.Configuration;

public class RewriteArrayRef extends AbstractRewriter {

  public enum Target { Cell, Ref };
  
  public final Target target;
  
	public RewriteArrayRef(ProgramUnit source,Target target) {
	  super(source);
	  this.target=target;
  }
	
  private HashSet<Type> new_array;
  private HashSet<Type> ref_array=new HashSet<Type>();
	
	@Override
	public void visit(OperatorExpression e){
		switch (e.getOperator()){
		  case NEQ:
		  {
        ASTNode e0=e.getArg(0);
        ASTNode e1=e.getArg(1);
        ASTNode array=null;
        if (e0.isReserved(ASTReserved.Null) && e1.getType().isPrimitive(Sort.Array)){
          array=e1;
        }
        if (e1.isReserved(ASTReserved.Null) && e0.getType().isPrimitive(Sort.Array)){
          array=e0;
        }
        if(array==null){
          super.visit(e);
        } else {
          ASTNode base;
          Type t=array.getType();
          array=rewrite(array);
          if (t.getArgCount()==2){
            base=create.expression(StandardOperator.EQ,
                create.expression(StandardOperator.Size, array),
                rewrite(t.getArg(1)));
          } else {
            base=create.constant(true);
          }
          ASTNode guard=create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name("i_481")),
              create.expression(StandardOperator.LT,create.local_name("i_481"),create.expression(StandardOperator.Size,array)));
          ASTNode claim=create.expression(StandardOperator.Value,create.dereference(
              create.expression(StandardOperator.Subscript,array,create.local_name("i_481")),"array_dummy"));
          DeclarationStatement decl=create.field_decl("i_481",create.primitive_type(Sort.Integer));
          result=create.expression(StandardOperator.Star,
              base, create.starall(guard, claim, decl));
        }
		    break;
		  }
		  case Subscript:
		  	super.visit(e);
			  if (e.getArg(0).getType().isPrimitive(Sort.Array)){
			    switch(target){
			    case Ref:{
  			  	ASTNode res=result;
  			  	Type t=(Type)e.getArg(0).getType().getArg(0);
  			  	String field=t.toString()+"_value";
  			  	ref_array.add(t);
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
		  case NewArray:
        Type t=(Type)e.getArg(0);
        new_array.add(t);
		    switch(target){
        case Ref:{
  		    result=create.invokation(null,null,"new_array_"+t,rewrite(e.getArg(1)));
	  	    break;
        }
        case Cell:{
          result=create.invokation(null,null,"new_array_"+t,rewrite(e.getArg(1)));
          break;
          
        }}
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
		    Type tt=(Type)t.getArg(0);
		    ref_array.add(tt);
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
        res.add(ref);
      }
      for(Type t:ref_array){
        String s=t.toString();
        ref.add_dynamic(create.field_decl(s+"_value",t));
      }
      ref.add_dynamic(create.field_decl("array_dummy",create.primitive_type(Sort.Integer)));
    }
    return res;
  }

  @Override
  public void visit(ASTClass cl){
    new_array=new HashSet();
    super.visit(cl);
    ASTClass res=(ASTClass)result;
    for(Type t:new_array){
      Type result_type;
      if (target==Target.Ref){
        result_type=create.primitive_type(Sort.Sequence,create.class_type("Ref"));
      } else {
        result_type=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t)));
      }
      ContractBuilder cb=new ContractBuilder();
      
      cb.ensures(create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.reserved_name(ASTReserved.Result)),
          create.local_name("len")));
      DeclarationStatement decl=create.field_decl("i",create.primitive_type(Sort.Integer));
      ASTNode guard=and(lte(constant(0),create.local_name("i")),
          less(create.local_name("i"),create.expression(StandardOperator.Size,create.reserved_name(ASTReserved.Result))));
      ASTNode base=create.expression(StandardOperator.Subscript,create.reserved_name(ASTReserved.Result),create.local_name("i"));
      ASTNode claim;
      if (target==Target.Ref){
        claim=create.expression(StandardOperator.Perm,
            create.dereference(base,t+"_value")
            ,create.reserved_name(ASTReserved.FullPerm));
      } else {
        claim=create.expression(StandardOperator.Perm,
            create.dereference(base,"item")
            ,create.reserved_name(ASTReserved.FullPerm));
      }
      cb.ensures(create.starall(guard, claim, decl));
      DeclarationStatement args[]=new DeclarationStatement[]{create.field_decl("len",create.primitive_type(Sort.Integer))};
      res.add_dynamic(create.method_decl(result_type,cb.getContract(), "new_array_"+t, args,null));
    }
    if (target==Target.Ref){
      ref_array.addAll(new_array);
    }
    new_array=null;
    result=res;
  }

}

