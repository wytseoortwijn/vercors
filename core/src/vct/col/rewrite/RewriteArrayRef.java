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

	public RewriteArrayRef(ProgramUnit source) {
	  super(source);
  }
	
  private HashSet<Type> new_array;
  private HashSet<Type> ref_array=new HashSet<Type>();
	
	@Override
	public void visit(OperatorExpression e){
		switch (e.getOperator()){
		  case EQ:
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
          result=create.expression(e.getOperator(),
              create.reserved_name(ASTReserved.OptionNone),
              rewrite(array));
          /* TODO: this is old code that inserts information about the encoding.
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
           */
        }
		    break;
		  }
		  case Subscript:
			  if (e.getArg(0).getType().isPrimitive(Sort.Array)){
			    
          ASTNode res=create.expression(StandardOperator.OptionGet,rewrite(e.getArg(0)));
          res=create.expression(StandardOperator.Subscript,res,rewrite(e.getArg(1)));
          result=create.dereference(res,"item");
			  } else {
			    super.visit(e);
			  }
			  break;
		  case Length:{
		    ASTNode res=create.expression(StandardOperator.OptionGet,rewrite(e.getArg(0)));
		    result=create.expression(StandardOperator.Size,res);
		    break;
		  }
		  case NewArray:{
        Type t=(Type)e.getArg(0);
        new_array.add(t);
        result=create.invokation(null,null,"new_array_some_"+t,rewrite(e.getArg(1)));
		    break;
		  }
			default:
				super.visit(e);
		}
	}
	
  @Override
	public void visit(Dereference e){
	  if (e.field.equals("length")){
	    ASTNode res=rewrite(e.object);
	    if (e.object.getType().isPrimitive(Sort.Array)){
  	    res=create.expression(StandardOperator.OptionGet,res);
	    }
      result=create.expression(StandardOperator.Size,res);
	  } else {
	    super.visit(e);
	  }
	}
	
	@Override
	public void visit(PrimitiveType t){
		switch(t.sort){
		case Array:
			result=
			  create.primitive_type(Sort.Option,
			    create.primitive_type(Sort.Sequence,
		          create.primitive_type(Sort.Cell,
			        rewrite(t.getArg(0)))));
			break;
		  default:
		  	super.visit(t);
		}
	}
	
  @Override
  public ProgramUnit rewriteAll(){
    ProgramUnit res=super.rewriteAll();
    // TODO: move newarray generation here.
    return res;
  }

  @Override
  public void visit(ASTClass cl){
    new_array=new HashSet();
    super.visit(cl);
    ASTClass res=(ASTClass)result;
    for(Type t:new_array){
      Type result_type;
      result_type=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t)));
      ContractBuilder cb=new ContractBuilder();
      
      cb.ensures(create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.reserved_name(ASTReserved.Result)),
          create.local_name("len")));
      DeclarationStatement decl=create.field_decl("i",create.primitive_type(Sort.Integer));
      ASTNode guard=and(lte(constant(0),create.local_name("i")),
          less(create.local_name("i"),create.expression(StandardOperator.Size,create.reserved_name(ASTReserved.Result))));
      ASTNode base=create.expression(StandardOperator.Subscript,create.reserved_name(ASTReserved.Result),create.local_name("i"));
      ASTNode claim;
      claim=create.expression(StandardOperator.Perm,
            create.dereference(base,"item")
            ,create.reserved_name(ASTReserved.FullPerm));
      cb.ensures(create.starall(guard, claim, decl));
      DeclarationStatement args[]=new DeclarationStatement[]{create.field_decl("len",create.primitive_type(Sort.Integer))};
      res.add_dynamic(create.method_decl(result_type,cb.getContract(), "new_array_"+t, args,null));
    }
    for(Type t:new_array){
      Type result_type;
      result_type=create.primitive_type(Sort.Option,
          create.primitive_type(Sort.Sequence,
              create.primitive_type(Sort.Cell,rewrite(t))));
      ContractBuilder cb=new ContractBuilder();
      cb.ensures(create.expression(StandardOperator.NEQ,
          create.reserved_name(ASTReserved.Result),
          create.reserved_name(ASTReserved.OptionNone)
          ));
      ASTNode Result=create.expression(StandardOperator.OptionGet,create.reserved_name(ASTReserved.Result));
      cb.ensures(create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,Result),
          create.local_name("len")));
      DeclarationStatement decl=create.field_decl("i",create.primitive_type(Sort.Integer));
      ASTNode guard=and(lte(constant(0),create.local_name("i")),
          less(create.local_name("i"),create.expression(StandardOperator.Size,Result)));
      ASTNode base=create.expression(StandardOperator.Subscript,Result,create.local_name("i"));
      ASTNode claim;
      claim=create.expression(StandardOperator.Perm,
            create.dereference(base,"item")
            ,create.reserved_name(ASTReserved.FullPerm));
      cb.ensures(create.starall(guard, claim, decl));
      DeclarationStatement args[]=new DeclarationStatement[]{create.field_decl("len",create.primitive_type(Sort.Integer))};
      res.add_dynamic(create.method_decl(result_type,cb.getContract(), "new_array_some_"+t, args,null));
    }
    new_array=null;
    result=res;
  }

}

