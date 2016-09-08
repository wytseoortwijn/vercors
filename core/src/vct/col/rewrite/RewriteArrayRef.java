package vct.col.rewrite;

import java.util.HashSet;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.Type;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;

public class RewriteArrayRef extends AbstractRewriter {

	public RewriteArrayRef(ProgramUnit source) {
	  super(source);
  }
	
  private HashSet<Type> new_array;

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
    new_array=new HashSet<Type>();
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

