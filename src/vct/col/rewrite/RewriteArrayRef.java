package vct.col.rewrite;

import java.util.ArrayList;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.BindingExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
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

	public RewriteArrayRef(ProgramUnit source) {
	  super(source);
  }

	@Override
	public void visit(ASTClass cl){
		super.visit(cl);
		ASTClass res=(ASTClass)result;
		res.add_dynamic(create.field_decl("Integer_value",create.primitive_type(Sort.Integer)));
		result=res;
	}
	
	@Override
	public void visit(OperatorExpression e){
		switch (e.getOperator()){
		  case Subscript:
		  	Warning("subscript %s",e.getArg(0).getType());
		  	super.visit(e);
			  if (e.getArg(0).getType().isPrimitive(Sort.Array)){
			  	ASTNode res=result;
			  	String field=e.getArg(0).getType().getArg(0).toString()+"_value";
			  	result=create.dereference(res,field);
			  }
			  break;
		  case Length:
		    result=create.expression(StandardOperator.Size,rewrite(e.getArguments()));
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
			result=create.primitive_type(Sort.Sequence,create.class_type("Ref"));
			break;
		  default:
		  	super.visit(t);
		}
	}
	
	@Override
	public void visit(Method m){
	  if (m.kind==Method.Kind.Constructor){
	    result=null;
	  } else {
	    String name=m.getName();
	    int N=m.getArity();
	    if (currentContractBuilder==null) currentContractBuilder=new ContractBuilder();
	    ArrayList<DeclarationStatement> args=new ArrayList();
	    args.add(create.field_decl("this", create.class_type("Ref")));
	    for(DeclarationStatement decl:rewrite(m.getArgs())){
	      args.add(decl);
	    }
	    Contract mc=m.getContract();
	    if (mc!=null){
	      rewrite(mc,currentContractBuilder);
	    }
	    Method.Kind kind=m.kind;
	    Type rt=rewrite(m.getReturnType());
	    Contract c=currentContractBuilder.getContract();
	    currentContractBuilder=null;
	    ASTNode body=rewrite(m.getBody());
	    if (body==null){
	      body=create.block(create.expression(StandardOperator.Assume,create.constant(false)));
	    }
	    result=create.method_kind(kind, rt, c, name, args.toArray(new DeclarationStatement[0]), m.usesVarArgs(), body);
	  }
	}
	  @Override
	  public void visit(MethodInvokation e) {
	    ASTNode object=rewrite(e.object);
	    int N=e.getArity();
	    ASTNode args[]=new ASTNode[N+1];
	    args[0]=create.reserved_name(ASTReserved.This);
	    for(int i=0;i<N;i++){
	      args[i+1]=e.getArg(i).apply(this);
	    }
	    MethodInvokation res=create.invokation(object,rewrite(e.dispatch),e.method,args);
	    res.set_before(rewrite(e.get_before()));
	    res.set_after(rewrite(e.get_after()));
	    result=res;
	  }

	
	@Override
	public void visit(BindingExpression e){
	  if (e.binder==BindingExpression.Binder.STAR){
	    if (e.getDeclCount()!=1) Fail("no rules for more than one declaration");
	    DeclarationStatement decl=e.getDeclaration(0);
	    if (!e.select.isa(StandardOperator.And)) {
	      Fail("select is not a conjunction");
	    }
	    ASTNode left=((OperatorExpression)e.select).getArg(0);
	    ASTNode right=((OperatorExpression)e.select).getArg(1);
	    if (!left.isa(StandardOperator.LTE)
	        ||!right.isa(StandardOperator.LT)
	        ){
	      Fail("not a . <= . && . < . pattern");
	    }
	    ASTNode lower=((OperatorExpression)left).getArg(0);
	    ASTNode var1=((OperatorExpression)left).getArg(1);
	    ASTNode var2=((OperatorExpression)right).getArg(0);
	    ASTNode upper=((OperatorExpression)right).getArg(1);
	    if (!(var1 instanceof NameExpression)
	        ||  !(((NameExpression)var1).getName().equals(decl.getName()))
	        ||  !(var2 instanceof NameExpression)
	        ||  !(((NameExpression)var2).getName().equals(decl.getName()))
	        ){
	      Fail("not a . <= i && i < . pattern");
	    }
	    ASTNode select=create.expression(StandardOperator.Member,rewrite(var1),create.expression(StandardOperator.RangeSeq,rewrite(lower),rewrite(upper)));
	    result=create.binder(e.binder,rewrite(e.result_type),rewrite(e.getDeclarations()), select , rewrite(e.main));
	  } else {
	    result=create.binder(e.binder,rewrite(e.result_type),rewrite(e.getDeclarations()), rewrite(e.select), rewrite(e.main));
	  }
	}
}

