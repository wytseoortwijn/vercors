package vct.col.rewrite;

import java.util.ArrayList;

import vct.col.ast.ASTClass;
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
		  	super.visit(e);
			  if (e.getArg(0).getType().isPrimitive(Sort.Array)){
			  	ASTNode res=result;
			  	String field=e.getArg(0).getType().getArg(0).toString()+"_value";
			  	result=create.dereference(res,field);
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
			result=create.primitive_type(Sort.Sequence,create.class_type("Ref"));
			break;
		  default:
		  	super.visit(t);
		}
	}
	
	@Override
	public void visit(Method m){
	  if (m.kind==Method.Kind.Constructor){
	    Warning("discarding constructor");
	    result=null;
	  } else if (m.isStatic()){
	    super.visit(m);
	  } else {
	    String name=m.getName();
	    int N=m.getArity();
	    if (currentContractBuilder==null) currentContractBuilder=new ContractBuilder();
	    ArrayList<DeclarationStatement> args=new ArrayList();
	    //do not add this!
	    //args.add(create.field_decl("this", create.class_type("Ref")));
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

	/*
  @Override
  public void visit(MethodInvokation e) {
    if (e.getDefinition().isStatic()) {
      super.visit(e);
    } else {
      ASTNode object = rewrite(e.object);
      int N = e.getArity();
      ASTNode args[] = new ASTNode[N + 1];
      args[0] = object;
      for (int i = 0; i < N; i++) {
        args[i + 1] = e.getArg(i).apply(this);
      }
      MethodInvokation res = create.invokation(null, rewrite(e.dispatch), e.method, args);
      res.set_before(rewrite(e.get_before()));
      res.set_after(rewrite(e.get_after()));
      result = res;
    }
  }
	*/
	
	@Override
	public void visit(BindingExpression e){
	  if (e.binder==BindingExpression.Binder.STAR || e.binder==BindingExpression.Binder.FORALL){
	    if (e.getDeclCount()!=1){
	      //Fail("no rules for more than one declaration");
          super.visit(e);
          return;
	    }
	    DeclarationStatement decl=e.getDeclaration(0);
	    ASTNode var1;
	    ASTNode lower;
	    ASTNode upper;
	    if (e.select.isa(StandardOperator.And)) {
  	    ASTNode left=((OperatorExpression)e.select).getArg(0);
  	    ASTNode right=((OperatorExpression)e.select).getArg(1);
  	    if (!(left.isa(StandardOperator.LTE)||left.isa(StandardOperator.LT))
  	        ||!right.isa(StandardOperator.LT)
  	        ){
  	      //Fail("not a . <[=] . && . < . pattern");
            super.visit(e);
            return;
  	    }
  	    lower=((OperatorExpression)left).getArg(0);
  	    if (left.isa(StandardOperator.LT)){
  	      if (lower instanceof ConstantExpression){
  	        create.enter();
  	        int v=((IntegerValue)((ConstantExpression)lower).value).value;
  	        lower=create(lower).constant(v+1);
  	        create.leave();
  	      } else {
  	        lower=create.expression(StandardOperator.Plus,lower,create.constant(1));
  	      }
  	    }
  	    var1=((OperatorExpression)left).getArg(1);
  	    ASTNode var2=((OperatorExpression)right).getArg(0);
  	    upper=((OperatorExpression)right).getArg(1);
  	    if (!(var1 instanceof NameExpression)
  	        ||  !(((NameExpression)var1).getName().equals(decl.getName()))
  	        ||  !(var2 instanceof NameExpression)
  	        ||  !(((NameExpression)var2).getName().equals(decl.getName()))
  	        ){
  	      //Fail("not a . <= i && i < . pattern");
            super.visit(e);
            return;
  	    }
	    } else if (e.select.isa(StandardOperator.Member)){
	      var1=((OperatorExpression)e.select).getArg(0);
	      ASTNode right=((OperatorExpression)e.select).getArg(1);
        if (!(var1 instanceof NameExpression)
        ||  !(((NameExpression)var1).getName().equals(decl.getName()))
        ||  !right.isa(StandardOperator.RangeSeq)
        ){
          super.visit(e);
          return;
        }
        lower=((OperatorExpression)right).getArg(0);
        upper=((OperatorExpression)right).getArg(1);
	    } else {
        super.visit(e);
        return;	      
	    }
	    ASTNode main;
	    Hole p=new Hole();
	    Hole ar=new Hole();
	    Hole e1=new Hole();
	    Hole e2=new Hole();
      ASTNode m_idx=create.expression(StandardOperator.Minus,e1,e2);
      ASTNode m_pattern=create.expression(StandardOperator.Perm,create.expression(StandardOperator.Subscript,ar,m_idx),p);
      ASTNode p_idx=create.expression(StandardOperator.Plus,e1,e2);
      ASTNode p_pattern=create.expression(StandardOperator.Perm,create.expression(StandardOperator.Subscript,ar,p_idx),p);
	    if (m_pattern.match(e.main)
	        && e1.get() instanceof NameExpression
	        && e2.get() instanceof ConstantExpression
      ){
        lower=create.expression(StandardOperator.Minus,lower,e2.get());
        upper=create.expression(StandardOperator.Minus,upper,e2.get());
        ASTNode tmp=create.expression(StandardOperator.Subscript,rewrite(ar.get()),rewrite(e1.get()));
        if (ar.get().getType().isPrimitive(Sort.Array)){
          String field=ar.get().getType().getArg(0).toString()+"_value";
          tmp=create.dereference(tmp,field);
        }
	      main=create.expression(StandardOperator.Perm,tmp,rewrite(p.get()));
	    } else if (p_pattern.match(e.main)
          && e1.get() instanceof NameExpression
          && e2.get() instanceof ConstantExpression
      ){
        lower=create.expression(StandardOperator.Plus,lower,e2.get());
        upper=create.expression(StandardOperator.Plus,upper,e2.get());
        ASTNode tmp=create.expression(StandardOperator.Subscript,rewrite(ar.get()),rewrite(e1.get()));
        if (ar.get().getType().isPrimitive(Sort.Array)){
          String field=ar.get().getType().getArg(0).toString()+"_value";
          tmp=create.dereference(tmp,field);
        }
        main=create.expression(StandardOperator.Perm,tmp,rewrite(p.get()));
      } else {
	      main=rewrite(e.main);
	    }
	    ASTNode select=create.expression(StandardOperator.Member,rewrite(var1),create.expression(StandardOperator.RangeSeq,rewrite(lower),rewrite(upper)));
	    result=create.binder(e.binder,rewrite(e.result_type),rewrite(e.getDeclarations()), select , main);
	  } else {
	    result=create.binder(e.binder,rewrite(e.result_type),rewrite(e.getDeclarations()), rewrite(e.select), rewrite(e.main));
	  }
	}

  private ASTNode simplify(ASTNode temp) {
    Hole name=new Hole();
    Hole lower=new Hole();
    Hole upper=new Hole();
    Hole p=new Hole();
    Hole ar=new Hole();
    Hole idx=new Hole();
    ASTNode pattern=create.starall(create.expression(StandardOperator.Member,name,
        create.expression(StandardOperator.RangeSeq,lower,upper)),
        create.expression(StandardOperator.Perm,create.expression(StandardOperator.Subscript,ar,idx),p));
    if (pattern.match(temp)){
      Warning("MATCH!");
    }
    return temp;
  }
  
}

