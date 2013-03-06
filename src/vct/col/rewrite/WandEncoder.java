package vct.col.rewrite;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.util.ASTUtils;
import vct.col.util.WandScanner;

public class WandEncoder extends AbstractRewriter {

	public WandEncoder(ProgramUnit source) {
		super(source);
		WandScanner scanner=new WandScanner(source);
		for(ASTClass cl:source.classes()){
			scanner.visit(cl);
		}
	}
	  public void visit(OperatorExpression e){
		  	
		    switch (e.getOperator()){
		    case Apply:{
		      ASTNode arg1=e.getArg(0);
		      if (arg1.labels()==1){
		        for(NameExpression lbl:arg1.getLabels()){
		          result=create.invokation(create.local_name(lbl.getName()), null, "apply");
		          return;
		        }
		        Warning("weird %s expression",e.getOperator());
		      } else {
		        Abort("bad apply");
		      }
		      break;
		    }
		    case Wand:{
		    	if (e.labels()!=1){
		    		Abort("badly labeled magic wand");
		    	}
		    	String lbl=e.getLabel(0).getName();
		    	String type_name="Wand";
		    	ASTNode res=create.expression(StandardOperator.NEQ,
		    					create.local_name(lbl),create.reserved_name("null"));
		    	ASTNode tmp=create.invokation(create.local_name(lbl), null, "valid");
		    	res=create.expression(StandardOperator.Star,res,tmp);
		    	int count=0;
		    	for(ASTNode n:ASTUtils.conjuncts(e.getArg(0))){
		    		count++;
		    		if (n instanceof MethodInvokation){
		    			MethodInvokation m=(MethodInvokation)n;
		    			type_name+="_"+m.method;
			    		tmp=create.invokation(create.local_name(lbl), null, "get_in_"+count);
			    		tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.object));
			    		res=create.expression(StandardOperator.Star,res,tmp);
		    		} else {
		    			Abort("unexpected clause in magic wand");
		    		}
		    	}
		    	count=0;
    			type_name+="_for";
		    	for(ASTNode n:ASTUtils.conjuncts(e.getArg(1))){
		    		count++;
		    		if (n instanceof MethodInvokation){
		    			MethodInvokation m=(MethodInvokation)n;
		    			type_name+="_"+m.method;
			    		tmp=create.invokation(create.local_name(lbl), null, "get_out_"+count);
			    		tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.object));
			    		res=create.expression(StandardOperator.Star,res,tmp);
		    		} else {
		    			Abort("unexpected clause in magic wand");
		    		}
		    	}
		    	if (in_requires){
		    		currentContractBuilder.given(create.field_decl(lbl,create.class_type(type_name)));
		    	}
		    	if (in_ensures){
		    		currentContractBuilder.yields(create.field_decl(lbl,create.class_type(type_name)));
		    	}
		    	auto_labels=false;
		    	result=res;
		    	return;
		    }
		    default:
		      super.visit(e);
		    }
    }
}
