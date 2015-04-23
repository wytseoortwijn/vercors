package vct.col.rewrite;

import hre.ast.MessageOrigin;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.ASTClass.ClassKind;

public class ForkJoinCompilation extends AbstractRewriter {

	public ForkJoinCompilation(ProgramUnit arg) {
	  super(arg);
	  create.enter();
    ASTClass global_class=create(new MessageOrigin("fork join class")).ast_class("ForkJoinBase",ClassKind.Plain,null,null,null);
    target().add(global_class);
    global_class.add_dynamic(create.method_decl(
    		create.primitive_type(Sort.Void),
    		null,
    		"fork",
    		new DeclarationStatement[0],
    		null
		));
	  global_class.add_dynamic(create.method_decl(
	  		create.primitive_type(Sort.Void),
	  		null,
	  		"join",
	  		new DeclarationStatement[0],
	  		null
		));
	  create.leave();
  }
	
	@Override
	public void visit(ASTClass cl){
		currentClass=create.ast_class(cl.name, cl.kind,
		    rewrite(cl.parameters),
				new ClassType[]{create.class_type("ForkJoinBase")} , null);
		for (ASTNode item:cl){
			currentClass.add(rewrite(item));
		}
		result=currentClass;
	}
	
	@Override
	public void visit(OperatorExpression e){
		switch(e.getOperator()){
		case Fork:{
			result=create.invokation(rewrite(e.getArg(0)), null, "fork" );
			break;
		}
		case Join:{
			result=create.invokation(rewrite(e.getArg(0)), null, "join" );
			break;
		}
		default:
			super.visit(e);
			break;
		}
	}
}
