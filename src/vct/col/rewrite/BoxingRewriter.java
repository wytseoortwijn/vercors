package vct.col.rewrite;

import vct.col.ast.*;

public class BoxingRewriter extends AbstractRewriter {

	public BoxingRewriter(ProgramUnit arg) {
		super(arg);
	}

	
	public void visit(DeclarationStatement decl){
		if (decl.getType() instanceof ClassType){
			ClassType t=(ClassType)decl.getType();
			ClassType bt=create.class_type(t.getName()+"_Ref");
			ASTNode init=create.invokation(bt,null,bt.getName());
			if (decl.getInit()!=null){
				init=create.invokation(init,null,"set",rewrite(decl.getInit()));
			}
			result=create.field_decl(decl.getName(),bt,init);
		} else {
			super.visit(decl);
		}
	}
}
