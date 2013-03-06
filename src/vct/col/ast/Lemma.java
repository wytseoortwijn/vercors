package vct.col.ast;

public class Lemma extends ASTNode {

	public final BlockStatement block;
	
	public Lemma(BlockStatement block) {
		this.block=block;
	}

	@Override
	protected <T> void accept_simple(ASTVisitor<T> visitor) {
	    visitor.visit(this);
	}

}
