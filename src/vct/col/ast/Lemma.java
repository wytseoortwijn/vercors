package vct.col.ast;

/**
 * This class represents magic wand proofs, a.k.a. create blocks.
 * 
 * @author Stefan Blom
 *
 */
public class Lemma extends ASTNode {

	public final BlockStatement block;
	
	public Lemma(BlockStatement block) {
		this.block=block;
	}

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }

}
