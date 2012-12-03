package vct.col.ast;

public abstract class ExpressionNode extends ASTNode {

  /** Block of proof hints to be executed just before
   *  evaluating the expression represented by this AST node.
   *  But after any argument has been evaluated.
   */
  private BlockStatement before;
  /** Block of proof hints to be executed after the
   *  current node has been evaluated.
   */
  private BlockStatement after;
  
  public void set_before(BlockStatement block){
    before=block;
    if (block!=null) block.setParent(this);
  }
  public BlockStatement get_before(){
    return before;
  }
  
  public void set_after(BlockStatement block){
    after=block;
    if (block!=null) block.setParent(this);
  }
  public BlockStatement get_after(){
    return after;
  }

}
