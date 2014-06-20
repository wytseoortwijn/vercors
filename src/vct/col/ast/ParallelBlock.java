package vct.col.ast;

public class ParallelBlock extends ASTNode {

  @Override
  public <T> void accept_simple(ASTVisitor<T> visitor){
    visitor.visit(this);
  }
  @Override
  public <T> T accept_simple(ASTMapping<T> map){
    return map.map(this);
  }
  
  public final Contract contract;
  public final DeclarationStatement decl;
  public final ASTNode count;
  public final BlockStatement block; 
  
  public ParallelBlock(Contract contract,DeclarationStatement decl,ASTNode count,BlockStatement block){
    this.contract=contract;
    this.decl=decl;
    this.count=count;
    this.block=block;
  }

}
