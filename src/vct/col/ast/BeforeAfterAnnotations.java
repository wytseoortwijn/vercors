package vct.col.ast;

public interface BeforeAfterAnnotations {

  public void set_before(BlockStatement block);
  
  public BlockStatement get_before();
  
  public void set_after(BlockStatement block);
  
  public BlockStatement get_after();

}
