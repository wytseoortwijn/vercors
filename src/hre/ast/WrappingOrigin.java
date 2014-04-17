package hre.ast;

public interface WrappingOrigin extends Origin {

  public WrappingOrigin wrap(Origin other);
  
}
