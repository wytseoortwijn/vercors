package vct.silver;

public interface VerCorsErrorFactory<Origin,Err> {

  public Err generic_error(Origin o,String message);

}
