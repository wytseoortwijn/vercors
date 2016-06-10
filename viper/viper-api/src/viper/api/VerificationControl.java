package viper.api;

public interface VerificationControl<O> {

  boolean function(O origin,String name);
  
  boolean predicate(O origin,String name);
  
  boolean method(O origin,String name);
  
  void pass(O origin);
  
  void fail(O origin);
    
}
