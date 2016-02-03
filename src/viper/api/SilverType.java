package viper.api;

/**
 * Factory API for Silver types.
 * 
 * @author Stefan Blom
 *
 * @param <T> Type of objects that represent types.
 */
public interface SilverType<T> {

  /** Create an integer type. */
  public T Int();
  
  /** Create a boolean type. */
  public T Bool();
  
  /** Create a fractional permission type. */
  public T Perm();
  
  /** Create a reference type. */
  public T Ref();
  
  /** Create a list type. */
  public T List(T t);
  
  /** Create a bag or multi-set type. */
  public T Bag(T t);
  
  /** Create a set type. */
  public T Set(T t);
  
  /** Create a domain type. */
  public T domain_type(String name); 

}
