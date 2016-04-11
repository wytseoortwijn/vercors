package viper.api;

import java.util.List;

/**
 * 
 * @author Stefan Blom
 *
 * @param <O> Type of objects that represent origins.
 * @param <T> Type of objects that represent types.
 * @param <E> Type of objects that represent expressions.
 * @param <S> Type of objects that represent statements.
 */
public interface SilverStatement<O, T, E, Decl, S> {

  /** Create a statement that inhales a boolean/permission expression. */
  public S inhale(O o,E expr);
  
  /** Create a statement that exhales a permission expression. */
  public S exhale(O o,E expr);

  /** Create a statement that asserts a boolean/permission expression. */
  public S assert_(O o,E expr);

  /** Create a statement that refutes a boolean expression. */
  public S refute(O o,E expr);

  public S fold(O o,E expr);
  
  public S unfold(O o,E expr);
  
  public S new_object(O o,E var,List<String> names,List<T>types);

  /** Assign a value to a field or local variable.
   *  Note that Silver uses different assignment statements for
   *  field and locals, but this can be deduced from the
   *  location expression so a single method suffices.
   */
  public S assignment(O o,E loc, E val);
  
  /** Create a goto statement. */
  public S goto_(O o,String l);
  
  /** Create a target label for a goto statement. */
  public S label(O o,String l);

  /** Create a block of statements. */
  public S block(O o,List<S> stats);
  
  /** Create a while loop. */
  public S while_loop(O o,E cond,List<E> invs,List<Decl> locals,S body);
  
  /** Create a method call. */
  public S method_call(O o,String name,List<E> args,List<E> outs,List<Decl> pars,List<Decl> rets);
  
  /** Create an if-the-else. */
  public S if_then_else(O o,E c,S s1,S s2);

}
