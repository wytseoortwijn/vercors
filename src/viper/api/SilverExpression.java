package viper.api;

import java.util.List;
import java.util.Map;

/**
 * 
 * @author Stefan Blom
 *
 * @param <O> Type of objects that represent origins.
 * @param <T> Type of objects that represent types.
 * @param <E> Type of objects that represent expressions.
 */
public interface SilverExpression<O,T,E,Decl> {

  /** Create an integer constant. */
  public E Constant(O o, int i);

  /** Create a boolean constant. */
  public E Constant(O o, boolean b);

  /** Create a <code>null</code> constant. */
  public E null_(O o);

  public E write_perm(O o);
  public E read_perm(O o);
  public E no_perm(O o);

  public E explicit_set(O o,List<E> elems);
  public E explicit_bag(O o,List<E> elems);
  public E explicit_seq(O o,List<E> elems);
  public E empty_set(O o,T t);
  public E empty_bag(O o,T t);
  public E empty_seq(O o,T t);
  public E range(O o, E e1, E e2);
  public E take(O o, E e1, E e2);
  public E drop(O o, E e1, E e2);
  public E size(O o, E e1);
  public E index(O o, E e1, E e2);
  
  public E append(O o, E e1, E e2);
  public E union(O o, E e1, E e2);
  
  public E predicate_call(O o,String name,List<E> args); 
  public E function_call(O o,String name,List<E> args,T rt,List<Decl> pars);
  public E result(O o,T t);
  
  public E domain_call(O o,String name,List<E> args,Map<String,T> dpars,T rt,List<Decl> pars,String domain); 
 
  public E field_access(O o,E e1, E e2);
  public E scale_access(O o,E e1, E e2);
  
  public E unfolding_in(O o,E e1, E e2);
  
  /** Create a node that accesses a field in an object. */
  public E FieldAccess(O o,E obj,String field,T t);
  
  /** Create a node that accesses a local variable.
   *  Note that in Silver arguments and return variables are
   *  considered to be local variables.
   */
  public E local_name(O o,String name, T t);

  /** Create an universal quantification. */
  public E forall(O o,List<Decl> vars,List<List<E>> triggers,E e);
  
  /** Create an existential quantification. */
  public E exists(O o,List<Decl> vars,E e);
  
  public E old(O o, E e1);
  
  /** Create a not equal expression */
  public E neq(O o, E e1, E e2);

  public E eq(O o, E e1, E e2);

  /** Create a greater than expression. */
  public E gt(O o, E e1, E e2);
  
  public E lt(O o, E e1, E e2);

  public E gte(O o, E e1, E e2);
  
  public E lte(O o, E e1, E e2);

  public E seq_contains(O o, E e1, E e2);
  public E any_set_contains(O o, E e1, E e2);
  
  public E mult(O o, E e1, E e2);
  public E div(O o, E e1, E e2);
  public E mod(O o, E e1, E e2);
  public E frac(O o, E e1, E e2);
  public E add(O o, E e1, E e2);
  public E sub(O o, E e1, E e2);
  public E neg(O o, E e1);

  
  public E and(O o, E e1, E e2);
  public E or(O o, E e1, E e2);
  public E implies(O o, E e1, E e2);
  public E not(O o, E e1);
  
  public E cond(O o, E e1, E e2, E e3);

  public E current_perm(O o, E expr);


}
