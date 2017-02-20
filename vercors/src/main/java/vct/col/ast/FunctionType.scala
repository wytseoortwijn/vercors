package vct.col.ast

import hre.lang.System.Abort
import vct.col.util.VisitorHelper

/**
 * AST node representing function types (`T_0*...*T_n -> T`), where `params` is the
 * list of parameter types (`T_0,...,T_n`) and `result` the return type (`T`).
 * 
 * @author sccblom, whmoortwijn
 */
case class FunctionType(val params:List[Type], val result:Type) extends Type with VisitorHelper {
  if (result == null) Abort("function types should have a result type")
  
  /** Constructs a new function type from an array of input parameter types */
  def this(params:Array[Type], result:Type) = this(params.toList, result)
  
  /** Yields the arity of the function type */
  def arity = params.length
  
  /** Yields the type of the `i`-th parameter */
  def param(i:Int) = params(i)
  
  override def equals(other:Any) = other match {
    case FunctionType(pars, res) => params == pars && result == res
    case _ => false
  }
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
  override def supertypeof(context:ProgramUnit, otherType:Type) = false
  override val zero = null
}
