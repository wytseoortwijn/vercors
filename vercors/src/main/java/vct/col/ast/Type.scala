package vct.col.ast

import hre.lang.System.Abort
import scala.collection.JavaConverters._
import vct.col.ast.PrimitiveType.Sort

/**
 * Subclass of ASTNode meant for holding all type expressions.
 * 
 * Types need to be both manipulated in special ways (hence this class)
 * and treated as any AST node (hence we extend ASTNode).
 *  
 * @param args A list of type arguments (e.g. class parameters)
 * @author sccblom, whmoortwijn
 */
abstract class Type(val args:List[ASTNode]) extends ASTNode {
  def this(args:Array[ASTNode]) = this(args.toList)
  def this() = this(List())
  
  /** @return The arguments list as an array (for Java interoperability). */
  def argsToArray = args.toArray
  
  def getArg(i:Int) = args.apply(i)
  def getArgCount = args.size
  def equalSize(t:Type) = false
  
  def isPrimitive(fraction:Sort) = false
  def isBoolean = false
  def isInteger = false
  def isDouble = false
  def isVoid = false
  def isNull = false
  def isIntegerType = false
  def isNumeric = false
  def isResource = false

  def zero : ASTNode = {
    Abort(s"zero is unimplemented for ${getClass()}")
    null
  }
  
  final def apply[T](map:TypeMapping[T]) : T = {
    map.pre_map(this)
    var result = accept_simple(map)
    map.post_map(this, result)
  }
  
  def comparableWith(context:ProgramUnit, t:Type) = {
    if (isNumeric) t.isNumeric
    else equals(t) || supertypeof(context, t) || t.supertypeof(context, this)
  }
  
  /** Yields a comma-separated string of type arguments */
  def argsCommaSeparated = args mkString ","
  
  /**
   * Yields a string "<`a_1,...,a_n`>" of the list `args` of arguments `a_i`, 
   * provided that `args` has at least one element.
   */
  override def toString = args.isEmpty match {
    case false => s"<$argsCommaSeparated>"
    case true => ""
  }
  
  def supertypeof(unit:ProgramUnit, t:Type) : Boolean
  protected def accept_simple[T](map:TypeMapping[T]) : T
}
