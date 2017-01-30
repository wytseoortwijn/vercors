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
 * @author sccblom
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
    Abort("zero unimplemented for %s", getClass())
    null
  }
  
  final def apply[T](map:TypeMapping[T]) : T = {
    map.pre_map(this)
    var result = accept_simple(map)
    map.post_map(this, result)
  }
  
  def comparableWith(context:ProgramUnit, t:Type) = {
    if (isNumeric) t.isNumeric
    else if (equals(t)) true
    else if (supertypeof(context, t)) true
    else if (t.supertypeof(context, this)) true
    else false
  }
  
  def supertypeof(unit:ProgramUnit, t:Type) : Boolean
  protected def accept_simple[T](map:TypeMapping[T]) : T
}
