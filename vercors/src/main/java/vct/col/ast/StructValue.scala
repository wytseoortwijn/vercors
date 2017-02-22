package vct.col.ast

import scala.collection.JavaConversions.mapAsScalaMap
import scala.collection.JavaConverters._
import scala.collection.immutable.Map
import vct.col.util.VisitorHelper

case class StructValue(val `type`:Type, val map:Map[String,Integer], val values:List[ASTNode]) extends ExpressionNode with VisitorHelper {
  require(values != null, "The StructValue value list cannot be null")
  require(map != null, "The StructValue map cannot be null")

  def this(t:Type, map:Map[String,Integer], values:Array[ASTNode]) = this(t, map, values.toList)
  def this(t:Type, map:Map[String,Integer]) = this(t, map, Array[ASTNode]())
  def this(t:Type, map:java.util.Map[String,Integer], values:Array[ASTNode]) = this(t, Map(map.toSeq:_*), values.toList)
  def this(t:Type, map:java.util.Map[String,Integer]) = this(t, map, Array[ASTNode]())
  def this(t:Type) = this(t, Map[String,Integer]())
  
  def valuesLength = values.length
  def value(i:Int) = values.apply(i)
  
  /** @note Although `map` is an immutable collection, via `mapJava` it is possible to alter its contents. */
  def mapJava = map.asJava
  
  @deprecated("this method will be removed", "soon")
  def valuesArray = values.toArray

  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
