package vct.col.ast

import java.util.HashMap
import scala.collection.JavaConverters._
import vct.col.util.VisitorHelper

class StructValue(val `type`:Type, private[this] val _map:java.util.Map[String,Integer], val values:List[ASTNode]) extends ExpressionNode with VisitorHelper {
  val map = if (_map != null) new HashMap[String,Integer](_map) else null
  
  def this(t:Type, m:java.util.Map[String,Integer], values:Array[ASTNode]) = this(t, m, values.toList)
  def this(t:Type, m:java.util.Map[String,Integer]) = this(t, m, Array[ASTNode]())
  
  def valuesLength = values.length
  
  @deprecated("this method will be removed", "soon")
  def valuesArray = values.toArray
  
  def value(i:Int) = values.apply(i)
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
