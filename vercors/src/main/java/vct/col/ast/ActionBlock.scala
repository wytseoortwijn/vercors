package vct.col.ast

import scala.collection.JavaConverters._
import vct.col.util.VisitorHelper

class ActionBlock(val history:ASTNode, val fraction:ASTNode, val process:ASTNode, val action:ASTNode, val map:Map[String,ASTNode], val block:ASTNode) extends ASTNode with VisitorHelper {
  def mapAsJava() = map.asJava
  
  /** This constructor is added to retain compatibility with Java (by converting the map to a Scala structure) */
  def this(history:ASTNode, fraction:ASTNode, process:ASTNode, action:ASTNode, map:java.util.Map[String,ASTNode], block:ASTNode) = 
    this(history, fraction, process, action, map.asScala.toMap, block)
  
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
}