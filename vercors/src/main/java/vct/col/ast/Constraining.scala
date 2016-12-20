package vct.col.ast

import scala.annotation.varargs
import vct.col.util.VisitorHelper

class Constraining(val block:BlockStatement, val vars:Array[NameExpression]) extends ASTNode with VisitorHelper {
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = try { map.map(this, arg) } catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
}