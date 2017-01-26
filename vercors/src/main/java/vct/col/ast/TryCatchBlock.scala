package vct.col.ast

import scala.collection.JavaConverters._
import scala.collection.mutable.ArrayBuffer
import vct.col.util.VisitorHelper

class TryCatchBlock(val main:BlockStatement, val after:BlockStatement, private[this] val _catches:ArrayBuffer[CatchClause]) extends ASTNode with VisitorHelper {
  def this(main:BlockStatement, after:BlockStatement) = this(main, after, new ArrayBuffer[CatchClause]())
  
  def catches = _catches.toIterable.asJava
  
  def catch_clause(decl:DeclarationStatement, block:BlockStatement) : Unit =
    _catches += new CatchClause(decl, block)

  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
