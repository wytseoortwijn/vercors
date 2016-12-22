package vct.col.ast

import vct.col.util.VisitorHelper

/**
 * This class represents magic wand proofs, a.k.a. create blocks.
 * 
 * @author Stefan Blom, Wytse Oortwijn
 * @param block The block representing the lemma (for the magic wand proof).
 */
class Lemma(val block:BlockStatement) extends ASTNode with VisitorHelper {
  def getBlock() = block
  override def accept_simple[T,A](map:ASTMapping1[T,A], arg:A) = map.map(this, arg)
  override def accept_simple[T](visitor:ASTVisitor[T]) = try visitor.visit(this) catch { case t:Throwable => handle_throwable(t) }
  override def accept_simple[T](map:ASTMapping[T]) = try map.map(this) catch { case t:Throwable => handle_throwable(t) }
}