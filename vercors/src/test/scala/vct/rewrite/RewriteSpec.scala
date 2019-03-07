package vct.rewrite

import org.scalatest.{FlatSpec, Matchers}
import vct.col.ast.{ASTNode, Type}
import vct.col.rewrite.AbstractRewriter
import vct.col.util.ASTFactory

case class RewriteSpec(rewriter: AbstractRewriter) extends FlatSpec with Matchers with RewriteMatcher {
  protected var create = new ASTFactory

  def ofType(node: ASTNode, t: Type): ASTNode = {
    node.setType(t)
    node
  }
}
