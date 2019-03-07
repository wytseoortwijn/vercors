package vct.rewrite

import org.scalatest.matchers.{MatchResult, Matcher}
import vct.col.ast.ASTNode
import vct.col.rewrite.ArrayNullValues

trait RewriteMatcher {
  def rewriteTo(node: ASTNode) = RewriteMatcher(node)

  case class RewriteMatcher(right: ASTNode) extends Matcher[ASTNode] {
    override def apply(left: ASTNode): MatchResult = MatchResult(new ArrayNullValues(null).rewrite(left).equals(right), "ASTNode is not rewritten to right ASTNode", "")
  }
}