package silAST.expressions.terms.permission

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}

sealed abstract class PermissionTerm protected[silAST](sl: SourceLocation)
  extends ASTNode(sl) {
  override def toString: String
}

final case class FullPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "write"
}

private[silAST] object FullPermissionTerm {
  val fullPermissionTerm = new FullPermissionTerm()
}

final case class NoPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "none"
}

private[silAST] object NoPermissionTerm {
  val noPermissionTerm = new NoPermissionTerm()
}

final case class PercentagePermissionTerm private[silAST](sl: SourceLocation, percentage: Int)
  extends PermissionTerm(sl) with AtomicNode {
  require(percentage > 0)
  require(percentage < 100)

  override def toString: String = percentage.toString + "%"
}

final case class EpsilonPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "epsilon"
}

private[silAST] object EpsilonPermissionTerm {
  val epsilonPermissionTerm = new EpsilonPermissionTerm()
}

final case class PermissionVariableTerm private[silAST](
                                                         sl: SourceLocation,
                                                         variable: PermissionVariable
                                                         )
  extends PermissionTerm(sl) with AtomicNode {
  override def toString: String = variable.name

}


final case class PermissionAdditionTerm private[silAST](
                                                         sl: SourceLocation,
                                                         t1: PermissionTerm,
                                                         t2: PermissionTerm
                                                         ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "+" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionSubtractionTerm private[silAST](
                                                            sl: SourceLocation,
                                                            t1: PermissionTerm,
                                                            t2: PermissionTerm
                                                            ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "-" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionMultiplicationTerm private[silAST](
                                                               sl: SourceLocation,
                                                               t1: PermissionTerm,
                                                               t2: PermissionTerm
                                                               ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "*" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionIntegerMultiplicationTerm private[silAST](
                                                                      sl: SourceLocation,
                                                                      t1: PermissionTerm,
                                                                      t2: Int
                                                                      ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "+" + t2.toString

  override val subNodes = List(t1)
}
