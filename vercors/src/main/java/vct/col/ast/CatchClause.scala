package vct.col.ast

class CatchClause(val decl:DeclarationStatement, val block:BlockStatement) {
  def getBlock() = block
  def getDecl() = decl
}