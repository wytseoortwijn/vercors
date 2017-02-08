package vct.col.ast

import vct.col.util.VisitorHelper
import vct.util.ClassName

/**
 * AST node that represents a declaration statement, e.g. "{@code int test := 2+4;}". 
 * 
 * @param _name The name of the declared variable, e.g. "{@code test}".
 * @param _type The type of the declared variable, e.g. "{@code int}".
 * @param init The expression that determines the (initial) value of the declared variable, e.g. "{@code 2+4}".
 */
class DeclarationStatement(private[this] val _name:String, private[this] val _type:Type,private[this] val init:ASTNode) extends ASTDeclaration(_name) with VisitorHelper {
  /**
   * Initialises a new AST node that represents a declaration statement without 
   * initial value, e.g. "{@code int test;}".
   * 
   * @param name The name of the declared variable, e.g. "{@code test}".
   * @param t The type of the declared variable, e.g. "{@code int}".
   */
  def this(name:String, t:Type) = this(name, t, null)
  
  /** Yields the declaration type */
  override def getType() = _type

  def getInit() = init
  def init():ASTNode = init

  /** Yields the full name of the declared variable (including the package name). */
  override def getDeclName() = {
    hre.lang.System.Debug("%s.%s", packageName, name)
    new ClassName(packageName, name)
  }
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
