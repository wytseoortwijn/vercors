package vct.col.ast

import hre.ast.Origin
import hre.ast.MessageOrigin
import vct.col.util.VisitorHelper

/**
 * AST node that represents a return statement, that is, either
 * "{@code return;}" if the parameter {@code expression} is "{@code None}", or
 * "{@code return expr;}" if the parameter {@code expression} equals "{@code Some(expr)}".
 * 
 * @param expression The expression that determines the return value.
 */
class ReturnStatement(private[this] val expression:Option[ASTNode]) extends ASTNode with BeforeAfterAnnotations with VisitorHelper {
  /**
   * A block of proof hints to be executed just before
   * evaluating the expression represented by this AST node.
   * But after any argument has been evaluated.
   */
  private[this] var before : Option[BlockStatement] = None
  
  /**
   * A block of proof hints to be executed after the
   * current node has been evaluated.
   */
  private[this] var after : Option[BlockStatement] = None
  
  /**
   * Instantiates a new AST node representing a "{@code return expr;}" statement, where the 
   * parameter {@code node} represents the expression {@code expr}.
   */
  def this(node:ASTNode) = this(Some(node))
  
  /**
   * Instantiates a new AST node representing a "{@code return;}" statement 
   * without an associated expression.
   */
  def this() = this(None)
  
  /**
   * Getter for the "returned" expression, but with Java interoperability (meaning that
   * this getter returns {@code null} whether the expression is {@code None}).
   */
  def getExpression : ASTNode = expression match {
    case Some(expr) => expr
    case None => null
  }
  
  /** 
   *  Helper method used to set the origin of {@code block} if it does not 
   *  have an origin already.
   */
  private[this] def updateOrigin(block:BlockStatement, message:String) = Option(block.getOrigin()) match {
    case None => block.setOrigin(new MessageOrigin(message))
    case Some(o:Origin) => ()
  }
  
  /**
   * Helper method for updating the parent and the origin of a given {@code block}.
   */
  private[this] def updateBlock(block:BlockStatement, originMessage:String) = {
    block.setParent(this); updateOrigin(block, originMessage)
  }
  
  /**
   * Assigns {@code block} to the {@code before} field, provided that {@code element = Some(block)}.
   */
  def set_before(element:Option[BlockStatement]) = element match {
    case Some(block) => { updateBlock(block, "before block"); before = Some(block); this }
    case None => this
  }
  
  /**
   * Assigns {@code block} to the {@code before} field, provided that {@code block} is not {@code null}.
   */
  override def set_before(block:BlockStatement) = set_before(Option(block))
  
  /**
   * Assigns {@code block} to the {@code after} field, provided that {@code element = Some(block)}.
   */
  def set_after(element:Option[BlockStatement]) = element match {
    case Some(block) => { updateBlock(block, "after block"); after = Some(block); this }
    case None => this
  }
  
  /**
   * Assigns {@code block} to the {@code after} field, provided that {@code block} is not {@code null}.
   */
  override def set_after(element:BlockStatement) = set_after(Option(element))
  
  /**
   * Getter for the {@code before} field, but assigns a default 
   * value to {@code before} if it equals "{@code None}".
   */
  override def get_before = before match {
    case None => { set_before(new BlockStatement()); get_before }
    case Some(block:BlockStatement) => block
  }
  
  /**
   * Getter for the {@code after} field, but assigns a default 
   * value to {@code after} if it equals "{@code None}".
   */
  override def get_after = after match {
    case None => { set_after(new BlockStatement()); get_after }
    case Some(block:BlockStatement) => block
  }
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
