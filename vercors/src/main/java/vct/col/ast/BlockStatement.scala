package vct.col.ast

import scala.collection.JavaConverters._
import scala.collection.mutable.ArrayBuffer
import vct.col.util.VisitorHelper

/**
 * AST node that represents a block of statements, that is, a sequence
 * "{@code S_1;...;S_n}" of (individual) statements "{@code S_i}".
 */
class BlockStatement extends ASTNode with ASTSequence[BlockStatement] with VisitorHelper {
  /**
   * The list of statements that constitutes the statement block.
   */
  private[this] val statements = new ArrayBuffer[ASTNode]
  
  /** 
   *  Adds a given statement {@code stmt} to this block of statements.
   *  
   *  @param stmt The statement to add.
   *  @return A reference to the resulting statement block.
   */
  def addStatement(stmt:ASTNode) = add(stmt)
  
  /** 
   *  Appends a given AST node "{@code node}", representing a statement, to this block of
   *  statements by applying chaining (see the method {@code chain}). 
   *  
   *  @return A reference to the resulting statement block.
   */
  def append(node:ASTNode) = chain(node)
  
  /** Same as the {@code get} method. */
  def getStatement(i:Int) = get(i)
  
  /** Yields a (copy of the) list of statements in this block. */
  def getStatements = statements.clone.toArray
  
  /** Tests whether the statement block is empty (i.e. does not contain any statements). */
  def isEmpty = statements.isEmpty
  
  /** Prepends the given AST node "{@code node}" to the front of this statement block. */
  def prepend(node:ASTNode) : Unit = prepend(Option(node))
  
  /** Applies the function "{@code f}" to each statement in this block (works the same as the
   *  {@code forEach} method provided by the {@code Iterable} interface, only {@code forEachStmt}
   * 	works nicer with Scala code). */
  def forEachStmt(f:ASTNode=>Unit) = statements.foreach(f)
  
  /** Same as the {@code size} method. */
  def getLength = size
  
  /** 
   *  If {@code element} contains an AST node, the node is added to 
   *  (the back of) this statement block.
   *  
   *  @param element The AST node to insert.
   */
  def add(element:Option[ASTNode]) : Unit = element match {
    case Some(node) => node.setParent(this); statements += node
    case None => ()
  }
  
  /** 
   *  Adds the given AST node "{@code node}" to this block statement, and if {@code node} is
   *  a block statement itself, all {@code node}'s (internal) statements are added instead. 
   *  
   *  @param node The node to "chain" to the block statement
   *  @return A reference to the resulting statement block.
   */
  def chain(node:ASTNode) : BlockStatement = node match {
    case block:BlockStatement => block.forEachStmt { stmt => stmt.clearParent(); add(stmt) }; this
    case other => add(other)
  }
  
  /**
   * Prepends {@code element} to this statement block (i.e. {@code element} is added to the front of the
   * statement list).
   * 
   * @note This method behaves differently from {@code append}, as {@code append} performs "chaining" 
   * (see the {@code chain} method) whereas {@code prepend does not}.
   * @param element The element to prepend.
   */
  def prepend(element:Option[ASTNode]) : Unit = element match {
    case Some(node) => node.setParent(this); statements.+=:(node)
    case None => ()
  }

  /** 
   *  Adds the given AST node "{@code node}" to (the back of) this statement block.
   *  
   *  @return A reference to the resulting statement block.
   */
  override def add(node:ASTNode) = { 
    add(Option(node))
    this 
  }
  
  /** Yields the {@code i}-th statement in this statement block. */
  override def get(i:Int) = statements.apply(i)
  
  /** Yields an (Java) iterator for the statements in this block. */
  override def iterator = statements.toIterator.asJava
  
  /** Yields the number of statements in this statement block. */
  override def size = statements.length
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
}
