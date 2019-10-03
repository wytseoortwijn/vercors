package vct.col.ast.stmt.decl

import vct.col.ast.generic.ASTNode

import scala.collection.JavaConverters._
import vct.col.ast.util.ASTVisitor
import vct.col.util.{ASTMapping, ASTMapping1, VisitorHelper}
import vct.util.ClassName

import scala.collection.mutable.ArrayBuffer

/**
 * @author sccblom, whmoortwijn
 * @note We may refactor the three mutable buffers if we first refactor `CheckHistoryAlgebra`.
 */
case class AxiomaticDataType(override val name:String, val parameters:List[DeclarationStatement]) extends ASTDeclaration(name) with VisitorHelper {
  require(parameters != null, "The list of parameters is null")

  /** Constructs a new ADT from Java constructs */
  def this(name:String, pars:Array[DeclarationStatement]) = this(name, pars.toList)

  /** Provides a Java wrapper (as an `java.util.List`) for the list of parameters. */
  def parametersJava = parameters.asJava

  private val axioms = new ArrayBuffer[Axiom]()
  private val constructors = new ArrayBuffer[Method]()
  private val mappings = new ArrayBuffer[Method]()

  def axiomsJava = axioms.toIterable.asJava
  def constructorsJava = constructors.toIterable.asJava
  def mappingsJava = mappings.toIterable.asJava

  def add_map(m:Method) : Unit = {
    m.setFlag(ASTFlags.STATIC, true)
    m.setParent(this)
    mappings += m
  }

  def add_cons(m:Method) : Unit = {
    m.setFlag(ASTFlags.STATIC, true)
    m.setParent(this)
    constructors += m
  }

  def add_axiom(ax:Axiom) : Unit = {
    ax.setParent(this);
    axioms += ax
  }

  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def getDeclName = new ClassName(name)

  override def debugTreeChildrenFields(): Iterable[String] = Seq("parameters")
  override def debugTreePropertyFields(): Iterable[String] = Seq("name")
}
