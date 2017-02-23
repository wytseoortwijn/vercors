package vct.col.ast

import hre.lang.System.Debug
import vct.col.util.VisitorHelper

object ClassType {
  val nullType = new ClassType("<<null>>")
  val labelType = new ClassType("<<label>>")
  
  /** Tests whether `name` holds the class type `java.lang.Object`. */
  def isJavaLangObject(name:List[String]) : Boolean =
    name == List("java","lang","Object") || name == List("java_DOT_lang_DOT_Object")
  
  /** Tests whether `name` holds a default type name, for example "null" or "label". */
  def isDefaultName(name:List[String]) : Boolean = 
    name == nullType.names || name == labelType.names
}

/**
 * AST node that represents the type of classes (including their class parameters).
 * 
 * @param names A list of name parts that together constitute the full class name (including package name)
 * @param params A list of AST nodes representing the types of the class parameters
 * @author sccblom, whmoortwijn
 */
case class ClassType(val names:List[String], val params:List[ASTNode]) extends Type(params) with VisitorHelper {
  require(!names.isEmpty, "class types must have a name (at least one name part).")
  
  var definition : ASTDeclaration = null
  
  def this(names:Array[String], args:Array[ASTNode]) = this(names.toList, args.toList)
  def this(names:Array[String]) = this(names, Array[ASTNode]())
  def this(name:String) = this(Array(name))
  
  def getName = this.names.last
  def getNameFull = this.names.toArray
  def getFullName(separator:String) = this.names mkString separator
  def getFullName : String = getFullName(".")
  def setDefinition(decl:ASTDeclaration) = definition = decl

  /**
   * Checks if any of `foundClass`'s super classes (of implemented classes) is a supertype of `this`,
   * in the given program context (`context`).
   */
  private def searchContextForSupertype(unit:ProgramUnit, foundClass:Option[ASTClass]) = foundClass match {
    case None => Debug("class not found."); false
    case Some(cl:ASTClass) => {
      cl.super_classes.exists { parent => searchForSupertype(Some(unit), parent) } ||
      cl.implemented_classes.exists { parent => searchForSupertype(Some(unit), parent) }
    }
  }
  
  /**
   * Checks if the type of this object (i.e. `this`) is a supertype of `ct` in the 
   * given program context (`context`).
   */
  private def searchForSupertype(context:Option[ProgramUnit], ct:ClassType) : Boolean = {
    Debug(s"checking if $this is a supertype of $ct.")
    if (ct.names == this.names) true else context match {
      case Some(unit:ProgramUnit) => searchContextForSupertype(unit, Option(unit.find(ct)))
      case None => Debug("missing program context."); false
    }
  }
  
  /**
   * @note Everything is a supertype of `null` (or any other default name).
   */
  private def searchForSupertype(context:ProgramUnit, other:Type) : Boolean = other match {
    case ct:ClassType => ClassType.isDefaultName(ct.names) || searchForSupertype(Option(context), ct)
    case _ => false
  }
  
  /**
   * Tests whether this class is a supertype of `otherType` (in the given `context`).
   * 
   * @note `java.lang.Object` is a supertype of everything.
   */
  override def supertypeof(context:ProgramUnit, otherType:Type) = 
    ClassType.isJavaLangObject(this.names) || searchForSupertype(context, otherType)
  
  override def equals(obj:Any) = obj match {
    case other:ClassType => this.getFullName == other.getFullName
    case _ => false
  }
  
  override def hashCode = this.getFullName.hashCode
  override def toString = this.getFullName + super.toString
  override def isNull = this.names == ClassType.nullType.names
  override def zero = new NameExpression(ASTReserved.Null)
  
  override def accept_simple[T,A](m:ASTMapping1[T,A], arg:A) = m.map(this, arg)
  override def accept_simple[T](v:ASTVisitor[T]) = handle_standard(() => v.visit(this))
  override def accept_simple[T](m:ASTMapping[T]) = handle_standard(() => m.map(this))
  override def accept_simple[T](m:TypeMapping[T]) = handle_standard(() => m.map(this))
}
