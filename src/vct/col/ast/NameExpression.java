// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

/** Node that can hold every possible kind of defined name.
 * 
 * @author Stefan Blom
 *
 */
public class NameExpression extends ASTNode {

  /** The possible kinds of defined names */
  public static enum Kind {
    /** an unresolved name */
    Unresolved,
    /** argument to a function */
    Argument,
    /** local variable */
    Local,
    /** a field in a class */
    Field,
    /** a method in a class */
    Method,
    /** for the reserved names: null, this, and super. */
    Reserved,
    /** for labels, such as statement labels and predicate labels. */
    Label;
  }
  
  /** The name that this AST node is referencing. */
  private String name;
  /** The kind of the definition being referenced. */
  private Kind kind;
  /** The site where this name was defined. */
  private ASTNode site;
  
  /** Create an unresolved name expression */
  public NameExpression(String name){
    this.name=name;
    kind=Kind.Unresolved;
  }
  /** Create an specific kind of name expression */
  public NameExpression(Kind kind,String name){
    this.name=name;
    this.kind=kind;
  }
  
  public void setKind(Kind kind){
    this.kind=kind;
  }
  public Kind getKind(){
    return kind;
  }
  public ASTNode getSite(){
    return site;
  }
  public void setSite(ASTNode site){
    this.site=site;
  }
  public String getName() { return name; }

  public void accept_simple(ASTVisitor visitor){
    visitor.visit(this);
  }

  public String toString(){ return name; }

  public boolean equals(Object o){
    if (o instanceof NameExpression){
      NameExpression other=(NameExpression)o;
      return name.equals(other.name);
    }
    return false;
  }
  
  public boolean isName(String name) {
    return this.name.equals(name);
  }

  public int hashCode(){
    return name.hashCode();
  }
}

