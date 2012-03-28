// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

/**
 * Subclass of ASTNode meant for holding all type expressions.
 * 
 * Types need to be both manipulated in special ways (hence this class)
 * and treated as any AST node (hence we extend ASTNode).
 *  
 * @author sccblom
 *
 */
public abstract  class Type extends ASTNode {

  public boolean isBoolean() {
    return false;
  }

  public abstract boolean supertypeof(Type t);

  public boolean isInteger() {
    return false;
  }

  public boolean isDouble() {
    return false;
  }

}

