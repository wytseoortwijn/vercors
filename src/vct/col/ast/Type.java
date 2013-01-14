// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.*;

import vct.col.ast.PrimitiveType.Sort;
import static hre.System.*;

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

  public abstract boolean supertypeof(ProgramUnit context, Type t);

  public boolean isInteger() {
    return false;
  }

  public boolean isDouble() {
    return false;
  }

  public boolean isVoid() {
    return false;
  }

  public boolean isPrimitive(Sort fraction) {
    return false;
  }

  public ASTNode zero() {
    Abort("zero unimplemented for %s",getClass());
    return null;
  }

  public boolean comparableWith(Type t2) {
    // TODO: the following is not 100% fool proof.
    // E.g. Void is not comparable to anything...
    return getClass()==t2.getClass();
  }

  public boolean isNull() {
    return false;
  }

}

