// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.ast;

/** 
 * This interface allows tracking the origin of
 * AST nodes through transformations to the original file(s).
 */
public interface Origin {
  public void report(String level, Iterable<String> message);
  public void report(String level, String ... message);
}

