package vct.col.rewrite;

import vct.col.ast.ProgramUnit;

/**
 * Standardize the representation of programs.
 * 
 * <UL>
 * <LI> Replace assignment expressions used as statements by assignment statements. 
 * </UL>
 * 
 * @author Stefan Blom
 *
 */
public class Standardize extends AbstractRewriter {

  public Standardize(ProgramUnit source) {
    super(source);
  }

}
