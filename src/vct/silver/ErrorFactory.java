package vct.silver;

import hre.ast.Origin;
import vct.error.VerificationError;

public class ErrorFactory implements  VerCorsErrorFactory<Origin,VerificationError>{

  @Override
  public VerificationError generic_error(Origin o, String message) {
    o.report("error", message);
    return new VerificationError(){};
  }

}
