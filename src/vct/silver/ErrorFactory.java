package vct.silver;

import hre.ast.Origin;
import vct.error.VerificationError;

public class ErrorFactory implements  VerCorsErrorFactory<Origin,VerificationError>{

  @Override
  public VerificationError generic_error(Origin o, String message) {
    if (o!=null){
      o.report("error", message);
    } else {
      System.err.printf("error: %s%n",message);
    }
    return new VerificationError(){};
  }

}
