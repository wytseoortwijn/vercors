package vct.silver;

import hre.ast.Origin;
import viper.api.VerificationControl;

public class ViperControl implements VerificationControl<Origin> {

  @Override
  public boolean function(Origin origin, String name) {
    return true;
  }

  @Override
  public boolean predicate(Origin origin, String name) {
    return true;
  }

  @Override
  public boolean method(Origin origin, String name) {
    return true;
  }

  @Override
  public void pass(Origin origin) {
    origin.report("result", "pass");
  }

  @Override
  public void fail(Origin origin) {
    origin.report("result", "fail");
  }

}
