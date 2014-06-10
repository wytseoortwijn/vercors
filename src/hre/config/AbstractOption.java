package hre.config;

import static hre.System.*;

public abstract class AbstractOption implements Option {

  private final String help;
  private final boolean arg_needed;
  public AbstractOption(boolean arg, String help){
    arg_needed=arg;
    this.help=help;
  }
  @Override
  public boolean needsArgument() {
    return arg_needed;
  }

  @Override
  public void pass() {
    Abort("illegal call to pass()");
  }

  @Override
  public void pass(String arg) {
    Abort("illegal call to pass(String)");
  }
  
  public String getHelp(){
    return help;
  }
  
  protected boolean used=false;
  
  public boolean used(){
    return used;
  }

}
