package hre.config;

import static hre.System.*;

public class StringSetting {

  private String value;
  
  public StringSetting(String default_setting){
    value=default_setting;
  }
  
  private class AssignOption extends AbstractOption {
    StringSetting about;
    public AssignOption(StringSetting about,String help){
      super(true,help);
      this.about=about;
    }
    public void pass(String value){
      about.value=value;
    }
  }
  
  public Option getAssign(String help){
    return new AssignOption(this,help);
  }
  public String get(){
    return value;
  }
  
  public void set(String value){
    this.value=value;
  }
}
