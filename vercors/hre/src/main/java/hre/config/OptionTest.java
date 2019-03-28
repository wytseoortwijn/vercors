package hre.config;

import static hre.lang.System.*;

public class OptionTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
    BooleanSetting var=new BooleanSetting(false);
    OptionParser cli=new OptionParser();
    cli.add(var.getEnable("enable x"),'x');
    cli.add(var.getDisable("disable x"),'X');    
    String file[]=cli.parse(args);
    for(int i=0;i<file.length;i++){
      Output("file: %s",file[i]);
    }
    Output("Option is %s",var.get()?"enabled":"disabled");
  }

}
