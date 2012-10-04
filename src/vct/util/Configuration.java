package vct.util;

import hre.config.BooleanSetting;
import hre.config.OptionParser;

public class Configuration {

  public static BooleanSetting keep_temp_files=new BooleanSetting(false);
  public static BooleanSetting detailed_errors=new BooleanSetting(false);
  
  public static void add_options(OptionParser clops){
    clops.add(keep_temp_files.getEnable("keep temporary files"),"keep");
    clops.add(detailed_errors.getEnable("produce detailed error messages"),"detail");
    clops.add(vct.boogie.Main.boogie_location.getAssign("location of boogie binary"),"boogie-tool");
    clops.add(vct.boogie.Main.chalice_location.getAssign("location of chalice binary"),"chalice-tool");
  }

}
