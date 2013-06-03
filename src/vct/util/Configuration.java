package vct.util;

import hre.config.BooleanSetting;
import hre.config.OptionParser;
import hre.config.StringSetting;
/**
 * This class contains the configuration options of the VerCors library.
 * 
 * @author Stefan Blom
 *
 */
public class Configuration {

  /**
   * Global options for controlling the deletion of temporary files.
   */
  public static final BooleanSetting keep_temp_files=new BooleanSetting(false);
  /**
   * Global options for increasing the detail used in error messages.
   * The idea is that normal error messages are independent of the
   * back-end used, while detailed messages may contain details which
   * are specific to a back-end.
   */
  public static final BooleanSetting detailed_errors=new BooleanSetting(false);
  
  /**
   * Set the name of the file that is fed into the back-end verifier.
   * The file is kept after the verification.
   */
  public static final StringSetting backend_file=new StringSetting(null);
  
  /**
   * Control type checking in the PVL parser.
   * By default type checking is enabled, but for multiple file input
   * it must often be disabled as the PVL type checker does not consider libraries.
   */
  public static final BooleanSetting pvl_type_check=new BooleanSetting(true);
  
  /**
   * Add the VCT library options to the given option parser.
   * @param clops Option parser.
   */
  public static void add_options(OptionParser clops){
    clops.add(keep_temp_files.getEnable("keep temporary files"),"keep");
    clops.add(detailed_errors.getEnable("produce detailed error messages"),"detail");
    clops.add(backend_file.getAssign("filename for storing the back-end input"),"encoded");
    clops.add(vct.boogie.Main.boogie_location.getAssign("location of boogie binary"),"boogie-tool");
    clops.add(vct.boogie.Main.boogie_timeout.getAssign("boogie time limit"),"boogie-limit");
    clops.add(vct.boogie.Main.chalice_location.getAssign("location of chalice binary"),"chalice-tool");
    clops.add(pvl_type_check.getDisable("disable type check in PVL parser"),"no-pvl-check");
  }

}
