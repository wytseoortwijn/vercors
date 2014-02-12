package vct.util;

import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Progress;
import static hre.System.Warning;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;

import hre.config.BooleanSetting;
import hre.config.OptionParser;
import hre.config.StringSetting;
import hre.io.Message;
import hre.io.ModuleShell;
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
   * When a kernel is a single group, some important simplifications can be performed.
   * Thus we have this option that tells the tools to assume gsize==tcount.
   */
  public static final BooleanSetting assume_single_group=new BooleanSetting(false);
  
  /**
   * Enable the resource check during kernel verification.
   */
  public static final BooleanSetting enable_resource_check=new BooleanSetting(true);
  
  /**
   * Enable post check during kernel verification. 
   */
  public static final BooleanSetting enable_post_check=new BooleanSetting(true);
  
  /**
   * Add the VCT library options to the given option parser.
   * @param clops Option parser.
   */
  public static void add_options(OptionParser clops){
    clops.add(keep_temp_files.getEnable("keep temporary files"),"keep");
    clops.add(detailed_errors.getEnable("produce detailed error messages"),"detail");
    clops.add(backend_file.getAssign("filename for storing the back-end input"),"encoded");
    clops.add(vct.boogie.Main.boogie_module.getAssign("name of the boogie environment module"),"boogie-module");
    clops.add(vct.boogie.Main.boogie_timeout.getAssign("boogie time limit"),"boogie-limit");
    clops.add(vct.boogie.Main.chalice_module.getAssign("name of the chalice environment module"),"chalice-module");
//    clops.add(pvl_type_check.getDisable("disable type check in PVL parser"),"no-pvl-check");
    clops.add(assume_single_group.getEnable("enable single group assumptions"),"single-group");
    clops.add(enable_resource_check.getDisable("disable barrier resource check during kernel verification"),"disable-resource-check");
    clops.add(enable_post_check.getDisable("disable barrier post check during kernel verification"),"disable-post-check");
  }

  
  private static Path home;
  private static Path generic_deps;
  private static Path system_deps;
  private static boolean windows;
  static {
    String tmp=System.getenv("VCT_HOME");
    if (tmp==null){
      ClassLoader loader=Configuration.class.getClassLoader();
      URL url=loader.getResource("vct/util/Configuration.class");
      File f=new File(url.getFile());
      //Warning("origin is %s", f);
      for(int i=0;i<5;i++) f=f.getParentFile();
      //Warning("home is %s", f);
      //throw new Error("variable VCT_HOME is not set");
      tmp=f.toString();
    }
    home=Paths.get(tmp).toAbsolutePath();
    if (!home.toFile().isDirectory()){
      throw new Error("VCT_HOME value "+tmp+" is not a directory");
    }
    generic_deps=home.resolve(Paths.get("deps","generic","modules"));
    String OS=System.getProperty("os.name");
    String arch=System.getProperty("os.arch");
    if(windows=OS.startsWith("Windows")){
      system_deps=home.resolve(Paths.get("deps","Windows","modules"));
    } else if (OS.equals("Linux")){
      switch(arch){
      case "x86":
        system_deps=home.resolve(Paths.get("deps","Linux-i386","modules"));
        break;
      case "amd64":
        system_deps=home.resolve(Paths.get("deps","Linux-x86_64","modules"));
        break;
      default:
        throw new Error("unknown "+OS+"architecure: "+arch);
      }
    } else if (OS.equals("Mac OS X")||OS.equals("Darwin")){
      system_deps=home.resolve(Paths.get("deps","Darwin-x86_64","modules"));
    } else {
      throw new Error("The "+OS+" Operating System is not supported");
    }

  }

  /**
   * Get the home of the VerCors Tool installation.
   * @return VerCors Tool home.
   */
  public static Path getHome(){
    return home;
  }

  /**
   * 
   */
  public static ModuleShell getShell(String ... modules){
    ModuleShell shell;
    try {
      //System.err.printf("home: %s%ngeneric:%s%nsystem:%s%n",getHome(),generic_deps,system_deps);
      shell = new ModuleShell(getHome().resolve(Paths.get("modules")),generic_deps,system_deps);
      for (String m:modules){
        shell.send("module load %s",m);
      }
      shell.send("module list -t");
      shell.send("echo ==== 1>&2");
      String line;
      for(;;){
        Message msg=shell.recv();
        if (msg.getFormat().equals("stdout: %s")){
          line=(String)msg.getArg(0);
          continue;
        }
        if (msg.getFormat().equals("stderr: %s")){
          line=(String)msg.getArg(0);
          if (line.equals("Currently Loaded Modulefiles:")) break;
          continue;
        }
        Warning("unexpected shell response");
        Abort(msg.getFormat(),msg.getArgs());
      }
      for(;;){
        Message msg=shell.recv();
        Debug(msg.getFormat(),msg.getArgs());
        String fmt=msg.getFormat();
        if (fmt.equals("stderr: %s")||fmt.equals("stdout: %s")){
          line=(String)msg.getArg(0);
          if (line.contains("echo ====")) continue;
          if (line.contains("====")) break;
          Progress("module %s loaded",line);
          continue;
        } 
        Warning("unexpected shell response");
        Abort(msg.getFormat(),msg.getArgs());
      }
    } catch (IOException e) {
      e.printStackTrace();
      throw new Error(e.getMessage());
    }
    return shell;
  }
}
