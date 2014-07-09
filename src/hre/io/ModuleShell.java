package hre.io;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static hre.System.Debug;
import static hre.System.Warning;
import static hre.System.Abort;
import static hre.System.Progress;

public class ModuleShell {

  private MessageProcess shell;
  public Path shell_dir;
  
  public MessageProcess getProcess(){
    return shell;
  }
  
  public ModuleShell(Path modules_home,Path ... modules_path) throws IOException{
    shell_dir=Files.createTempDirectory("modsh").toRealPath();
    shell_dir.toFile().deleteOnExit();
    String OS=System.getProperty("os.name");
    Progress("starting shell on %s in %s",OS,shell_dir);
    if(OS.startsWith("Windows")){
        shell=new MessageProcess(shell_dir,"cmd.exe");
        Debug("initializing modules from %s",modules_home);
        shell.send("set MODULESHOME=%s",modules_home);
        String path=System.getenv("PATH");
        shell.send("set Path=%s\\windows;"+path,modules_home);
      } else {
        shell=new MessageProcess(shell_dir,"/bin/bash");
        Debug("initializing modules from %s",modules_home);
        shell.send("export MODULESHOME=%s",modules_home);
        shell.send("module() { eval `tclsh %s/modulecmd.tcl bash $*`; }",modules_home);
      }
    for (Path p : modules_path){
      Debug("using modules in %s",p);
      shell.send("module use %s",p.toString().replace('\\','/'));
    }
  }
  
  public void send(String format,Object ... args){
    Debug("shell> "+format,args);
    shell.send(format,args);
  }

  public Message recv(){
    return shell.recv();
  }

}
