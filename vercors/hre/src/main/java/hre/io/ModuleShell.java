package hre.io;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;

import static hre.lang.System.Debug;
import static hre.lang.System.Progress;

class RMRF extends Thread {

  class Visitor extends SimpleFileVisitor<Path>{
    
    @Override
    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs)
        throws IOException
    {
        Files.deleteIfExists(file);
        return FileVisitResult.CONTINUE;
    }
    @Override
    public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs)
        throws IOException
    {
            return FileVisitResult.CONTINUE;
    }
    @Override
    public FileVisitResult postVisitDirectory(Path dir, IOException e)
        throws IOException
    {
        Files.deleteIfExists(dir);
        return FileVisitResult.CONTINUE;
    }

    
  }
  
  private final Path path;
  public RMRF(Path p){
    path=p;
  }
  
  public void run(){
    try {
      Files.walkFileTree(path,new Visitor());
    } catch (IOException e) {
      e.printStackTrace();
    }
  }
}
public class ModuleShell {

  public final boolean module_enabled;
  
  private MessageProcess shell;
  public Path shell_dir;
  
  public MessageProcess getProcess(){
    return shell;
  }
  
  public ModuleShell() throws IOException{
    this(false);
  }
  
  private ModuleShell(boolean enable) throws IOException{
    shell_dir=Files.createTempDirectory("modsh").toRealPath();
    Runtime.getRuntime().addShutdownHook(new RMRF(shell_dir));
    String OS=System.getProperty("os.name");
    Progress("starting shell on %s in %s",OS,shell_dir);
    if(OS.startsWith("Windows")){
      shell=new MessageProcess(shell_dir,"cmd.exe");
    } else {
      shell=new MessageProcess(shell_dir,"/bin/bash");
    }
    module_enabled=enable;
  }
  
  public ModuleShell(Path modules_home,Path ... modules_path) throws IOException{
    this(true);
    String OS=System.getProperty("os.name");
    Progress("starting shell on %s in %s",OS,shell_dir);
    Debug("initializing modules from %s",modules_home);
    if(OS.startsWith("Windows")){
        shell.send("set MODULESHOME=%s",modules_home);
        String path=System.getenv("PATH");
        shell.send("set Path=%s\\windows;"+path,modules_home);
      } else {
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
