package vct.main;

import hre.io.Message;
import hre.io.MessageProcess;
import hre.io.ModuleShell;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.concurrent.Semaphore;

import vct.util.Configuration;
import junit.framework.TestCase;

public class ToolTest extends TestCase {

  protected static Semaphore sem = new Semaphore(Runtime.getRuntime().availableProcessors());

  public void sem_get() {
    try {
      sem.acquire();
    } catch (InterruptedException e) {
      fail("test interrupted");
      return;
    }
  
  }

  public VCTResult run(String ... args) {
    VCTResult res=new VCTResult();
    Path f=Configuration.getHome();
    System.err.printf("home is %s%n", f);
    String OS=System.getProperty("os.name");
    for(int i=1;i<args.length;i++){
      if (args[i].startsWith("//")){
        args[i]=f+args[i].substring(1);
      }
    }
    MessageProcess p=null;
    ModuleShell sh=null;
    switch(args[0]){
    case "vct":
      if (OS.startsWith("Windows")){
        args[0]=f+"\\windows\\bin\\"+args[0]+".cmd"; //DRB --added
      } else {
        args[0]=f+"/unix/bin/"+args[0]; //DRB --added
      }
      p=new MessageProcess(args);
      break;
    case "z3":
      sh=Configuration.getShell(vct.boogie.Main.z3_module.get());
      break;
    case "boogie":
      sh=Configuration.getShell(
          vct.boogie.Main.z3_module.get(),
          vct.boogie.Main.boogie_module.get());
      break;
    case "chalice":
      sh=Configuration.getShell(
          vct.boogie.Main.z3_module.get(),
          vct.boogie.Main.boogie_module.get(),
          vct.boogie.Main.chalice_module.get());
      /*
        because Chalice assumes that every argument that starts with / is an option,
        we translate absolute path to relative paths.
       */
      for(int i=1;i<args.length;i++){
        if (args[i].startsWith("/") && new File(args[i]).isFile()){
          Path path=sh.shell_dir.relativize(Paths.get(args[i]));
          args[i]=path.toString();
        }
      }
      break;
    default:
      fail("unknown executable: "+args[0]);
      return res;
    }
    if (sh!=null){
      String cmd=args[0];
      for(int i=1;i<args.length;i++){
        cmd+=" "+args[i];
      }
      sh.send("%s",cmd);
      sh.send("exit");
      p=sh.getProcess();
      res.verdict=Verdict.Inconclusive;
    }
    for(;;){
      Message msg=p.recv();
      res.log.add(msg);
      if (msg==null){
        fail("unexpected null message");
      }
      System.err.printf(msg.getFormat(), msg.getArgs());
      System.err.println();
      if (msg.getFormat().equals("exit %d")){
        int n=(Integer)msg.getArg(0);
        if (n>0){
          fail("bad exit status "+n);
        }
        break;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Pass")){
        if (res.verdict!=null) fail("repeated verdict");
        res.verdict=Verdict.Pass;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Fail")){
        if (res.verdict!=null) fail("repeated verdict");
        res.verdict=Verdict.Fail;
      }
    }
    if (res.verdict==null) fail("missing verdict");
    return res;
  }

}
