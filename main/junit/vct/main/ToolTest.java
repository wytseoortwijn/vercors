package vct.main;

import hre.io.Message;
import hre.io.MessageProcess;
import hre.io.ModuleShell;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.EnumSet;
import java.util.concurrent.Semaphore;

import org.junit.Assume;
import org.junit.Test;

import vct.silver.SilverBackend;
import vct.util.Configuration;
import junit.framework.TestCase;
import static hre.System.Debug;

public class ToolTest extends TestCase {

  protected static Semaphore sem = new Semaphore(Runtime.getRuntime().availableProcessors()/3);

  private EnumSet<Feature> allowed=EnumSet.noneOf(Feature.class);
  private EnumSet<Feature> required=EnumSet.noneOf(Feature.class);
  
  public void allow(Feature ... tests){
    for(Feature test:tests){
      allowed.add(test);
    }
  }
  public void require(Feature ...tests){
    for(Feature test:tests){
      required.add(test);
    }
  }
  
  public void sem_get(Feature ... tests) {
    int count=0;
    for(Feature test:tests){
      Assume.assumeTrue(allowed.isEmpty()||allowed.contains(test));
      if (required.contains(test)) count++;
    }
    Assume.assumeTrue(count==required.size());
    try {
      sem.acquire();
    } catch (InterruptedException e) {
      fail("test interrupted");
      return;
    }
  
  }

  public VCTResult run(String ... args) {
    StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
    int idx=0;
    while(!stackTraceElements[idx].getMethodName().equals("run")){
      idx++;
    }
    idx++;
    String test_name=stackTraceElements[idx].getMethodName();
    System.err.printf("test name is %s%n", test_name);
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
    res.verdict=Verdict.Inconclusive;
    switch(args[0]){
    case "vct":
      if (OS.startsWith("Windows")){
        args[0]=f+"\\windows\\bin\\"+args[0]+".cmd"; //DRB --added
      } else {
        args[0]=f+"/unix/bin/"+args[0]; //DRB --added
      }
      sh=Configuration.getShell();
      res.verdict=null;
      if (CommandLineTesting.savedir.used()){
        Path dir=Paths.get(CommandLineTesting.savedir.get()).toAbsolutePath();
        String ext="";
        if (args[1].startsWith("--silver")){
          ext=".sil";
        } else if (args[1].startsWith("--chalice")) {
          ext=".chalice";
        } else if (args[1].startsWith("--boogie")) {
          ext=".bpl";
        } else if (args[1].startsWith("--dafny")) {
          ext=".dfy";
        }
        args[0]+=" --encoded="+dir+File.separator+test_name+ext;
      }
      if (SilverBackend.silver_module.used()){
        args[0]+=" --silver-module="+SilverBackend.silver_module.get();
      }
      //p=new MessageProcess(args);
      break;
    case "z3":
      sh=Configuration.getShell(vct.boogie.Main.z3_module.get());
      break;
    case "boogie":
      sh=Configuration.getShell(
          vct.boogie.Main.z3_module.get(),
          vct.boogie.Main.boogie_module.get());
      break;
    case "carbon":
      sh=Configuration.getShell(
          vct.boogie.Main.z3_module.get(),
          vct.boogie.Main.boogie_module.get(),
          vct.silver.SilverBackend.silver_module.get());
     
      break;
    case "silicon":
    case "silicon_qp":
      String z3;
      //if (vct.boogie.Main.z3_module.used()){
      //  z3=vct.boogie.Main.z3_module.get();
      //} else {
        z3="z3/4.3.2";
      //}
      sh=Configuration.getShell(
          z3,
          vct.silver.SilverBackend.silver_module.get());
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
      //System.err.printf("shell dir is %s %n", sh.shell_dir);
      for(int i=1;i<args.length;i++){
        if (args[i].startsWith("/") && new File(args[i]).isFile()){
          Path path=sh.shell_dir.relativize(Paths.get(args[i]));
          args[i]=path.toString();
          //System.err.printf("relative argument is %s %n", args[i]);
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
    }
    for(;;){
      Message msg=p.recv();
      if (msg==null){
        fail("unexpected null message");
      }
      if (msg.getFormat().equals("stderr: %s")||msg.getFormat().equals("stdout: %s")){
        String line=msg.getArgs()[0].toString();
        if (line.matches(".*took.*ms")){
          String split[]=line.split("took|ms");
          res.times.put(split[0].trim(),Integer.parseInt(split[1].trim()));
        }
      }
      res.log.add(msg);
      synchronized(sem){
        System.err.printf(msg.getFormat(), msg.getArgs());
        System.err.println();
      }
      if (msg.getFormat().equals("exit %d")){
        int n=(Integer)msg.getArg(0);
        if (n>0){
          res.verdict=Verdict.Error;
        }
        break;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Pass")){
        if (res.verdict!=null && res.verdict != Verdict.Pass) fail("inconsistent repeated verdict ("+res.verdict+")");
        res.verdict=Verdict.Pass;
      }
      if (((String)msg.getArg(0)).contains("The final verdict is Fail")){
        if (res.verdict!=null && res.verdict != Verdict.Fail) fail("inconsistent repeated verdict ("+res.verdict+")");
        res.verdict=Verdict.Fail;
      }
    }
    if (res.verdict==null) fail("missing verdict");
    synchronized(sem){
      System.err.printf("%s:%n",test_name);
      for (String key:res.times.keySet()){
        System.err.printf("  %s took %d %n",key,res.times.get(key));
      }
    }
    return res;
  }

}
