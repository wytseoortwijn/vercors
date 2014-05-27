package vct.main;

import hre.io.Message;
import hre.io.MessageProcess;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
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
    ClassLoader loader=Configuration.class.getClassLoader();
    URL url=loader.getResource("vct/util/Configuration.class");
    File f=new File(url.getFile());
    for(int i=0;i<5;i++) f=f.getParentFile();
    System.err.printf("home is %s%n", f);
    String OS=System.getProperty("os.name");
    String vct;
    if (OS.startsWith("Windows")){
      vct=f+"/windows/bin/";
    } else {
      vct=f+"/unix/bin/";
    }
    args[0]=vct+args[0];
    for(int i=1;i<args.length;i++){
      if (args[i].startsWith("//")){
        args[i]=f+args[i].substring(1);
      }
    }
    MessageProcess p=new MessageProcess(args);
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
