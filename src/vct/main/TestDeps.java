package vct.main;

import hre.io.Message;
import hre.io.ModuleShell;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static hre.System.Warning;
import static hre.System.Abort;


public class TestDeps {
	  public static void main(String args[]){
		    try {
		      String vct_home=System.getenv("VCT_HOME");
		      if (vct_home==null){
		        Abort("variable VCT_HOME is not set");
		      }
		      String OS=System.getProperty("os.name");
		      Path os_path;
		      if(OS.startsWith("Windows")){
		    	  os_path=Paths.get(vct_home,"deps","Windows","modules");
		      } else if (OS.startsWith("Mac")){
		    	  os_path=Paths.get(vct_home,"deps","Darwin-x86_64","modules");
		      } else {
		    	  os_path=Paths.get(vct_home,"deps","Linux-x86_64","modules");
		      }
		      ModuleShell shell=new ModuleShell(Paths.get(vct_home,"modules"),
		          Paths.get(vct_home,"deps","generic","modules"),os_path);
		      //shell.send("module avail -t");
		      shell.send("module load z3");
		      shell.send("z3 -smt2 %s/deps/input/test-unsat.smt",vct_home);
		      shell.send("z3 -smt2 %s/deps/input/test-sat.smt",vct_home);
		      shell.send("module load boogie");
		      shell.send("module list");
		      shell.send("boogie %s/deps/input/test-fail.bpl",vct_home);
		      shell.send("boogie %s/deps/input/test-pass.bpl",vct_home);
		      shell.send("module load chalice");
		      Path vct_path=shell.shell_dir.relativize(Paths.get(vct_home));
		      shell.send("chalice %s/deps/input/test-fail.chalice",vct_path);
		      shell.send("chalice %s/deps/input/test-pass.chalice",vct_path);
		      shell.send("exit");
		      for(;;){
		        Message res=shell.recv();
		        System.err.printf(res.getFormat(),res.getArgs());
		        System.err.println();
		        if (res.getFormat().equals("exit %d")) break;
		      }
		    } catch (IOException e) {
		      e.printStackTrace();
		    }
		  }

}
