package hre;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Map.Entry;
import java.lang.System;

public class WinExec {

	public static void main(String args[]){
		Runtime rt=Runtime.getRuntime();
		String home=java.lang.System.getProperty("user.home");
		  for (Entry e:java.lang.System.getProperties().entrySet()){
			  java.lang.System.err.printf("%s=%s%n",e.getKey(),e.getValue());
		  }
		  String vct_home=System.getenv("VCT_HOME");
		  System.out.printf("VerCors tool home is %s%n",vct_home);
		Process p;
		try {
			p = rt.exec("C:\\Windows\\System32\\cmd.exe",
			    new String[0],new File(home+"\\AppData\\Local\\Temp"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return;
		}
		new CopyThread(p.getErrorStream(),java.lang.System.err).start();
		new CopyThread(p.getInputStream(),java.lang.System.out).start();
		PrintStream bash=new PrintStream(p.getOutputStream());
		String path=java.lang.System.getenv("PATH");
		bash.println("set MODULESHOME=C:\\Users\\twente\\vct\\modules");
		bash.println("set Path=C:\\Users\\twente\\vct\\modules\\windows;"+path);
		bash.println("call module use C:/Users/twente/vct/modules/modulefiles");
		bash.println("call module use C:/Users/twente/vct/deps/generic/modules");
		bash.println("call module use C:/Users/twente/vct/deps/Windows/modules");
		bash.println("call module avail");
		bash.println("module load z3");
		bash.println("z3 /smt2 "+vct_home+"\\deps\\input\\test-sat.smt");
		bash.println("module load boogie");
		bash.println("boogie "+vct_home+"\\deps\\input\\test-pass.bpl");
		bash.println("module load chalice");
		bash.println("chalice "+vct_home+"\\deps\\input\\test-pass.chalice");
		bash.println("echo %errorlevel%");
		bash.println("chalice "+vct_home+"\\deps\\input\\test-fail.chalice");
		bash.println("echo %errorlevel%");
//		bash.println("export MOD_BASE=/home/sccblom/sfw");
//		bash.println(". $MOD_BASE/bin/mod_setup.sh");
		//bash.println("echo $PATH");
		//bash.println("module avail");
//		bash.println("/bin/true");
//		bash.println("echo $?");
//		bash.println("/bin/false");
//		bash.println("echo $?");
//		bash.println("module load java");
    //bash.println("java -version");
    //bash.println("set");
    bash.println("exit 37");
		bash.close();
		try {
			int code=p.waitFor();
			java.lang.System.out.printf("exit code %d%n", code);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
