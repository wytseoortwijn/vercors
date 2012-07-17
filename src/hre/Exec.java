package hre;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import static hre.System.*;

/**
 * Provides methods that can execute an external program.
 * 
 * @author Stefan Blom
 *
 */
public class Exec {
  
	/**
	 * Execute an external program with IO from and to files.
	 * @param stdin Optional input file.
	 * @param stdout File for storing standard output.
	 * @param stderr File for storing standard error.
	 * @param command_line An array of strings comprising the command line.
	 * @return
	 */
  public static int exec(File stdin,File stdout,File stderr,String ... command_line){
    Runtime runtime=Runtime.getRuntime();
    String OS=java.lang.System.getProperty("os.name");
    Warning("OS is %s%n",OS);
    if (OS.startsWith("Windows")){
      File tmp=new File(command_line[0]);
      if (!tmp.exists()){
        command_line[0]=command_line[0]+".bat";
      }
    }
    Process process;
    try {
      process=runtime.exec(command_line);
    } catch (IOException e){
      java.lang.System.err.printf("exec yields %s%n",e);
      return -1;
    }
    CopyThread stdin_copy,stdout_copy,stderr_copy;
    try {
      if (stdin!=null) stdin_copy=new CopyThread(stdin,process.getOutputStream());
      stdout_copy=new CopyThread(process.getInputStream(),stdout);
      stdout_copy.start();
      stderr_copy=new CopyThread(process.getErrorStream(),stderr);
      stderr_copy.start();
    } catch (IOException e){
      java.lang.System.err.printf("IO setup failed %s%n",e);
      return -1;      
    }
    try {
      // wait for process and output.
      int exitcode=process.waitFor();
      stdout_copy.join();
      if (stdout_copy.getError()!=null) {
        hre.System.Abort("stdout error: %s%n",stdout_copy.getError());
      }
      stderr_copy.join();
      if (stderr_copy.getError()!=null) {
        hre.System.Abort("stderr error: %s%n",stderr_copy.getError());
      }
      return exitcode;
    } catch (InterruptedException e){
      process.destroy();
      return -1;
    }
  }

}
