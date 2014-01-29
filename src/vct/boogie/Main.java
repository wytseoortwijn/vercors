// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.MessageOrigin;
import hre.ast.Origin;
import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;
import hre.config.BooleanSetting;
import hre.config.IntegerSetting;
import hre.config.StringSetting;
import hre.io.Message;
import hre.io.ModuleShell;
import hre.io.SplittingOutputStream;
import hre.util.CompositeReport;
import hre.util.TestReport.Verdict;

import java.io.*;
import java.util.*;

import vct.col.ast.*;
import vct.util.*;
import static hre.System.*;

/**
 * This class contains the main procedures of the Boogie/Chalice back ends.
 * 
 * @author Stefan Blom
 *
 */
public class Main {

  public static StringSetting z3_module;
  public static StringSetting boogie_module;
  // The default timeout is set to half an hour, to give Z3 plenty of time yet avoid run-aways. 
  public static IntegerSetting boogie_timeout=new IntegerSetting(1800);
  public static StringSetting chalice_module;
  
  static {
	  String OS=System.getProperty("os.name");
	  if(OS.startsWith("Windows")){
		  z3_module=new StringSetting("z3/3.2");
		  boogie_module=new StringSetting("boogie/2012-06-15");
		  chalice_module=new StringSetting("chalice/2012-06-15");
	  } else {
		  z3_module=new StringSetting("z3/4.3.1");
		  boogie_module=new StringSetting("boogie/2012-10-22");
		  chalice_module=new StringSetting("chalice/2012-11-20");
	  }
  }
  
  /**
   * Generate Boogie code and optionally verify a class.
   * @param arg The class for which code must be generated.
   */
  public static BoogieReport TestBoogie(ProgramUnit arg){
    int timeout=boogie_timeout.get();
    ModuleShell shell=Configuration.getShell(z3_module.get(),boogie_module.get());
    try {
      File boogie_input_file=File.createTempFile("boogie-input",".bpl",shell.shell_dir.toFile());
      boogie_input_file.deleteOnExit();
      final PrintStream boogie_input;
      
      if (vct.util.Configuration.backend_file.get()==null){
        boogie_input=new PrintStream(boogie_input_file);
      } else {
        OutputStream temp=new FileOutputStream(boogie_input_file);
        File encoded_file=new File(vct.util.Configuration.backend_file.get());
        OutputStream encoded=new FileOutputStream(encoded_file);
        boogie_input=new PrintStream(new SplittingOutputStream(temp,encoded));
      }
      TrackingOutput boogie_code=new TrackingOutput(boogie_input);
      BoogiePrinter printer=new BoogiePrinter(boogie_code);
      for(ASTClass cl:arg.classes()){
        if (cl.getDynamicCount()>0 && cl.getStaticCount()>0) {
          throw Failure("mixed static(%d)/dynamic(%d) boogie program.",cl.getStaticCount(),cl.getDynamicCount());
        }  
        printer.print(cl);
      }
      TrackingTree tree=boogie_code.close();
      File boogie_xml_file=File.createTempFile("boogie-output",".xml",shell.shell_dir.toFile());
      boogie_xml_file.deleteOnExit();
      //shell.send("which boogie");
      //shell.send("pwd");
      //shell.send("ls -al");
      shell.send("boogie /timeLimit:%s /xml:%s %s",timeout,boogie_xml_file.getName(),boogie_input_file.getName());
      //shell.send("ls -al");
      shell.send("exit");
      BoogieReport output=new BoogieReport(shell,boogie_xml_file,tree);
      return output;
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
      hre.System.Abort("internal error");
      return null;
    }
  }

  /**
   * Pretty print a Chalice program and optionally verify it.
   * 
   * @param program AST of the Chalice program.
   *
   */
  public static ChaliceReport TestChalice(final ProgramUnit program){
    int timeout=boogie_timeout.get();
    ModuleShell shell=Configuration.getShell(z3_module.get(),boogie_module.get(),chalice_module.get());
    File shell_dir=shell.shell_dir.toFile();
    System.err.println("Checking with Chalice");
    try {
      File chalice_input_file=File.createTempFile("chalice-input",".chalice",shell_dir);
      //if (!vct.util.Configuration.keep_temp_files.get()){
        chalice_input_file.deleteOnExit();
      //}
      final PrintStream chalice_input;
      
      if (vct.util.Configuration.backend_file.get()==null){
        chalice_input=new PrintStream(chalice_input_file);
      } else {
        OutputStream temp=new FileOutputStream(chalice_input_file);
        File encoded_file=new File(vct.util.Configuration.backend_file.get());
        OutputStream encoded=new FileOutputStream(encoded_file);
        chalice_input=new PrintStream(new SplittingOutputStream(temp,encoded));
      }
      final TrackingOutput chalice_code=new TrackingOutput(chalice_input);
      final ChalicePrinter printer=new ChalicePrinter(chalice_code);
      
      for(ASTClass cl:program.classes()){
        if (cl.getStaticCount()>0){
          throw new Error("class "+cl.getName()+" has static entries");
        } else {
          cl.accept(printer);
        }
      }
      
      TrackingTree tree=chalice_code.close();
        //shell.send("which chalice");
        //shell.send("pwd");
        //shell.send("ls -al");
        shell.send("chalice -boogieOpt:timeLimit:%d -noTermination %s",timeout,chalice_input_file.getName());
        //shell.send("ls -al");
        shell.send("exit");
        ChaliceReport output=new ChaliceReport(shell,tree);
        return output;
    } catch (Exception e) {
      Warning("error: ");
      e.printStackTrace();
      return null;
    }
  }

}


