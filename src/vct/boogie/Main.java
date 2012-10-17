// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.MessageOrigin;
import hre.ast.Origin;
import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;
import hre.config.BooleanSetting;
import hre.config.StringSetting;
import hre.util.CompositeReport;
import hre.util.TestReport.Verdict;

import java.io.*;
import java.util.*;

import vct.col.ast.*;
import vct.util.*;

/**
 * This class contains the main procedures of the Boogie/Chalice back ends.
 * 
 * @author Stefan Blom
 *
 */
public class Main {

  public static StringSetting boogie_location=new StringSetting("vct-boogie");
  public static StringSetting chalice_location=new StringSetting("vct-chalice");
  
  /**
   * Generate Boogie code and optionally verify a class.
   * @param cl The class for which code must be generated.
   */
  public static BoogieReport TestBoogie(ASTClass cl){
    int timeout=15;
    String boogie=boogie_location.get();
    try {
      if (cl.getDynamicCount()>0 && cl.getStaticCount()>0) {
        throw new Error("mixed static/dynamic boogie program.");
      }
      PrintStream boogie_input=new PrintStream("boogie-input.bpl");
      TrackingOutput boogie_code=new TrackingOutput(boogie_input);
      //InputStream pre_s=ClassLoader.getSystemResourceAsStream("vct/boogie/boogie-prelude.bpl");
      //if (pre_s==null) throw new Error("missing boogie-prelude.bpl");
      //BufferedReader pre=new BufferedReader(new InputStreamReader(pre_s));
      //Origin origin=new MessageOrigin("Boogie Prelude");
      //boogie_code.enter(origin);
      //for(;;) {
      //  String line=pre.readLine();
      //  if (line==null) break;
      //  boogie_code.println(line);
      //}
      //boogie_code.leave(origin);
      //pre.close();
      BoogiePrinter printer=new BoogiePrinter(boogie_code);
      printer.print(cl);
      TrackingTree tree=boogie_code.close();

      if (boogie==null) throw new Error("please set location of boogie binary");
      File boogie_out=File.createTempFile("boogie-out","txt");
      boogie_out.deleteOnExit();
      File boogie_err=File.createTempFile("boogie-err","txt");
      boogie_err.deleteOnExit();
      int res=hre.Exec.exec(null, boogie_out, boogie_err, boogie,"/timeLimit:"+timeout, "/xml:boogie-output.xml","boogie-input.bpl");
      if (res<0){
        hre.System.Abort("boogie execution failed");
      }
      BoogieReport output=new BoogieReport(new FileInputStream(boogie_out),"boogie-output.xml",tree);
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
  public static CompositeReport TestChalice(final ASTClass program){
    String chalice=chalice_location.get();
    CompositeReport report=new CompositeReport();
    System.err.println("Checking with Chalice");
    if (program.getDynamicCount()>0) throw new Error("chalice program with dynamic top level.");
    if (program.getStaticCount()==1){
      ASTNode tmp=program.getStatic(0);
      if (!(tmp instanceof ASTClass)){
        throw new Error("unexpected entity: "+tmp.getClass());
      }
      ASTClass class_def=(ASTClass)tmp;
      if (class_def.isPackage()){
        return TestChalice(class_def);
      }
    }
    try {
      File chalice_input_file;
      if (vct.util.Configuration.backend_file.get()==null){
        chalice_input_file=File.createTempFile("chalice-input",".chalice",new File("."));
        if (!vct.util.Configuration.keep_temp_files.get()){
          chalice_input_file.deleteOnExit();
        }
      } else {
        chalice_input_file=new File(vct.util.Configuration.backend_file.get());
      }

      final PrintStream chalice_input=new PrintStream(chalice_input_file);
      final TrackingOutput chalice_code=new TrackingOutput(chalice_input);
      final ChalicePrinter printer=new ChalicePrinter(chalice_code);
      
      Runnable local=new Runnable(){
        public void run(){find_classes(program);}
        private void find_classes(ASTClass pkg){
          if (pkg.getDynamicCount()>0) throw new Error("package with dynamic entries");
          int N=pkg.getStaticCount();
          for(int i=0;i<N;i++){
            ASTNode tmp=pkg.getStatic(i);
            if (!(tmp instanceof ASTClass)){
              throw new Error("unexpected entity: "+tmp.getClass());
            }
            ASTClass class_def=(ASTClass)tmp;
            if (class_def.isPackage()){
              find_classes(class_def);
            } else if (class_def.getStaticCount()>0){
              throw new Error("class "+class_def.getName()+" has static entries");
            } else {
              class_def.accept(printer);
            }
          }
        }
      };
      local.run();
      
      TrackingTree tree=chalice_code.close();
      if (true){
        if (chalice==null) throw new Error("please set location of chalice binary");
        File chalice_out=File.createTempFile("chalice-out",".txt");
        chalice_out.deleteOnExit();
        File chalice_err=File.createTempFile("chalice-err",".txt");
        chalice_err.deleteOnExit();
        int result=hre.Exec.exec(null, chalice_out, chalice_err,chalice,chalice_input_file.toString());
        ChaliceReport output=new ChaliceReport(new FileInputStream(chalice_out),tree);
        if (vct.util.Configuration.keep_temp_files.get()){
          System.err.printf("Input file was kept as: %s%n",chalice_input_file);
        }
        if (result!=0) {
          output.setVerdict(Verdict.Error);
        }
        report.addReport(output);
      }
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
    }
    return report;
  }

}


