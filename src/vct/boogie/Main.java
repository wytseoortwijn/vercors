// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.MessageOrigin;
import hre.ast.Origin;
import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;

import java.io.*;
import java.util.*;

import vct.col.ast.*;
import vct.options.VerCorsToolOptionStore;
import vct.options.VerCorsToolSettings;
import vct.util.*;

/**
 * This class contains the main procedures of the Boogie/Chalice back ends.
 * 
 * @author Stefan Blom
 *
 */
public class Main {

  /**
   * Generate Boogie code and optionally verify a class.
   * @param cl The class for which code must be generated.
   * @param check If true, execute boogie with the generated code as input.
   * @param boogie Location of the Boogie binary.
   */
  public static BoogieReport TestBoogie(ASTClass cl){
    VerCorsToolOptionStore store=VerCorsToolSettings.getOptionStore();
    int timeout=store.getTimeOut();
    String boogie=store.getBoogieTool();
    try {
      if (cl.getDynamicCount()>0 && cl.getStaticCount()>0) {
        throw new Error("mixed static/dynamic boogie program.");
      }
      PrintStream boogie_input=new PrintStream("boogie-input.bpl");
      TrackingOutput boogie_code=new TrackingOutput(boogie_input);
      InputStream pre_s=ClassLoader.getSystemResourceAsStream("vct/boogie/boogie-prelude.bpl");
      if (pre_s==null) throw new Error("missing boogie-prelude.bpl");
      BufferedReader pre=new BufferedReader(new InputStreamReader(pre_s));
      Origin origin=new MessageOrigin("Boogie Prelude");
      boogie_code.enter(origin);
      for(;;) {
        String line=pre.readLine();
        if (line==null) break;
        boogie_code.println(line);
      }
      boogie_code.leave(origin);
      pre.close();
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
   * @param check If true, the verifier must be executed.
   * @param chalice Location of the Chalice verifier.
   *
   */
  public static void TestChalice(ASTClass program,boolean check,String chalice){
    System.err.println("Checking with Chalice");
    if (program.getDynamicCount()>0) throw new Error("chalice program with dynamic top level.");
    try {
      final PrintStream chalice_input=new PrintStream("chalice-input.chalice");
      final TrackingOutput chalice_code=new TrackingOutput(chalice_input);
      final ChalicePrinter printer=new ChalicePrinter(chalice_code);
      
      int N=program.getStaticCount();
      for(int i=0;i<N;i++){
        ASTNode tmp=program.getStatic(i);
        if (!(tmp instanceof ASTClass)){
          throw new Error("unexpected entity: "+tmp.getClass());
        }
        ASTClass class_def=(ASTClass)tmp;
        if (class_def.getStaticCount()>0){
          throw new Error("class "+class_def.getName()+" has static entries");
        }
        class_def.accept(printer);
      }
      TrackingTree tree=chalice_code.close();
      if (check){
        if (chalice==null) throw new Error("please set location of chalice binary");
        Process child = Runtime.getRuntime().exec(chalice+" chalice-input.chalice");
        ChaliceOutput output=new ChaliceOutput(child.getInputStream(),tree);
        int result=child.waitFor();
        if (result!=0) throw new Exception("unexpected exit code "+result);
      }
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
    }
  }

}


