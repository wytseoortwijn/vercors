// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.FileOrigin;
import hre.ast.Origin;
import hre.ast.TrackingTree;

import java.io.*;
import java.util.*;

import vct.col.ast.*;
import vct.options.VerCorsToolOptionStore;
import vct.options.VerCorsToolSettings;
import vct.util.*;
import static hre.System.Debug;
import static hre.System.Warning;
import static hre.ast.Context.globalContext;

/**
 * This class contains a parser for the output of the Chalice tool.
 * 
 * @author sccblom
 *
 */
public class ChaliceReport extends hre.util.TestReport {

  private boolean boogie_started;
  private boolean boogie_completed;
  
  public ChaliceReport(InputStream stream,TrackingTree tree){
    try {
      VerCorsToolOptionStore store=VerCorsToolSettings.getOptionStore();
      BufferedReader in=new BufferedReader(new InputStreamReader(stream));
      PrintStream out=new PrintStream("chalice-output.txt");
      String line;
      while((line=in.readLine())!=null){
        out.println(line);
        if (line.equals("")) continue;
        if (line.startsWith("  ")){
          //System.out.println("processing:"+line);
          int dot=line.indexOf(".");
          int colon=line.indexOf(":");
          //System.out.printf("[%s][%s]\n",line.substring(2,dot),line.substring(dot+1,colon));
          int line_no=Integer.parseInt(line.substring(2,dot));
          int col_no=Integer.parseInt(line.substring(dot+1,colon));
          Origin origin=tree.getOrigin(line_no,col_no);
          if (!store.isDetailedErrorsSet()){
            Debug("line is [%s]",line);
            int sentence=line.indexOf(". ",colon);
            String message;
            if (sentence >0){
              message=line.substring(colon+2,sentence+1);
            } else {
              message=line.substring(colon+2);
            }
            message=message.replaceAll(" at [0-9]+[.][0-9]+ "," ");
            Debug("error at %s: %s%n",origin,message);
            globalContext.report("error",origin,message);
          } else {
            ArrayList<String> error=new ArrayList<String>();
            String parts[]=line.substring(colon+2).split("[0-9]+[.][0-9]+");
            error.add(parts[0]);
            //System.out.printf
            Debug("error at %s: %s",origin,parts[0]);
            int current=colon+2+parts[0].length();
            for(int i=1;i<parts.length;i++){
              int end=line.indexOf(parts[i],current);
              dot=line.indexOf(".",current);
              line_no=Integer.parseInt(line.substring(current,dot));
              col_no=Integer.parseInt(line.substring(dot+1,end));
              Origin msg_origin=tree.getOrigin(line_no,col_no);
              //System.out.printf("[%d.%d/%s]%s",line_no,col_no,msg_origin,parts[i]);
              //System.out.printf
              Debug("%s%s",msg_origin,parts[i]);
              error.add(msg_origin+parts[i]);
              current=end+parts[i].length();
            }
            //System.out.println("");
            globalContext.report("error",origin,error);
          }
          continue;
        }
        if (line.startsWith("Boogie program verifier version")){
          boogie_started=true;
          continue;
        }
        if (line.startsWith("Boogie program verifier finished")){
          boogie_completed=true;
          if (line.contains("verified, 0 errors")){
            setVerdict(Verdict.Pass);
          } else {
            setVerdict(Verdict.Fail);
          }
          continue;
        }
        System.err.println("chalice: "+line);
      }
      out.close();
    } catch (Exception e) {
      Warning("unexpected exception %s",e);
      setException(e);
    }
  }
}


