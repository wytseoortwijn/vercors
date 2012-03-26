// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.Origin;
import hre.ast.TrackingTree;

import java.io.*;
import java.util.*;

import vct.col.ast.*;
import vct.util.*;

/**
 * This class contains a parser for the output of the Chalice tool.
 * 
 * @author sccblom
 *
 */
public class ChaliceReport extends hre.util.TestReport {

  private boolean boogie_started;
  private boolean boogie_completed;
  
  public ChaliceReport(InputStream stream,TrackingTree tree) throws IOException {
    //tree.print("");
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
        String parts[]=line.substring(colon+2).split("[0-9]+[.][0-9]+");
        System.out.printf("error at %s: %s",origin,parts[0]);
        int current=colon+2+parts[0].length();
        for(int i=1;i<parts.length;i++){
          int end=line.indexOf(parts[i],current);
          dot=line.indexOf(".",current);
          line_no=Integer.parseInt(line.substring(current,dot));
          col_no=Integer.parseInt(line.substring(dot+1,end));
          Origin msg_origin=tree.getOrigin(line_no,col_no);
          //System.out.printf("[%d.%d/%s]%s",line_no,col_no,msg_origin,parts[i]);
          System.out.printf("%s%s",msg_origin,parts[i]);
          current=end+parts[i].length();
        }
        System.out.println("");
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
  }

}


