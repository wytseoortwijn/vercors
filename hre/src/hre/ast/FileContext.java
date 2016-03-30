package hre.ast;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.util.ArrayList;

import static hre.System.*;

public class FileContext {
  private ArrayList<String> list=new ArrayList<String>();
  public FileContext(String file){
    try {
      BufferedReader in=new BufferedReader(new FileReader(file));
      String line;
      while((line=in.readLine())!=null){
        list.add(line);
      }
      in.close();
    } catch (IOException e){
      Abort("Could not create context for %s: %s",file,e);
    }
  }
  
  public void printLines(PrintStream out,int begin,int end){
    for(int i=begin;i<=end;i++){
      out.println(getLine(i));
    }
  }
  
  public String getLine(int i){
    return list.get(i-1);
  }
  public void printContext(PrintStream out,FileOrigin o,int before, int after){
    int N=o.getFirstLine()-before;
    if (N<1) N=1;
    int K=o.getLastLine();
    if (K<0) K=o.getFirstLine();
    K=K+after;
    if (K>list.size()) K=list.size();
    int len=1;
    for(int i=N;i<=K;i++){
      String line=getLine(i);
      if (i==o.getFirstLine()){
        int C=o.getFirstColumn();
        out.printf("    ");
        int k=1;
        while(k<C) {
          out.printf(" ");
          k++;
        }
        out.printf("[");
        if (o.getLastLine()==i){
          C=o.getLastColumn();
        } else {
          C=line.length();
        }
        while(k<=C){
          out.printf("-");
          k++;         
        }
        out.printf("%n");
      }
      out.printf("%4d %s%n",i,line);
      if (line.length()>len) len=line.length();
      if (i==o.getLastLine()){
        int C;
        if (o.getFirstLine() == i){
          C=o.getFirstColumn();
        } else {
          C=1;
        }
        out.printf("     ");
        int k=1;
        while(k<C) {
          out.printf(" ");
          k++;
        }
        C=o.getLastColumn();
        while(k<=C){
          out.printf("-");
          k++;         
        }
        out.printf("]%n");
      }
    }
    //out.print("     0");
    //for(int i=2;i<=len;i+=2) out.printf(" %d",((i/10)%10));
    //out.println();
    //out.print("     0");
    //for(int i=2;i<=len;i+=2) out.printf(" %d",(i%10));
    //out.println();
  }

}
