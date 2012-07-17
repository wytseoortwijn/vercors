package hre.ast;

import java.io.PrintStream;
import java.text.Format;
import java.util.ArrayList;
import java.util.Hashtable;

public class Context {
  
  public static Context globalContext=new Context();
  public int linesBefore=2;
  public int linesAfter=2;
  
  
  private Hashtable<String,FileContext> data=new Hashtable<String,FileContext>();
  
  public void printContext(PrintStream out,FileOrigin o,int before,int after){
    String file=o.getName();
    FileContext fc=data.get(file);
    if (fc==null){
      System.out.println("=========================================");
      System.out.printf("error at %s: ",o);
    } else {
      out.printf("=== %-30s ===%n",file);
      fc.printContext(out,o,before,after);
      int N=8+file.length();
      System.out.println("-----------------------------------------");
    }
  }
  
  public void add(String file){
    data.put(file,new FileContext(file));
  }
  public void report(String level, Origin origin, Iterable<String> message) {
    if (origin instanceof FileOrigin){
      printContext(System.out,(FileOrigin)origin,linesBefore,linesAfter);     
    } else {
      System.out.println("=========================================");
      System.out.printf("error at %s: ",origin);
    }
    for(String line:message){
      System.out.printf("  %s%n",line);
    }
    System.out.println("=========================================");
  }
  public void report(String level, Origin origin, String ... message) {
    ArrayList<String> list=new ArrayList<String>();
    for(String line:message) list.add(line);
    report(level,origin,list);
  }
}
