package hre.ast;

import java.io.PrintStream;
import java.util.Hashtable;

public class Context {
  private Hashtable<String,FileContext> data=new Hashtable<String,FileContext>();
  
  public void printContext(PrintStream out,FileOrigin o,int context){
    String file=o.getName();
    out.printf("--- %s ---%n",file);
    FileContext fc=data.get(file);
    fc.printContext(out,o,context);
  }
  
  public void add(String file){
    data.put(file,new FileContext(file));
  }
}
