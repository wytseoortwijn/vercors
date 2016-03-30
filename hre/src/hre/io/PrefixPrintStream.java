// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package hre.io;

import java.io.PrintStream;
import java.util.Stack;

/**
 * PrintStream with a stack of prefixes.
 * 
 * @author <a href="mailto:sccblom@ewi.utwente.nl">Stefan Blom</a>
 *
 */
public class PrefixPrintStream {

  private PrintStream out;
  
  private Stack<String> stack=new Stack<String>();
  
  private String prefix="";

  boolean at_new_line=true;
  
  public PrefixPrintStream(PrintStream out){
    this.out=out;
  }

  public void enter(){
    stack.push(prefix);
  }
  public void leave(){
    prefix=stack.pop();
  }
  public void reenter(){
    prefix=stack.peek();
  }
  public void prefixAdd(String s){
    prefix+=s;
  }

  public PrefixPrintStream printf(String format,Object... args){
    String message=String.format(format,args);
    while(message.length()>0){
      if (at_new_line) out.print(prefix);
      int eol=message.indexOf("\n");
      if (eol>=0) {
        out.print(message.substring(0,eol+1));
        message=message.substring(eol+1);
        at_new_line=true;
      } else {
        out.print(message);
        at_new_line=false;
      }
    }
    return this;
  }
}

