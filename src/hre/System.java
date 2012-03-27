package hre;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

class MessageStream {
  private PrintStream out;
  private String tag;
  public MessageStream(PrintStream out,String tag){
    this.out=out;
    this.tag=tag;
  }
  public void say(String format,Object...args){
    String message=String.format(format,args);
    out.printf("%s: %s%n",tag,message);
  }
}

public class System {
  
  private static Map<String,MessageStream> debug_map=new HashMap<String,MessageStream>();
  
  public static void Abort(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.err.printf("%s%n",message);
    Thread.dumpStack();
    java.lang.System.exit(1);
  }
  public static void Fail(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.err.printf("%s%n",message);
    java.lang.System.exit(1);
  }
  
  public static void EnableDebug(String className,PrintStream out,String tag){
    debug_map.put(className,new MessageStream(out,tag));
  }
  
  public static void DisableDebug(String className){
    debug_map.remove(className);
  }
  
  public static void Debug(String format,Object...args){
    StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
    int N=stackTraceElements.length;
    MessageStream out=debug_map.get(stackTraceElements[N-2].getClassName());
    if (out!=null){
      out.say(format,args);
    }
  }
  
  private static boolean progress=true;
  
  public static void setProgressReporting(boolean progress){
    System.progress=progress;
  }
  
  public static void Progress(String format,Object...args){
    if (progress){
      String message=String.format(format,args);
      java.lang.System.err.printf("%s%n",message);
    }
  }

  public static void Output(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.out.printf("%s%n",message);    
  }
  
  public static void Warning(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.err.printf("WARNING: %s%n",message);    
  }
}
