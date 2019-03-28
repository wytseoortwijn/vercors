package hre.lang;

import hre.io.MessageStream;

import java.io.PrintStream;
import java.lang.Thread.UncaughtExceptionHandler;
import java.util.HashMap;
import java.util.Map;

/**
 * This class provides a way of providing feedback.
 */
public class System {
  
  private static Map<String,MessageStream> debug_map;
  
  /**
   * Emit an error message, print stack trace and abort.
   * 
   * This method is meant for internal errors which are fatal
   * and may be reported as bugs.
   * 
   * @param format The formatting of the message.
   * @param args The arguments to be formatted.
   */
  public static void Abort(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.err.printf("%s%n",message);
    Thread.dumpStack();
    throw new HREExitException(1);
  }
  
  /**
   * Emit an error message and abort.
   * 
   * This function is meant to be used for external error conditions,
   * such as bad input.
   */
  public static void Fail(String format,Object...args){
    String prefix="";
    if (where){
      StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
      int idx=2;
      while(stackTraceElements[idx].getMethodName().equals("Fail")){
        idx++;
      }
      String name=stackTraceElements[idx].getClassName();
      int line=stackTraceElements[idx].getLineNumber();
      java.lang.System.err.printf("At line %d of %s:%n",line,name);
      prefix="  ";
    }
    String message=String.format(format,args);
    java.lang.System.err.printf("%s%s%n",prefix,message);
    throw new HREExitException(1);
  }
  
  public static void EnableDebug(String className,PrintStream out,String tag){
    if (debug_map==null){
      debug_map=new HashMap<String,MessageStream>();
    }
    debug_map.put(className,new MessageStream(out,tag));
  }
  
  public static void DisableDebug(String className){
    if (debug_map==null){
      return;
    }
    debug_map.remove(className);
    if (debug_map.size()==0){
      debug_map=null;
    }
  }
  
  /**
   * Emit a debug message if the class calling this method is tagged for debugging.
   * 
   */
  public static boolean Debug(String format,Object...args){
    if (debug_map==null) return false;
    StackTraceElement[] stackTraceElements = Thread.currentThread().getStackTrace();
    int idx=2;
    while(stackTraceElements[idx].getMethodName().equals("Debug")){
      idx++;
    }
    String name=stackTraceElements[idx].getClassName();
    for(;;){
      MessageStream out=debug_map.get(name);
      if (out!=null){
        out.say(format,args);
        return true;
      }
      int lastdot=name.lastIndexOf(".");
      if (lastdot<0) return false;
      name=name.substring(0,lastdot);
    }
  }
  
  private static boolean progress=true;
  
  public static void setProgressReporting(boolean progress){
    System.progress=progress;
  }
  
  /**
   * Emit a progress message, if those messages are enabled.
   */
  public static void Progress(String format,Object...args){
    if (progress){
      String message=String.format(format,args);
      java.lang.System.err.printf("%s%n",message);
    }
  }

  /**
   * Emit an output message.
   */
  public static void Output(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.out.printf("%s%n",message);    
  }
  
  /**
   * Emit a warning message.
   */
  public static void Warning(String format,Object...args){
    String message=String.format(format,args);
    java.lang.System.err.printf("WARNING: %s%n",message);    
  }

  private static boolean where=false;
  
  public static void EnableWhere(boolean b) {
    where=b;
  }
  
  public static Failure Failure(String format,Object...args){
    String message=String.format(format, args);
    java.lang.System.err.printf("FAILURE: %s%n",message);    
    return new Failure(message);
  }

  static {
    //java.lang.System.err.printf("HRE System loaded%n");
    final UncaughtExceptionHandler parent=Thread.getDefaultUncaughtExceptionHandler();
    UncaughtExceptionHandler eh=new UncaughtExceptionHandler(){

      @Override
      public void uncaughtException(Thread t, Throwable e) {
        if (e instanceof HREExitException){
          java.lang.System.exit(((HREExitException) e).exit);
        }
        parent.uncaughtException(t,e);
      }
      
    };
    Thread.setDefaultUncaughtExceptionHandler(eh);
  }
}
