package hre;

public class System {
  
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
 
}
