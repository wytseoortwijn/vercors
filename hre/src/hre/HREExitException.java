package hre;

public class HREExitException extends Error {
  
  public final int exit;
  
  public HREExitException(int val){
    super("exit["+val+"]");
    exit=val;
  }

}
