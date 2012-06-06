package hre.util;

import sun.misc.Unsafe;
import static hre.System.*;

public class FieldStack implements FrameControl {
  
  static sun.misc.Unsafe getUnsafe() {
    try {
            java.lang.reflect.Field theUnsafe = sun.misc.Unsafe.class.getDeclaredField("theUnsafe");
            theUnsafe.setAccessible(true);
            return (sun.misc.Unsafe) theUnsafe.get(null);
    } catch (Exception e) {throw new RuntimeException(e);}
  }
  private static final sun.misc.Unsafe unsafe = getUnsafe();

/* 
  private static final Unsafe unsafe = Unsafe.getUnsafe();
  private static final long valueOffset;

  static {
    try {
      valueOffset = unsafe.objectFieldOffset
          (FieldStack.class.getDeclaredField("value"));
    } catch (Exception ex) { throw new Error(ex); }
  }

  private volatile Object value;
*/
  public void enter() {
  }

  public void leave() {
  }

  public void register(Object o,String field){
    long offset=0;
    try {
      offset=unsafe.objectFieldOffset(o.getClass().getDeclaredField(field));
    } catch (SecurityException e) {
      e.printStackTrace();
      Abort("getting field disallowed");
    } catch (NoSuchFieldException e) {
      e.printStackTrace();
      Abort("no field %s in class %s",field,o.getClass());
    }
    System.err.printf("field %s at offset %d%n",field,offset);
  }
  
  public void register(Class cl,String field){
    long offset=0;
    try {
      offset=unsafe.objectFieldOffset(cl.getDeclaredField(field));
    } catch (SecurityException e) {
      e.printStackTrace();
      Abort("getting field disallowed");
    } catch (NoSuchFieldException e) {
      e.printStackTrace();
      Abort("no field %s in class %s",field,cl);
    }
    System.err.printf("field %s at offset %d%n",field,offset);
  }
}
