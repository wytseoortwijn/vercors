package col.lang;

import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Lock;

public class Object implements Runnable {

  private Lock lock=new ReentrantLock();
  private boolean locked=false;
  
  public void lock(){
    lock.lock();
    if (locked) {
      throw new Error("illegal attempt to relock non-reentrant lock");
    }
    locked=true;
  }

  public void unlock(){
    lock.lock();
    if (!locked) {
      throw new Error("illegal attempt to unlock while not holding the lock");
    }
    locked=false;
    lock.unlock();
    lock.unlock();
  }
  
  private volatile Thread t;
  
  public synchronized void fork(){
    if (t==null){
      t=new Thread(this);
      t.start();
    } else {
      throw new Error("task has already been forked");
    }
  }
  
  public void join(){
    if (t==null){
      throw new Error("tasks must be forked before they can be joined");
    } else {
      try {
        t.join();
      } catch (InterruptedException e) {
        throw new Error("unexpected interruption of join");
      }
    }
  }
  
  public void run(){
    throw new Error("illegal attempt to fork a thread for a non-runnable object");
  }

}
