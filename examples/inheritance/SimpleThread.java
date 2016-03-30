// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SimpleThread
public class Thread {

  //@ public resource joinToken();

  //@ public resource preFork();

  //@ public resource postJoin();
  
  /*@
    requires preFork();
    ensures  postJoin();
  @*/
  public void run();

  /*@
    requires preFork();
    ensures  joinToken();
  @*/
  public final void start();
  
  /*@
    requires joinToken();
    ensures  postJoin();
  @*/
  public final void joinWith();

}

