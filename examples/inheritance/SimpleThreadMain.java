// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SimpleThread
//:: tools chalice silicon
//:: verdict Pass

/*
  vct --silver=silicon  SimpleThreadInstance.java SimpleThread.java SimpleThreadMain.java
  vct --chalice SimpleThreadInstance.java SimpleThread.java SimpleThreadMain.java
*/
public class Main {


  public void direct(){
    Instance i=new Instance(7);
    //@ assert i.input==7;
    i.run();
    //@ assert i.input==7;
    //@ open i.postJoin@Instance();
    //@ unfold i.postJoin@Instance();
    //@ assert i.output==8;
  }
  
  public void forkjoin(){
    Instance i=new Instance(7);
    //@ assert i.input==7;
    i.start();
    i.joinWith();
    //@ assert i.input==7;
    //@ open i.postJoin@Instance();
    //@ unfold i.postJoin@Instance();
    //@ assert i.output==8;
  }

}

