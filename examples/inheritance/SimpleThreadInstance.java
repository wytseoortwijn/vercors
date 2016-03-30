// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SimpleThread
public class Instance extends Thread {

  /*@
    ensures preFork() ** Value(this.input) ** this.input==input;
  @*/
  public Instance(int input){
    this.input=input;
    //@ fold preFork@Instance();
  }

  //@ public resource joinToken()=joinToken@Thread();

  //@ public resource preFork()=Value(input)**Perm(output,write);

  //@ public resource postJoin()=Value(input)**PointsTo(output,write,input+1);
  

  int input;
  int output;
  
  public void run(){
    //@ unfold preFork@Instance();
    output=input+1;
    //@ fold postJoin@Instance();
  }
 
}

