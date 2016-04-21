// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases WandDemo
//:: tools chalice

/**
  The command line to verify with the VerCors Tool is:
  
  vct --chalice WandDemo.java
  
  The expected result is Pass.
*/
class WandDemo {
  int x;

  /*@
    resource readonly()=Perm(x,25);
    resource writeonly()=Perm(x,100);
  @*/
  
  //@ requires readonly();
  public /*@ pure */ int get(){
    //@ unfold readonly();
    return x;
  }
  
  //@ ensures writeonly();
  WandDemo(){
    //@ fold writeonly();
  }

  /*@
    requires writeonly();
    ensures  readonly();
    ensures  wand:(readonly()-*writeonly());
  @*/
  void set(int v){
    //@ unfold writeonly();
    x=v;
    //@ fold readonly();
    /*@
      create {
        unfold readonly();
        use    Perm(this.x,75);
        fold   writeonly();
        qed    wand:(readonly()-*writeonly());
      }
    @*/
  }
  
  void demo(){
    //@ witness wand:(readonly()-*writeonly());
    WandDemo d=new WandDemo();
    int i=1;
    //@ loop_invariant d.writeonly();
    while(true){
        d.set(i) /*@ then { wand=wand; } */;
        i=d.get()+d.get();
        //@ apply wand:(readonly()-*writeonly());
    }
  }
}

