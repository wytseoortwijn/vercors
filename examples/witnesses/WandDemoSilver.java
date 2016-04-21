// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases WandDemoSilver
//:: tools silicon
/**
  The command line to verify with the VerCors Tool is:
  
  vct --silver=silicon WandDemoSilver.java
  
  The expected result is Pass.
*/
class WandDemo {
  int x;

  /*@
    resource readonly()=Perm(x,1/4);
    resource writeonly()=Perm(x,write);
  @*/
  
  /*@
    requires readonly();
    public pure int get()=\unfolding readonly() \in x;
  */
   
  //@ ensures writeonly();
  WandDemo(){
    //@ fold writeonly();
  }

  /*@
    requires writeonly();
    ensures  readonly();
    ensures  w:(readonly()-*writeonly());
  @*/
  void set(int v){
    //@ unfold writeonly();
    x=v;
    //@ fold readonly();
    /*@
      create {
        unfold readonly();
        use    Perm(this.x,3/4);
        fold   writeonly();
        qed    w:(readonly()-*writeonly());
      }
    @*/
  }


  void demo(){
    //@ witness w:(readonly()-*writeonly());
    WandDemo d=new WandDemo();
    int i=1;
    //@ loop_invariant d.writeonly();
    while(true)
    {
        d.set(i) /*@ then { w=w; } */;
        i=d.get()+d.get();
        //@ apply w:(readonly()-*writeonly());
    }
  }

}

