// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases Counter
//:: tools chalice
/*
check with vct --chalice Counter.java
*/
class Counter {
  private int val;

  /*@ requires Perm(val,100);
      ensures  Perm(val,100) ** val==\old(val)+1;
   */
  void incr(){
    val = val+1;
  }
  
  /*@ requires Perm(val,100) ** n>=0; */
  /*@ ensures Perm(val,100) ** val==\old(val)+n; */
  void incr_by_n(int n)
  {
    int tmp=n;
    /*@ loop_invariant Perm(val,100); */
    /*@ loop_invariant val+tmp==\old(val)+n ** tmp>=0; */
    while(tmp>0)
    {
      val=val+1;
      tmp=tmp-1;
    }
  }

  /*@ requires Perm(c.val,100) ** n>=0; */
  /*@ ensures Perm(c.val,100) ** c.val==\old(c.val)+n; */
  static void incr_static(Counter c,int n)
  {
    int tmp=n;
    /*@ loop_invariant Perm(c.val,100); */
    /*@ loop_invariant c.val+tmp==\old(c.val)+n ** tmp>=0; */
    while(tmp>0)
    {
      c.incr();
      tmp=tmp-1;
    }
  }

  static void main(){
    Counter c=new Counter();
    assert c.val==0;
  }
}

