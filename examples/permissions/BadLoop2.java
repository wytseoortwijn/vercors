// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases BaddLoop2
//:: tools chalice
//:: verdict Fail
class Counter {
  private int val;
  /*@ requires Perm(val,100) ** n>=0; */
  /*@ ensures Perm(val,100) ** val==\old(val)+n; */
  void incr(int n)
  {
    int tmp=n;
    /*@ loop_invariant val+tmp==\old(val)+n && tmp>=0; */
    while(tmp>0)
    {
      val=val+1;
      tmp=tmp-1;
    }
  }
}

