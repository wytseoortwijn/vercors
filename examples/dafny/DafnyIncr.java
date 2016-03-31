// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases DafnySuccess
//:: tools dafny

class Incr {

  /*@
    ensures \result==\old(x)+1;
  @*/
  public int incr(int x){
    return x+1;
  }

  int y;

  /*@
    requires true;
    modifies this;
    ensures y == \old(y)+1;
  @*/
  public void incry(){
    y = y + 1;
  }
}
