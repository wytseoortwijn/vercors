// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases BoogieWithGlobals
//:: tools boogie
//:: options --infer-modifies

/* run with: vct --boogie --infer-modifies BoogieWithGlobals.java */

public class BoogieWithGlobals {

  static int x;
  static int y;
  
  /*@
    requires  true;
    ensures   x==\old(x)+\old(y);
  @*/
  static void add(){
    x=x+y;
  }

}


