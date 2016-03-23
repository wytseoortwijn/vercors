// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SwapLong
//:: tools chalice
//:: verdict Fail

public class SwapLong {

  long F;
  long G;
  /*@ requires Perm(F,100) ** Perm(G,100);
      ensures Perm(F,100) ** Perm(G,100);
      ensures F == \old(G) && G == \old(F);
   */
  void n()
  {
    long tmp;
    tmp = F;
    F = G;
    G = tmp;
  }


  /*@ requires Perm(F,100) ** Perm(G,100);
      ensures Perm(F,100) ** Perm(G,100);
      ensures F == \old(F) && G == \old(G);
   */
  void twice()
  {
    n();
    n();
  }
  
  /*@ requires Perm(F,100) ** Perm(G,100);
      ensures Perm(F,100) ** Perm(G,100);
      ensures F == \old(F) && G == \old(G);
   */
  void wrong()
  {
    n();
  }

}

