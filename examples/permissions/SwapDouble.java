// -*- tab-width:2 ; indent-tabs-mode:nil -*-
// vct --chalice SwapDouble.java
public class SwapDouble {

  double F;
  double G;
  /*@ requires Perm(F,100) ** Perm(G,100);
      ensures Perm(F,100) ** Perm(G,100);
      ensures F == \old(G) && G == \old(F);
   */
  void n()
  {
    double tmp;
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

