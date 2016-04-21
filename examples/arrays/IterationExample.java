// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases IterationExample
//:: tools silicon
//:: verdict Pass
class Ref {
  /*@
    requires (\forall* int i ; 0 <= i && i < a.length ; Perm(a[i],write));
    ensures  (\forall* int i ; 0 <= i && i < a.length ; Perm(a[i],write));
  @*/
  public void main(int a[]){
    for(int i=0;i<a.length;i++)
    /*@
      requires Perm(a[i],1/2);
      requires i==0 ==> Perm(a[i],1/2);
      requires i < a.length-1 ==> Perm(a[i+1],1/2);
      ensures  Perm(a[i],write);
    @*/
    {
      //@ S1:if(i>0){ recv Perm(a[i],1/2) from S2,1; }
      S2:if (i < a.length-1) {
        a[i]=a[i+1];
        //@ send Perm(a[i+1],1/2) to S1,1;
      }
    }
  }
}
