// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases TestFloat
//:: tools silicon
//:: pass Global__TestFloat_main TestFloat__add TestFloat__prefixsum

class TestFloat {

  public static void main(String args[]){
    float a,b,c,d;
    
    a=(float)1;
    b=(float)2;
    c=a+b;
    d=b+a;
    
    //@ assert c == d;
    
    /*@
      seq<float> s=seq<float>{};
      
      //assert \sum(s)==((float)0);
    */
  }

  /*@
    given seq<float> vals;
    invariant a!=null ** (a.length == |vals|);
    invariant (\forall* int i; 0 <= i && i < a.length;PointsTo(a[i],1/2,vals[i]));
    ensures \result == \sum(vals,0,a.length);
  @*/
  public float add(float a[]){
    int k=0;
    float res=(float)0;
    //@ loop_invariant 0 <= k && k <= a.length;
    //@ loop_invariant \sum(vals,0,k) == res;
    while(k<a.length){
      res=res+a[k];
      k=k+1;
    }
    return res;
  }

  /*@
    given seq<float> vals;
    invariant a!=null ** (a.length == |vals|);
    invariant b!=null ** (a.length == b.length);
    invariant (\forall* int i; 0 <= i && i < a.length;PointsTo(a[i],1/2,vals[i]));
    invariant (\forall* int i; 0 <= i && i < a.length;Perm(b[i],1));
    ensures (\forall int i ; 0 <= i && i < b.length ; b[i] == \sum(vals,0,i));
  @*/
  public void prefixsum(float a[],float b[]){
    int k=0;
    float res=(float)0;
    //@ loop_invariant 0 <= k && k <= a.length;
    //@ loop_invariant \sum(vals,0,k) == res;
    //@ loop_invariant (\forall int i ; 0 <= i && i < k ; b[i] == \sum(vals,0,i));
    while(k<a.length){
      b[k]=res;
      res=res+a[k];
      k=k+1;
    }
  }
 
}

