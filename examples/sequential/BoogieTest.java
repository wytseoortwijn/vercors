// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases BoogieTest
//:: tools boogie
//:: verdict Fail

/* vct --boogie BoogieTest.java

produces

  method abs: Pass
  method bad_incr_1: Fail (assertion violation)
  method good_incr_1: Pass
  method good_incr_2: Pass
  method good_incr_3: Pass
  The final verdict is Fail

*/

public class BoogieTest {

  /*@ requires true;
      ensures \result >= 0 && (\result==x || \result==-x);
    @*/
  public static int abs(int x){
    if(x>0) return x;
    return -x;
  }
  
  /*@ requires true;
      ensures \result==x+1;
  */
  public static int bad_incr_1(int x){
    return x++;
  }

  /*@ requires  true;
      ensures \result==x+1;
  */
  public static int good_incr_1(int x){
    return ++x;
  }

  /*@ requires true;
      ensures \result==x+1;
  */
  public static int good_incr_2(int x){
    int res=x+1;
    return res;
  }

  /*@ requires true;
      ensures \result==x+1;
  */
  public static int good_incr_3(int x){
    int res=good_incr_2(x);
    return res;
  }

}

