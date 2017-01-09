// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases TestCount
//:: tools silicon
//:: pass TestCount__test_count_1 TestCount__test_count_2 TestCount__test_count_3
//:: fail TestCount__test_count_E1

class TestCount {

  public void test_count_1(){
    //@ seq<boolean> xs = seq<boolean>{ true, false , false, true };
    //@ assert \count(xs,0,0)==0;
  }
  
  public void test_count_2(){
    //@ seq<boolean> xs = seq<boolean>{ true, false , false, true };
    //@ assert \count(xs,0,0)==0;
    //@ assert \count(xs,0,1)==1;
  }
  
  public void test_count_3(){
    //@ seq<boolean> xs = seq<boolean>{ true, false , false, true };
    //@ assert \count(xs,0,0)==0;
    //@ assert \count(xs,0,1)==1;
    //@ assert \count(xs,0,4)==2;
  }
  
  public void test_count_E1(){
    //@ seq<boolean> xs = seq<boolean>{ true, false , false, true };
    //@ assert \count(xs,0,3)==3;
  }

}

