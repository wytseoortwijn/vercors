// -*- tab-width:4 ; indent-tabs-mode:nil -*-
//:: cases DuplicateFieldName
//:: tools silicon
//:: verdict Pass

public class A {
  int i;

  public void main() {
    B b = new B();

    b.testA()/*@ with {a = 9;} @*/;
    b.testI()/*@ with {i = 9;} @*/;
  }
}

class B {
  /*@
    given int a;
  @*/
  public void testA() {
  }

  /*@
    given int i;
  @*/
  public void testI() {
  }
}
