// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import java.util.Map;
import java.util.EnumMap;
import java.util.HashMap;

public enum StandardOperator {

  UPlus(1,"+.","positive"),
  UMinus(1,"-.","negative"),
  Plus(2,"+","addition"),
  Minus(2,"-","subtraction"),
  Mult(2,"x","multiplication"),
  Div(2,"/","division"),
  Mod(2,"%","remainder"),
  BitAnd(2,"&","bitwise and"),
  BitOr(2,"|","bitwise or"),
  BitXor(2,"^","bitwise xor"),
  BitNot(2,"~","bitwise negation"),
  And(2,"/\\","logical and"),
  Or(2,"\\/","logical or"),
  Not(1,"!","negation"),
  Implies(2,"->","logical implication"),
  IFF(2,"<=>","if and only if"),
  EQ(2,"==","equals"),
  NEQ(2,"!=","not equals"),
  GT(2,">","greater than"),
  GTE(2,">=","greater than or equal"),
  LT(2,"<","lesser than"),
  LTE(2,"<=","lesser than or equal"),
  ITE(3,".<|.|>.","if then else"),
  Instance(2,"<:","instance of"),
  Assign(2,":=","assignment"),
  Modify(3,":?=","modifying assignment"),
  PreIncr(1,"++.","increment return new"),
  PreDecr(1,"--.","decrement return new"),
  PostIncr(1,".++","increment return old"),
  PostDecr(1,".--","decrement return old"),
  LeftShift(2,"<<","shift left"),
  RightShift(2,">>","shift right"),
  UnsignedRightShift(2,">>>","signed shift right"),
  Star(2,"*","separating and"),
  Wand(2,"-*","separating implication"),
  Perm(2,"Perm","Fractional acces permission"),
  PointsTo(3,"PointsTo","Fractional access permission and contents"),
  FullAcc(1,"acc(.)","Full access"),
  PartialAcc(2,"acc(.,.)","Partial access based on percentage"),
  Select(2,".","select a member (x.y)"),
  GuardedSelect(2,"->","guarded select"),
  Subscript(2,"[.]","array subscription x[y]"),
  Requires(1,"requires","pre condition in contract"),
  Ensures(1,"ensures","post condition in contract"),
  Fork(1,"fork","start executing the given thread"),
  Join(1,"join","join with the given thread"),
  Lock(1,"lock","lock the given object"),
  Fold(1,"fold","hint that the prover should fold"),
  Unfold(1,"unfold","hint that the prover should unfold"),
  Unlock(1,"unlock","unlock the given object"),
  Assert(1,"assert","assert the argument"),
  HoareCut(1,"/*{ . }*/","cut statement of a Hoare logic proof."),
  Old(1,"old","evaluate argument in old state rather than current state");

  private final int arity;
  private final String description;
  
  StandardOperator(int arity,String afun,String description){
    this.arity=arity;
    this.description=description;
  }
  
  public int arity(){ return arity; }
  public String description(){ return description; }

/*
Java Operators 	Precedence
14 postfix 	expr++ expr--
13 unary 	++expr --expr +expr -expr ~ !
12 multiplicative 	* / %
11 additive 	+ -
10 shift 	<< >> >>>
 9 relational 	< > <= >= instanceof
 8 equality 	== !=
 7 bitwise AND 	&
 6 bitwise exclusive OR 	^
 5 bitwise inclusive OR 	|
 4 logical AND 	&&
 3 logical OR 	||
 2 ternary 	? :
 1 assignment 	= += -= *= /= %= &= ^= |= <<= >>= >>>=
*/

}

