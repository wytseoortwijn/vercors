// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

public enum StandardOperator {
  /** Unary plus. */
  UPlus(1),
  /** Unary minus. */
  UMinus(1),
  /** Addition. */
  Plus(2),
  /** Binary minus or subtraction. */
  Minus(2),
  /** Multiplication. */
  Mult(2),
  /** Division. */
  Div(2),
  /** Modulo or remainder. */
  Mod(2),
  /** Bitwise and. */
  BitAnd(2),
  /** Bitwise or. */
  BitOr(2),
  /** Bitwise eXclusive OR. */
  BitXor(2),
  /** Bitwise negation or complement. */
  BitNot(2),
  /** Logical and. May or may not mean 'and also' */
  And(2),
  /** Logical or. May or may not mean 'or else' */
  Or(2),
  /** Logical negation. */
  Not(1),
  /** Logical implication. */
  Implies(2),
  /** Logical if and only if. */
  IFF(2),
  /** Equality test. */
  EQ(2),
  /** Inequality test. */
  NEQ(2),
  /** Greater Than test. */
  GT(2),
  /** Greater Than or Equal test. */
  GTE(2),
  /** Lesss Than test. */
  LT(2),
  /** Lesss Than or Equal test. */
  LTE(2),
  /** If then else operator or conditional. */
  ITE(3),
  /** Instance of test. */
  Instance(2),
  /** Simple assignment operator. */
  Assign(2),
  /** Modifying assignment operator. The second argument is intended to be a binary function. */ 
  Modify(3),
  /** Increment and return new value. */
  PreIncr(1),
  /** Decrement and return new value. */
  PreDecr(1),
  /** Increment and return old value. */
  PostIncr(1),
  /** Decrement and return old value. */
  PostDecr(1),
  /** Shift left. */
  LeftShift(2),
  /** (signed) shift right. */
  RightShift(2),
  /** Unsigned shift right. */
  UnsignedRightShift(2),
  /** Separating conjunction. */
  Star(2),
  /** Separating implication. */
  Wand(2),
  /** Fractional permission predicate. */
  Perm(2),
  /** Fractional permission predicate with value access. */ 
  PointsTo(3),
  /** Immutable permission predicate.  */
  Value(1),
  /** Member selection. */
  Select(2),
  /** Guarded member selection. (Selection with built-in null test.) */
  GuardedSelect(2),
  /** Array subscript. */
  Subscript(2),
  /** Fork statement. */
  Fork(1),
  /** Join statement. */
  Join(1),
  /** Lock statement. */
  Lock(1),
  /** Unfold statement. */
  Unlock(1),
  /** Fold statement. */
  Fold(1),
  /** Unfold statement. */
  Unfold(1),
  /** Assert Statement. */
  Assert(1),
  /** Assume statement. */
  Assume(1),
  /** Havoc statement. */
  Havoc(1),
  /** Hoare Predicate statement. This is the main ingredient of a Hoare Logic proof. */
  HoarePredicate(1),
  /** Evaluate argument in pre-execution(old) state. */
  Old(1),
  /** Continue with next value in loop */
  Continue(1),
  /** Create a new uninitialized object */
  New(1);

  private final int arity;
  
  StandardOperator(int arity){
    this.arity=arity;
  }
  
  public int arity(){ return arity; }

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

