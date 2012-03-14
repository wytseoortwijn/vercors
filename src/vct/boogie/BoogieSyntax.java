// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import vct.util.Syntax;
import static vct.col.ast.StandardOperator.*;

/**
 * Create Syntax objects for Boogie and Chalice.
 * 
 * @author Stefan Blom
 */
public class BoogieSyntax {
  private static Syntax boogie;
  private static Syntax chalice;
  
  private static void setCommon(Syntax syntax){
    syntax.addLeftFix(Select,".",150);
    syntax.addPrefix(Not,"!",130);
    syntax.addLeftFix(Mult,"*",120);
    syntax.addLeftFix(Div,"/",120);
    syntax.addLeftFix(Mod,"%",120);
    syntax.addLeftFix(Plus,"+",110);
    syntax.addLeftFix(Minus,"-",110);
    syntax.addInfix(LT,"<",90);
    syntax.addInfix(LTE,"<=",90);
    syntax.addInfix(GT,">",90);
    syntax.addInfix(GTE,">=",90);
    syntax.addInfix(EQ,"==",80);
    syntax.addInfix(NEQ,"!=",80);
    syntax.addLeftFix(Star,"&&",40);
    syntax.addLeftFix(And,"&&",40);
    syntax.addLeftFix(Or,"||",30);
    syntax.addLeftFix(Implies, "==>", 30);
    syntax.addLeftFix(IFF, "<==>", 30);
    syntax.addRightFix(Assign,"=",10);
    syntax.addFunction(Old,"old");
  }

  public static Syntax getBoogie(){
    if(boogie==null){
      boogie=new Syntax();
      setCommon(boogie);
    }
    return boogie;
  }
  
  public static Syntax getChalice(){
    if(chalice==null){
      chalice=new Syntax();
      setCommon(chalice);
      chalice.addFunction(Perm,"acc");
    }
    return chalice;
  }

}


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

