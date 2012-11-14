// -*- tab-width:2 ; indent-tabs-mode:nil -*-

package vct.java.printer;

import vct.util.Syntax;
import static vct.col.ast.StandardOperator.*;
import static vct.col.ast.PrimitiveType.Sort.*;

/**
 * Create a Syntax object for Java.
 */
public class JavaSyntax {
  private static Syntax syntax;
  
  public static Syntax get(){
    if(syntax==null){
      syntax=new Syntax();
      // non-java operators.
      syntax.addInfix(Implies,"==>",30);
      syntax.addInfix(IFF,"<==>",30);
      syntax.addLeftFix(Wand,"-*",30);
      syntax.addFunction(Perm,"Perm");
      syntax.addFunction(Value,"Value");
      syntax.addFunction(PointsTo,"PointsTo");
      syntax.addFunction(Old,"\\old");
      
      syntax.addOperator(Subscript,145,"","[","]"); // TODO: check if relative order to Select is OK!
      
      // Java Operators  Precedence
      // 14 postfix  expr++ expr--
      syntax.addPostfix(PostIncr,"++",140);
      syntax.addPostfix(PostDecr,"--",140);
      // 13 unary   ++expr --expr +expr -expr ~ !
      syntax.addPrefix(BitNot, "~", 130);
      syntax.addPrefix(Not, "!", 130);
      syntax.addPrefix(UMinus, "-", 130);
      syntax.addPrefix(UPlus, "+", 130);
      syntax.addPrefix(PreIncr, "++", 130);
      syntax.addPrefix(PreIncr, "--", 130);
      // 12 multiplicative  * / %
      syntax.addLeftFix(Mult,"*",120);
      syntax.addLeftFix(Div,"/",120);
      syntax.addLeftFix(Mod,"%",120);
      // 11 additive  + -
      syntax.addLeftFix(Plus,"+",110);
      syntax.addLeftFix(Minus,"-",110);
      // 10 shift   << >> >>>
      syntax.addInfix(LeftShift,"<<", 100);
      syntax.addInfix(RightShift,">>", 100);
      syntax.addInfix(UnsignedRightShift,">>", 100);
      //  9 relational  < > <= >= instanceof
      syntax.addInfix(LT,"<",90);
      syntax.addInfix(LTE,"<=",90);
      syntax.addInfix(GT,">",90);
      syntax.addInfix(GTE,">=",90);
      syntax.addInfix(Instance," instanceof ",90);
      //  8 equality  == !=
      syntax.addInfix(EQ,"==",80);
      syntax.addInfix(NEQ,"!=",80);
      //  7 bitwise AND   &
      syntax.addInfix(BitAnd,"&",70);
      //  6 bitwise exclusive OR  ^
      syntax.addInfix(BitXor,"^",60);
      //  5 bitwise inclusive OR  |
      syntax.addInfix(BitOr,"|",50);
      //  4 logical AND   &&
      syntax.addLeftFix(And,"&&",40);
      syntax.addLeftFix(Star,"**",40);
      //  3 logical OR  ||
      syntax.addLeftFix(Or,"||",30);
      //  2 ternary   ? :
      syntax.addOperator(ITE,20,"","?",":","");
      //  1 assignment  = += -= *= /= %= &= ^= |= <<= >>= >>>=
      syntax.addRightFix(Assign,"=",10);
      // Note that Modify covers lhs <op> = rhs for any op,
      // not just the legal ones in Java.
      syntax.addOperator(Modify,10,"","","=","");
      
      syntax.addPrimitiveType(Double,"double");
      syntax.addPrimitiveType(Integer,"int");
      syntax.addPrimitiveType(Fraction,"frac");
      syntax.addPrimitiveType(Long,"long");
      syntax.addPrimitiveType(Void,"void");
      syntax.addPrimitiveType(Boolean,"boolean");
      syntax.addPrimitiveType(Class,"classtype");
      
    }
    return syntax;
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

