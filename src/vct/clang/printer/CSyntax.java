package vct.clang.printer;

import hre.ast.TrackingOutput;
import vct.col.ast.ASTNode;
import vct.util.Syntax;
import static vct.col.ast.StandardOperator.*;
import static vct.col.ast.PrimitiveType.Sort.*;

public class CSyntax extends Syntax{
  private static Syntax c_syntax;
  private static Syntax cml_syntax;
  
  public CSyntax(String dialect) {
    super(dialect);
  }

  public static void setCommon(Syntax syntax){
    syntax.addOperator(Subscript,145,"","[","]"); // check priority!!!
    
    syntax.addPostfix(PostIncr, "++", 160);
    syntax.addPostfix(PostDecr, "--", 160);
    syntax.addPrefix(PreIncr, "++", 160);
    syntax.addPrefix(PreDecr, "--", 160);
    
    syntax.addPrefix(UMinus, "-", 150);
    syntax.addPrefix(UPlus, "+", 150);

    syntax.addLeftFix(Mult,"*",130);
    syntax.addLeftFix(Div,"/",130);
    syntax.addLeftFix(Mod,"%",130);
    
    syntax.addLeftFix(Plus,"+",120);
    syntax.addLeftFix(Minus,"-",120);
    
    syntax.addInfix(LT,"<",100);
    syntax.addInfix(LTE,"<=",100);
    syntax.addInfix(GT,">",100);
    syntax.addInfix(GTE,">=",100);
    
    syntax.addInfix(EQ,"==",90);
    syntax.addInfix(NEQ,"!=",90);
    
    syntax.addRightFix(Assign,"=",30);
    
    syntax.addPrimitiveType(Double,"double");
    syntax.addPrimitiveType(Integer,"int");
    //syntax.addPrimitiveType(Fraction,"frac");
    syntax.addPrimitiveType(Long,"long");
    syntax.addPrimitiveType(Void,"void");
    //syntax.addPrimitiveType(Resource,"resource");
    syntax.addPrimitiveType(Boolean,"bool");
    //syntax.addPrimitiveType(Class,"classtype");
    syntax.addPrimitiveType(Char,"char");
    syntax.addPrimitiveType(Float,"float");
  }

  public static Syntax getC() {
    if (c_syntax==null){
      c_syntax=new CSyntax("C");
      setCommon(c_syntax);
    }
    return c_syntax;
  }
  
  public static Syntax getCML() {
    if (cml_syntax==null){
      cml_syntax=new CSyntax("C + CML");
      setCommon(cml_syntax);
      cml_syntax.addLeftFix(Star,"**",130); // TODO: priorities!
      cml_syntax.addLeftFix(Wand,"-*",120); // TODO: priorities!
      cml_syntax.addFunction(ArrayPerm,"ArrayPerm");
      cml_syntax.addFunction(Perm,"perm");
      cml_syntax.addFunction(Old,"old");
    }
    return cml_syntax;
  }

  @Override
  public void print(TrackingOutput out, ASTNode n) {
    CPrinter p=new CPrinter(out);
    n.accept(p);
  } 

}

/*

17  ::  Scope resolution  Left-to-right
16  ++   --   Suffix/postfix increment and decrement
    ()  Function call
    []  Array subscripting
    .   Element selection by reference
    −>  Element selection through pointer
15  ++   --   Prefix increment and decrement  Right-to-left
    +   −   Unary plus and minus
    !   ~   Logical NOT and bitwise NOT
    (type)  Type cast
    *   Indirection (dereference)
    &   Address-of
    sizeof  Size-of
    new, new[]  Dynamic memory allocation
    delete, delete[]  Dynamic memory deallocation
14  .*   ->*  Pointer to member   Left-to-right
13   *   /   %   Multiplication, division, and remainder
12   +   −   Addition and subtraction
11   <<   >>   Bitwise left shift and right shift
10   <   <=  For relational operators < and ≤ respectively
    >   >=  For relational operators > and ≥ respectively
 9  ==   !=   For relational = and ≠ respectively
 8  &   Bitwise AND
 7  ^   Bitwise XOR (exclusive or)
 6  |   Bitwise OR (inclusive or)
 5  &&  Logical AND
 4  ||  Logical OR
 3  ?:  Ternary conditional   Right-to-left
    =   Direct assignment (provided by default for C++ classes)
    +=   −=   Assignment by sum and difference
   *=   /=   %=  Assignment by product, quotient, and remainder
    <<=   >>=   Assignment by bitwise left shift and right shift
    &=   ^=   |=  Assignment by bitwise AND, XOR, and OR
 2 throw   Throw operator (for exceptions)
 1 ,   Comma   Left-to-right 

*/
