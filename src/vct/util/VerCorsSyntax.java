package vct.util;

import static vct.col.ast.ASTReserved.Any;
import static vct.col.ast.ASTReserved.Pure;
import static vct.col.ast.ASTReserved.Result;
import static vct.col.ast.PrimitiveType.Sort.Class;
import static vct.col.ast.PrimitiveType.Sort.Fraction;
import static vct.col.ast.PrimitiveType.Sort.Resource;
import static vct.col.ast.PrimitiveType.Sort.ZFraction;
import static vct.col.ast.StandardOperator.*;

public class VerCorsSyntax {

  public static void add(Syntax syntax) {
    //TODO: find out what the proper priorities are!
    syntax.addInfix(SubType,"<:",9);
    syntax.addInfix(SuperType,":>",9);
    syntax.addInfix(Implies,"==>",3);
    syntax.addInfix(IFF,"<==>",3);
    syntax.addLeftFix(Wand,"-*",3);
    syntax.addFunction(Perm,"Perm");
    syntax.addFunction(Head,"head");
    syntax.addFunction(Tail,"tail");
    syntax.addFunction(Value,"Value");
    syntax.addFunction(PointsTo,"PointsTo");
    syntax.addFunction(ArrayPerm,"ArrayPerm");
    syntax.addFunction(AddsTo,"AddsTo");
    syntax.addFunction(Volatile, "Volatile");
    syntax.addFunction(Old,"\\old");
    syntax.addFunction(Length,"\\length");
    syntax.addOperator(Size,999,"|","|");
    syntax.addOperator(Nil,999,"nil<",">");
    syntax.addLeftFix(Append,"+++",5);
    syntax.addLeftFix(Star,"**",4);

    syntax.addPrimitiveType(ZFraction,"zfrac");
    syntax.addPrimitiveType(Fraction,"frac");
    syntax.addPrimitiveType(Resource,"resource");
    syntax.addPrimitiveType(Class,"classtype");
    
    syntax.addReserved(Result,"\\result");
    syntax.addReserved(Pure,"pure");
    syntax.addReserved(Any,"*");
    syntax.addPrefix(BindOutput,"?",666);
  }

}
