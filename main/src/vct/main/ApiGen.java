package vct.main;

import vct.col.ast.ProgramUnit;
import vct.col.syntax.JavaSyntax;
import vct.java.printer.JavaDialect;

public class ApiGen {

  public static void main(String args[]){
    ProgramUnit api=Parsers.parseFile(args[0]);
    JavaSyntax.getJava(JavaDialect.JavaVerCors).print(System.out,api);
  }
}
