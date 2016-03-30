package vct.main;

import vct.col.ast.ProgramUnit;
import vct.java.printer.JavaDialect;
import vct.java.printer.JavaSyntax;

public class ApiGen {

  public static void main(String args[]){
    ProgramUnit api=Parsers.parseFile(args[0]);
    JavaSyntax.getJava(JavaDialect.JavaVerCors).print(System.out,api);
  }
}
