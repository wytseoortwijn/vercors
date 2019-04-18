package vct.main;

import vct.antlr4.parser.Parsers;
import vct.col.ast.ProgramUnit;
import vct.col.syntax.JavaDialect;
import vct.col.syntax.JavaSyntax;

import java.io.PrintWriter;

public class ApiGen {

  public static void main(String args[]){
    ProgramUnit api=Parsers.parseFile(args[0]);
    JavaSyntax.getJava(JavaDialect.JavaVerCors).print(new PrintWriter(System.out),api);
  }
}
