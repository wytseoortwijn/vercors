package vct.main;

import java.util.HashMap;

import vct.antlr4.parser.ColCParser;
import vct.antlr4.parser.ColIParser;
import vct.antlr4.parser.ColJavaParser;
import vct.antlr4.parser.ColPVLParser;
import vct.col.util.Parser;
import static hre.System.Fail;

public class Parsers {
  
  public static Parser getParser(String extension){
    switch(extension){
    case "c": return new ColCParser();
    case "i":return new ColIParser();
    case "java":return new ColJavaParser();
    case "pvl":return new ColPVLParser();
    }
    Fail("no parser for %s is known");
    return null;
    
  }
  
}
