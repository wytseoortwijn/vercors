package vct.main;

import java.io.File;
import java.util.HashMap;

import vct.antlr4.parser.ColCParser;
import vct.antlr4.parser.ColIParser;
import vct.antlr4.parser.ColJavaParser;
import vct.antlr4.parser.ColPVLParser;
import vct.col.ast.ProgramUnit;
import vct.col.util.Parser;
import vct.silver.ColSilverParser;
import static hre.System.Fail;
import static hre.System.Progress;

public class Parsers {
  
  public static Parser getParser(String extension){
    switch(extension){
    case "cl":
    case "c":
      return new ColCParser();
    case "i":return new ColIParser();
    case "java":return new ColJavaParser();
    case "pvl":return new ColPVLParser();
    case "sil":return new ColSilverParser();
    }
    Fail("no parser for %s is known",extension);
    return null;
    
  }
  
  public static ProgramUnit parseFile(String name){
    int dot=name.lastIndexOf('.');
    if (dot<0) {
      Fail("cannot deduce language of %s",name);
    }
    String lang=name.substring(dot+1);
    if (lang.equals("pvl")){
      //TODO: fix this kludge.
      vct.col.ast.ASTNode.pvl_mode=true;
    }
    Progress("Parsing %s file %s",lang,name);
    ProgramUnit unit=Parsers.getParser(lang).parse(new File(name));
    Progress("Read %s succesfully",name);
    return unit;
  }

}
