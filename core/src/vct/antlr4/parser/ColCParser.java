package vct.antlr4.parser;

import static hre.System.*;
import hre.ast.FileOrigin;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import pv.parser.PVFullLexer;
import pv.parser.PVFullParser;
import vct.java.printer.JavaDialect;
import vct.java.printer.JavaSyntax;
import vct.parsers.*;
import vct.util.Configuration;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.ProgramUnit;
import vct.col.rewrite.AbstractRewriter;
import vct.col.rewrite.AnnotationInterpreter;
import vct.col.rewrite.FlattenVariableDeclarations;

/**
 * Parse specified code and convert the contents to COL. 
 */
public class ColCParser extends ColIParser {
  
  
  
  @Override
  public ProgramUnit parse(File file) {
    String file_name=file.toString();
       try {
        Runtime runtime=Runtime.getRuntime();
                    	
      	String command=Configuration.cpp_command.get();
      	for(String p:Configuration.cpp_include_path){
      	  command+=" -I"+p;
      	}
      	command+=" "+file_name;
      	
      	Progress("pre-processing command line: %s",command);
      	Process process=runtime.exec(command);
          
      	return parse(file_name,process.getInputStream());
      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }
    return null;
  }

}

