package vct.antlr4.parser;

import static hre.System.*;
import hre.ast.FileOrigin;

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

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
      	command+=" -nostdinc -isystem "+Configuration.getHome().resolve("include");
        for(String p:Configuration.cpp_include_path){
          command+=" -I"+p;
        }
        for(String p:Configuration.cpp_defines){
          command+=" -D"+p;
        }
      	command+=" "+file_name;
      	
      	Progress("pre-processing command line: %s",command);
      	final Process process=runtime.exec(command);
        Thread t=new Thread(){
          public void run(){
            DataInputStream err=new DataInputStream(process.getErrorStream());
            boolean err_found=false;
            String s;
            try {
              while((s=err.readLine())!=null){
                System.err.println(s);
                if (s.matches(".*error.*")) err_found=true;
              }
            } catch (IOException e) {
              e.printStackTrace();
              err_found=true;
            }
            if (err_found){
              System.exit(1);
            }
          }
        };
        t.setDaemon(true);
        t.start();
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

