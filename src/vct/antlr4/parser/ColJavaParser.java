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
public class ColJavaParser implements vct.col.util.Parser {

  @Override
  public ProgramUnit parse(File file) {
    String file_name=file.toString();
      try {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        
        JavaLexer lexer = new JavaLexer(input);
        
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        
        JavaParser parser = new JavaParser(tokens);
        
        ParseTree tree = parser.compilationUnit();

        ProgramUnit pu=JavaToCol.convert(tree,file_name,tokens,parser);
        
        //System.out.printf("parsing got %d entries%n",pu.size());
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        
        pu=new CommentRewriter(pu,new JMLCommentParser()).rewriteAll();
        pu=new FlattenVariableDeclarations(pu).rewriteAll();
        pu=new SpecificationCollector(pu).rewriteAll();
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        pu=new JavaPostProcessor(pu).rewriteAll();
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        pu=new AnnotationInterpreter(pu).rewriteAll();
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        return pu;
      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }      
    return null;
  }

}

