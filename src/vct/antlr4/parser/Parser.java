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
import vct.java.printer.JavaSyntax;
import vct.parsers.*;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTNode;
import vct.col.ast.CompilationUnit;
import vct.col.ast.ProgramUnit;
import vct.col.rewrite.AbstractRewriter;
import vct.col.rewrite.AnnotationInterpreter;
import vct.col.rewrite.FlattenVariableDeclarations;

/**
 * Parse specified code and convert the contents to COL. 
 */
public class Parser implements vct.col.util.Parser {

  @Override
  public CompilationUnit parse(File file) {
    String file_name=file.toString();
    if (file_name.endsWith(".pvl")){
      try {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        
        PVFullLexer lexer = new PVFullLexer(input);
        
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        
        PVFullParser parser = new PVFullParser(tokens);
        
        ParseTree tree = parser.program();

        Debug("parser got: %s",tree.toStringTree(parser));

        CompilationUnit cu=PVLtoCOL.convert(tree,file_name,tokens,parser);
        
        ProgramUnit pu=new ProgramUnit();
        pu.add(cu);
        pu=new FlattenVariableDeclarations(pu).rewriteAll();
        if (pu.size()!=1){
          Fail("bad program unit size");
        }
        return pu.get(0);
      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }
    } else if (file_name.endsWith(".c11")){
      try {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        
        CLexer lexer = new CLexer(input);
        
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        
        CParser parser = new CParser(tokens);
        
        ParseTree tree = parser.compilationUnit();
        
        Debug("parser got: %s",tree.toStringTree(parser));

        CompilationUnit cu=CtoCOL.convert(tree,file_name,tokens,parser);
        
        ProgramUnit pu=new ProgramUnit();
        pu.add(cu);
        
        AbstractRewriter rw=new CommentRewriter(pu,new CMLCommentParser());
        pu=rw.rewriteAll();
        
        if (pu.size()!=1){
          Fail("bad program unit size");
        }
        
        cu=new CompilationUnit(file_name);
        ASTClass cl=new ASTClass("Main",ClassKind.Plain);
        cl.setOrigin(new FileOrigin(file_name,1,1));
        cu.add(cl);
        for(ASTNode n:pu.get(0).get()){
          cl.add_dynamic(n);
        }
        return cu;

      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }
    } else if (file_name.endsWith(".c")||file_name.endsWith(".cl")){
      try {
        Runtime runtime=Runtime.getRuntime();
        
    	Progress("pre-processing %s",file_name);
      
    	// the cpp pre processor turns \r\n line endings into \n\n !
    	// hence, we use may have to use clang
    	
    	//Process process=runtime.exec("clang -E -C -I. "+file_name);
    	Process process=runtime.exec("cpp -C -I. "+file_name);

        //ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        
        ANTLRInputStream input = new ANTLRInputStream(process.getInputStream());
        
        CLexer lexer = new CLexer(input);
        
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        
        CParser parser = new CParser(tokens);
        
        ParseTree tree = parser.compilationUnit();
        
        Debug("parser got: %s",tree.toStringTree(parser));

        CompilationUnit cu=CtoCOL.convert(tree,file_name,tokens,parser);
        
        ProgramUnit pu=new ProgramUnit();
        pu.add(cu);
        
        AbstractRewriter rw=new CommentRewriter(pu,new CMLCommentParser());
        pu=rw.rewriteAll();
        
        if (pu.size()!=1){
          Fail("bad program unit size");
        }
        
        cu=new CompilationUnit(file_name);
        ASTClass cl=new ASTClass("Main",ClassKind.Plain);
        cl.setOrigin(new FileOrigin(file_name,1,1));
        cu.add(cl);
        for(ASTNode n:pu.get(0).get()){
          cl.add_dynamic(n);
        }
        return cu;
      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }
    } else if (file_name.endsWith(".java")) {
      try {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        
        JavaLexer lexer = new JavaLexer(input);
        
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        
        JavaParser parser = new JavaParser(tokens);
        
        ParseTree tree = parser.compilationUnit();

        CompilationUnit cu=JavaToCol.convert(tree,file_name,tokens,parser);
        
        ProgramUnit pu=new ProgramUnit();
        pu.add(cu);
        pu=new CommentRewriter(pu,new JMLCommentParser()).rewriteAll();
        //JavaSyntax.getJavaJML().print(System.out, pu);
        pu=new FlattenVariableDeclarations(pu).rewriteAll();
        //JavaSyntax.getJavaJML().print(System.out, pu);
        pu=new SpecificationCollector(pu).rewriteAll();
        pu=new JavaPostProcessor(pu).rewriteAll();
        pu=new AnnotationInterpreter(pu).rewriteAll();
        if (pu.size()!=1){
          Fail("bad program unit size");
        }
        return pu.get(0);
      } catch (FileNotFoundException e) {
        Fail("File %s has not been found",file_name);
      } catch (Exception e) {
        e.printStackTrace();
        Abort("Exception %s while parsing %s",e.getClass(),file_name);
      }      
    } else {
      Fail("No parser for %s is known",file_name);
    }
    return null;
  }

}

