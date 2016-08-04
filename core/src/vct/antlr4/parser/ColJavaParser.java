package vct.antlr4.parser;

import static hre.System.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import vct.parsers.*;
import vct.col.ast.ProgramUnit;
import vct.col.rewrite.AnnotationInterpreter;
import vct.col.rewrite.FilterSpecIgnore;
import vct.col.rewrite.FlattenVariableDeclarations;
import vct.col.syntax.JavaDialect;
import vct.col.syntax.JavaSyntax;

/**
 * Parse specified code and convert the contents to COL. 
 */
public class ColJavaParser implements vct.col.util.Parser {

  @Override
  public ProgramUnit parse(File file) {
    String file_name=file.toString();
      try {
        TimeKeeper tk=new TimeKeeper();
        
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(file));
        JavaJMLLexer lexer = new JavaJMLLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        JavaJMLParser parser = new JavaJMLParser(tokens);
        ErrorCounter ec=new ErrorCounter(file_name);
        parser.removeErrorListeners();
        parser.addErrorListener(ec);
        lexer.removeErrorListeners();
        lexer.addErrorListener(ec);
        ParseTree tree = parser.compilationUnit();
        ec.report();
        Progress("first parsing pass took %dms",tk.show());
        
        ProgramUnit pu=JavaJMLtoCol.convert(tree,file_name,tokens,parser);
        Progress("AST conversion took %dms",tk.show());
        
        Debug("program after Java parsing:%n%s",pu);
        //System.out.printf("parsing got %d entries%n",pu.size());
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        
        pu=new CommentRewriter(pu,new JMLCommentParser(ec)).rewriteAll();
        Progress("Specification parsing took %dms",tk.show());
        ec.report();
        Debug("program after specification parsing:%n%s",pu);
        
        pu=new FlattenVariableDeclarations(pu).rewriteAll();
        Progress("Flattening variables took %dms",tk.show());
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        Debug("program after flattening variables:%n%s",pu);
        
        pu=new SpecificationCollector(JavaSyntax.getJava(JavaDialect.JavaVerCors),pu).rewriteAll();
        Progress("Shuffling specifications took %dms",tk.show());        
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        Debug("program after collecting specs:%n%s",pu);
        
        pu=new JavaPostProcessor(pu).rewriteAll();
        Progress("post processing took %dms",tk.show());        
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        
        pu=new AnnotationInterpreter(pu).rewriteAll();
        Progress("interpreting annotations took %dms",tk.show());        
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        
        //cannnot resolve here: other .java files may be needed!
        //pu=new JavaResolver(pu).rewriteAll();
        //Progress("resolving library calls took %dms",tk.show());        
        //vct.util.Configuration.getDiagSyntax().print(System.out,pu);
        
        pu=new FilterSpecIgnore(pu).rewriteAll();
        Progress("filtering spec_ignore took %dms",tk.show()); 

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

