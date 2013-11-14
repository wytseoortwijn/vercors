package vct.antlr4.parser;

import static hre.System.Failure;

import java.io.IOException;
import java.io.InputStream;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.CompilationUnit;
import vct.col.ast.Contract;
import vct.col.ast.Method;
import vct.parsers.CMLLexer;
import vct.parsers.CMLParser;
import hre.io.FifoStream;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

public abstract class CommentParser<Parser extends org.antlr.v4.runtime.Parser,Lexer extends org.antlr.v4.runtime.Lexer> {
  
  protected Parser parser;
  protected Lexer lexer;
  protected CommonTokenStream tokens;
  
  public CommentParser(Parser parser, Lexer lexer) {
    this.parser=parser;
    this.lexer=lexer;
  }

  public Contract contract(ASTSequence<?> seq,InputStream fifo){
    ANTLRInputStream input;
    try {
      input = new ANTLRInputStream(fifo);
    } catch (IOException e) {
      //e.printStackTrace();
      throw Failure("I/O error");
    }
    lexer.reset();
    lexer.setInputStream(input);
    tokens = new CommonTokenStream(lexer);
    parser.reset();
    parser.setTokenStream(tokens);
    CompilationUnit cu=parse_contract(seq);;
    Contract contract=null;
    for(ASTNode n:cu.get()){
      if (n instanceof Contract){
        contract=(Contract)n;
      } else {
        if (contract!=null && n instanceof Method){
          Method m=(Method)n;
          if (m.getContract()!=null){
            throw Failure("double contract");
          }
          m.setContract(contract);
        }
        seq.add(n);
        contract=null;
      }
    }
    return contract;
  }
  
  public abstract CompilationUnit parse_contract(ASTSequence<?> seq);

  public void annotations(ASTNode node, InputStream fifo){
    ANTLRInputStream input;
    try {
      input = new ANTLRInputStream(fifo);
    } catch (IOException e) {
      //e.printStackTrace();
      throw Failure("I/O error");
    }
    lexer.reset();
    lexer.setInputStream(input);
    tokens = new CommonTokenStream(lexer);
    parser.reset();
    parser.setTokenStream(tokens);
    CompilationUnit cu=parse_annotations();
    for(ASTNode n:cu.get()){
      node.attach(n);
    }
  }

  public abstract CompilationUnit parse_annotations();
  
}
