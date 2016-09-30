package vct.antlr4.parser;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

import vct.antlr4.parser.OMPoption.Kind;
import vct.antlr4.parser.OMPoption.Schedule;
import vct.parsers.ompLexer;
import vct.parsers.ompParser;
import vct.parsers.ompParser.Omp_optionContext;
import vct.parsers.ompParser.Omp_scheduleContext;
import vct.parsers.ompParser.Omp_sectionContext;
import vct.parsers.ompParser.Omp_sectionsContext;
import vct.parsers.ompParser.Omp_singleContext;
import vct.parsers.ompParser.*;
import vct.parsers.ompVisitor;

public class OMPParser {
  
  public static OMPpragma parse(String pragma){
    InputStream stream=new ByteArrayInputStream(pragma.getBytes());
    ANTLRInputStream input;
    try {
      input = new ANTLRInputStream(stream);
    } catch (IOException e) {
      throw new Error(e.getMessage());
    }
    ompLexer lexer = new ompLexer(input);
    CommonTokenStream tokens = new CommonTokenStream(lexer);
    ErrorCounter ec=new ErrorCounter(pragma);
    ompParser parser = new ompParser(tokens);
    parser.removeErrorListeners();
    parser.addErrorListener(ec);
    ParseTree tree = parser.omp_pragma();
    ConversionVisitor visitor=new ConversionVisitor();
    return (OMPpragma) tree.accept(visitor);
  }

}

class ConversionVisitor implements ompVisitor<OMPelement> {

  @Override
  public OMPelement visit(ParseTree arg0) {
    throw new Error("Cannot visit parse tree");
  }

  @Override
  public OMPelement visitChildren(RuleNode arg0) {
    throw new Error("Cannot visit children");
  }

  @Override
  public OMPelement visitErrorNode(ErrorNode arg0) {
    throw new Error("parse error "+ arg0 +"detected");
  }

  @Override
  public OMPelement visitTerminal(TerminalNode arg0) {
    return null;
  }

  @Override
  public OMPelement visitOmp_pragma(Omp_pragmaContext ctx) {
    System.err.printf("pragma %s%n",ctx.toStringTree());
    return ctx.getChild(0).accept(this); 
   }

  @Override
  public OMPelement visitId_list(Id_listContext ctx) {
    throw new Error("id_list cannot be converted to element");
  }

  @Override
  public OMPelement visitOmp_parallel_for(Omp_parallel_forContext ctx) {
    return new OMPpragma(OMPpragma.Kind.ParallelFor,map(ctx));
  }

  private OMPoption[] map(ParserRuleContext ctx){
    int N=ctx.getChildCount();
    OMPoption[] res=new OMPoption[N];
    for(int i=0;i<N;i++) res[i]=(OMPoption)ctx.getChild(i).accept(this);
    return res;
  }
  
  @Override
  public OMPelement visitOmp_for(Omp_forContext ctx) {
    return new OMPpragma(OMPpragma.Kind.For,map(ctx));
  }

  @Override
  public OMPelement visitOmp_parallel(Omp_parallelContext ctx) {
    return new OMPpragma(OMPpragma.Kind.Parallel,map(ctx));
  }

  @Override
  public OMPelement visitOmp_private(Omp_privateContext ctx) {
    String vars[]=new String[ctx.getChildCount()];
    for(int i=0;i<vars.length;i++){
      vars[i]=ctx.getChild(i).getText();
    }
    return new OMPprivate(vars);
  }

  @Override
  public OMPelement visitOmp_nowait(Omp_nowaitContext ctx) {
    return new OMPnowait();
  }

  @Override
  public OMPelement visitOmp_option(Omp_optionContext ctx) {
    return ctx.getChild(0).accept(this);
  }

  @Override
  public OMPelement visitOmp_schedule(Omp_scheduleContext ctx) {
    return new OMPoption(Kind.Schedule,Schedule.Static);
  }

  @Override
  public OMPelement visitOmp_single(Omp_singleContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public OMPelement visitOmp_sections(Omp_sectionsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public OMPelement visitOmp_section(Omp_sectionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

}

