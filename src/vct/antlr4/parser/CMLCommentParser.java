package vct.antlr4.parser;

import hre.HREError;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.tree.ParseTree;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.CompilationUnit;
import vct.col.ast.Contract;
import vct.parsers.CMLLexer;
import vct.parsers.CMLParser;

/**
 * Parser for CML comments.
 * 
 */
public class CMLCommentParser extends CommentParser<CMLParser,CMLLexer> {

  public CMLCommentParser() {
    super(new CMLParser(null), new CMLLexer(null));
  }

  @Override
  public CompilationUnit parse_contract(ASTSequence<?> seq) {
    ParseTree tree=parser.contract();
    return CMLtoCOL.convert(tree, "embedded_comments", tokens, parser);
  }

  @Override
  public CompilationUnit parse_annotations() {
	throw new HREError("annotations for C not defined yet.");
  }

}
