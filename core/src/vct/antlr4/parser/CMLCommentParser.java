package vct.antlr4.parser;

import hre.HREError;

import org.antlr.v4.runtime.tree.ParseTree;

import vct.col.ast.ASTSequence;
import vct.parsers.CMLLexer;
import vct.parsers.CMLParser;

/**
 * Parser for CML comments.
 * 
 */
public class CMLCommentParser extends CommentParser<CMLParser,CMLLexer> {

  public CMLCommentParser(ErrorCounter ec) {
    super(ec,new CMLParser(null), new CMLLexer(null));
  }

  @Override
  public TempSequence parse_contract(ASTSequence<?> seq) {
    ParseTree tree=parser.specificationSequence();
    ec.report();
    return CMLtoCOL.convert_seq(tree, "embedded_comments", tokens, parser);
  }

  @Override
  public TempSequence parse_annotations() {
	  throw new HREError("annotations for C not defined yet.");
  }

}
