package vct.antlr4.parser;

import org.antlr.v4.runtime.tree.ParseTree;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Contract;
import vct.parsers.Java7JMLLexer;
import vct.parsers.Java7JMLParser;

/**
 * Parser for JML comments.
 */
public class Java7JMLCommentParser extends CommentParser<Java7JMLParser,Java7JMLLexer> {

  
  public Java7JMLCommentParser(ErrorCounter ec) {
    super(ec,new Java7JMLParser(null), new Java7JMLLexer(null));
  }

  @Override
  public TempSequence parse_contract(ASTSequence<?> seq) {
    ParseTree tree=parser.specificationSequence();
    ec.report();
    return Java7JMLtoCol.convert(tree, "embedded_comments", tokens, parser);
  }

  @Override
  public TempSequence parse_annotations() {
	ParseTree tree=parser.specificationModifier();
	ec.report();
	return Java7JMLtoCol.convert(tree, "embedded_comments", tokens, parser);
  }

}
