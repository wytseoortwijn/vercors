package vct.antlr4.parser;

import org.antlr.v4.runtime.tree.ParseTree;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Contract;
import vct.parsers.JavaJMLLexer;
import vct.parsers.JavaJMLParser;

/**
 * Parser for JML comments.
 */
public class JMLCommentParser extends CommentParser<JavaJMLParser,JavaJMLLexer> {

  
  public JMLCommentParser(ErrorCounter ec) {
    super(ec,new JavaJMLParser(null), new JavaJMLLexer(null));
  }

  @Override
  public TempSequence parse_contract(ASTSequence<?> seq) {
    ParseTree tree=parser.specificationSequence();
    ec.report();
    return JavaJMLtoCol.convert_seq(tree, "embedded_comments", tokens, parser);
  }

  @Override
  public TempSequence parse_annotations() {
	ParseTree tree=parser.specificationModifier();
	ec.report();
	return JavaJMLtoCol.convert_seq(tree, "embedded_comments", tokens, parser);
  }

}
