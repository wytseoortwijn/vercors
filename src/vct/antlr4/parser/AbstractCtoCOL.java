package vct.antlr4.parser;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import vct.col.ast.ASTNode;
import vct.parsers.CParser.PrimaryExpressionContext;
import vct.util.Syntax;

public abstract class AbstractCtoCOL extends VCTVisitor {

  public AbstractCtoCOL(Syntax syntax,
      String filename,
      BufferedTokenStream tokens, Parser parser, int identifier, Class<?> lexer_class
  ) {
    super(syntax, filename, tokens, parser, identifier, lexer_class);
  }

  public ASTNode visitPrimaryExpression(ParserRuleContext ctx) {
    ASTNode res=visit(ctx);
    if (res!=null) return res;
    if (ctx.children.size()==1){
      ParseTree t=ctx.getChild(0);
      if (t instanceof TerminalNode){
        TerminalNode tn=(TerminalNode)t;
        Token tok=tn.getSymbol();
        return create.constant(Integer.parseInt(tok.getText()));
      }
    }
    return null;
  }

  
}
