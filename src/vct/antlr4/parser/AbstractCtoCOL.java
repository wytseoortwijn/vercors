package vct.antlr4.parser;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import vct.col.ast.ASTNode;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.PrimitiveType;
import vct.col.ast.Type;
import vct.parsers.CParser.PrimaryExpressionContext;
import vct.util.Syntax;

/**
 * Convert the shared parts of CML and C parse trees to COL.
 *
 * This class contains the conversions for parse tree nodes,
 * which are handled identically for CML and C and which
 * cannot be handled by the generic methods in ANTLRtoCOL.
 * 
 * @author <a href="mailto:s.c.c.blom@utwente.nl">Stefan Blom</a>
*/
public abstract class AbstractCtoCOL extends ANTLRtoCOL {

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

  public DeclarationStatement getDirectDeclarator(ParserRuleContext ctx) {
    String name=getIdentifier(ctx,0);
    Type t=create.class_type(name);
    if (match(ctx,null,"[","]")){
      t=create.primitive_type(PrimitiveType.Sort.Array,t);
    }
    return create.field_decl(name, t);
  }

}
