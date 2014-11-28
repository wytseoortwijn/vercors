package vct.antlr4.parser;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.NameExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;
import vct.parsers.CParser.BlockItemListContext;
import vct.parsers.CParser.CompoundStatementContext;
import vct.parsers.CParser.LabeledStatementContext;
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

  
  public ASTNode getCompoundStatement(ParserRuleContext ctx) {
    BlockStatement block=create.block();
    if (match(ctx,"{","}")) {
      scan_comments_after(block,ctx.getChild(0));
      return block;
    }
    if (!match(ctx,"{","BlockItemListContext","}")) return null;    
    doblock(block,(ParserRuleContext)ctx.getChild(1)); 
    return block;
  }
  private void doblock(BlockStatement block, ParserRuleContext ctx) {  
    if (match(ctx,"BlockItemContext")){
        //hre.System.Warning("%s",ctx.getChild(0).toStringTree(parser));
        ASTNode temp = convert(ctx,0);
        scan_comments_before(block,ctx.getChild(0)); //DRB    
        block.add_statement(temp);
        scan_comments_after(block,ctx.getChild(0));//DRB 
    } else if (match(ctx,"BlockItemListContext","BlockItemContext")){                       
         doblock(block,(ParserRuleContext)ctx.getChild(0));
         //hre.System.Warning("%s",ctx.getChild(1).toStringTree(parser));
         ASTNode temp = convert(ctx,1);              
         block.add_statement(temp);
         scan_comments_after(block,ctx.getChild(1)); //DRB
    } else {      
      throw hre.System.Failure("unknown BlockItemList");
    }
  }


  
  public ASTNode getLabeledStatement(ParserRuleContext ctx) {
    if (match(ctx, null, ":", null)) {
      ASTNode res = convert(ctx, 2);
      res.addLabel(create.label(ctx.getChild(0).getText()));
      return res;
    }
    return null;
  }
  public ASTNode getSelectionStatement(ParserRuleContext ctx) {
    // TODO Auto-generated method stub    
    if (match(ctx,"if","(","ExpressionContext",")",null)){  //DRB --Added  
        return create.ifthenelse(convert(ctx,2),convert(ctx,4));
    }
    else if (match(ctx,"if","(","ExpressionContext",")",null,"else",null)){ //DRB --Added     
        return create.ifthenelse(convert(ctx,2),convert(ctx,4),convert(ctx,6));
    }
    return null;
  }

  public ASTNode visitPrimaryExpression(ParserRuleContext ctx) {
    ASTNode res=visit(ctx);
    if (res!=null) return res;
    if (match(ctx,null,"(",null,")")){
      String name=getIdentifier(ctx,0);
      ASTNode args[]=convert_linked_list((ParserRuleContext)ctx.getChild(2),",");
      return create.invokation(null,null,name, args);
    }
    if (match(ctx,null,"(",")")){
      String name=getIdentifier(ctx,0);
      return create.invokation(null,null,name,new ASTNode[0]);
    }
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

  public ClassType forceClassType(ASTNode convert) {
	    if (convert instanceof ClassType) return (ClassType)convert;
	    if (convert instanceof NameExpression) return create.class_type(convert.toString());
	    throw hre.System.Failure("cannot convert %s to ClassType",convert.getClass());
	  }
  
  public DeclarationStatement getDirectDeclarator(ParserRuleContext ctx) {
    //hre.System.Warning("direct declarator %s",ctx.toStringTree(parser));
    if (match(ctx,(String)null)){
      String name=getIdentifier(ctx,0);
      return create.field_decl(name, VariableDeclaration.common_type);
    }
    if (match(ctx,null,"[","]")){
      DeclarationStatement d=(DeclarationStatement)convert(ctx,0);
      Type t=d.getType();
      t=create.primitive_type(PrimitiveType.Sort.Array,t);
      return create.field_decl(d.getName(),t);
    }
    if (match(ctx,null,"[",null,"]")){
      DeclarationStatement d=(DeclarationStatement)convert(ctx,0);
      Type t=d.getType();
      t=create.primitive_type(PrimitiveType.Sort.Array,t,convert(ctx,2));
      return create.field_decl(d.getName(),t);
    }
    return null;
  }

}
