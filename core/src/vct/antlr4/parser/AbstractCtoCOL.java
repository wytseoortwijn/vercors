package vct.antlr4.parser;

import hre.Failure;

import java.util.ArrayList;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import vct.col.ast.ASTDeclaration;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method.Kind;
import vct.col.ast.NameExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;
import vct.col.syntax.Syntax;
import vct.parsers.CParser.BlockItemListContext;
import vct.parsers.CParser.CompoundStatementContext;
import vct.parsers.CParser.LabeledStatementContext;
import vct.parsers.CParser.PrimaryExpressionContext;

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

  public AbstractCtoCOL(ASTSequence<?> unit,Syntax syntax,
      String filename,
      BufferedTokenStream tokens, Parser parser, int identifier, Class<?> lexer_class
  ) {
    super(unit, syntax, filename, tokens, parser, identifier, lexer_class);
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
    ParseTree t=ctx.getChild(0);
    if (t instanceof TerminalNode){
      TerminalNode tn=(TerminalNode)t;
      Token tok=tn.getSymbol();
      Vocabulary voc=parser.getVocabulary();
      String name=voc.getSymbolicName(tok.getType());
      String text=tok.getText();
      switch(name){
        case "Identifier":
          return convert(ctx,0);
        case "Constant":
          if (text.matches("[0-9]*")){
            return create.constant(Integer.parseInt(text));
          } else if (text.matches("0x[0-9]*")) {
            return create.constant(Integer.parseInt(text.substring(2),16));
          } else if (text.matches("[0-9]*[.][0-9]*")) {
            return create.constant(Float.parseFloat(text));
          } else if (text.matches("['].*[']")) {
            return create.constant(text);
          } else {
            throw new hre.HREError("could not match constant: %s",text);
          }
        case "StringLiteral":
          String str=text;
          int i=1;
          while(i<ctx.getChildCount()){
            tn=(TerminalNode)ctx.getChild(i);
            tok=tn.getSymbol();
            str=str+tok.getText();
            i++;
          }
          return create.constant(str);
        default:
          throw new hre.HREError("missing case in visitPrimaryExpression: %s",name);
      }
    }
    return null;
  }

  public ClassType forceClassType(ASTNode convert) {
	    if (convert instanceof ClassType) return (ClassType)convert;
	    if (convert instanceof NameExpression) return create.class_type(convert.toString());
	    throw hre.System.Failure("cannot convert %s to ClassType",convert.getClass());
	  }
  
  protected void convert_parameters(ArrayList<DeclarationStatement> args,
      ParserRuleContext arg_ctx) throws Failure {
    if (match(arg_ctx,null,",","...")){
      args.add(create.field_decl("va_args", create.primitive_type(Sort.CVarArgs)));
    }
    arg_ctx=(ParserRuleContext)arg_ctx.getChild(0);
    while(match(arg_ctx,null,",",null)){
      args.add(0,(DeclarationStatement)convert(arg_ctx,2));
      arg_ctx=(ParserRuleContext)arg_ctx.getChild(0);
    }
    ASTNode n=convert(arg_ctx);
    if (n instanceof DeclarationStatement){
      args.add(0,(DeclarationStatement)n);
    } else {
      args.add(0,create.field_decl("__x_"+args.size(),(Type)n));
    }
      
  }


  public ASTDeclaration getDirectDeclarator(ParserRuleContext ctx) {
    //hre.System.Warning("direct declarator %s",ctx.toStringTree(parser));
    if (match(ctx,(String)null)){
      String name=getIdentifier(ctx,0);
      return create.field_decl(name, VariableDeclaration.common_type);
    }
    boolean pars=false;
    if (match(ctx,null,"(",")")||(pars=match(ctx,null,"(","ParameterTypeList",")"))){
      String name=getIdentifier(ctx, 0);
      ArrayList<DeclarationStatement> args=new ArrayList();
      if (pars){  
        convert_parameters(args,(ParserRuleContext)ctx.getChild(2));
      }
      boolean varargs=false;
      if (args.size()>0){
        Type t=args.get(args.size()-1).getType();
        varargs=t.isPrimitive(Sort.CVarArgs);
      }
      return create.method_kind(Kind.Plain, VariableDeclaration.common_type, null, name, args, varargs, null);
    }
    if (match(ctx,null,"[","]")){
      DeclarationStatement d=(DeclarationStatement)convert(ctx,0);
      Type t=d.getType();
      t=create.primitive_type(PrimitiveType.Sort.Array,t);
      return create.field_decl(d.getName(),t);
    }
    int N=ctx.getChildCount();
    if (match(0,true,ctx,null,"[") && match(N-1,false,ctx,"]")){
      DeclarationStatement d=(DeclarationStatement)convert(ctx,0);
      Type t=d.getType();
      if (N>4) {
        hre.System.Warning("ignoring %d modifiers in declaration",N-4);
      }
      t=create.primitive_type(PrimitiveType.Sort.Array,t,convert(ctx,N-2));
      return create.field_decl(d.getName(),t);
    }
    return null;
  }


  public ASTNode getParameterDeclaration(ParserRuleContext ctx) {
    if (match(ctx,null,null)){
      Type t=(Type)convert(ctx,0);
      ParseTree var=ctx.getChild(1);
      if (var instanceof ParserRuleContext){
        ASTNode v=convert(ctx,1);
        if (v instanceof DeclarationStatement){
          VariableDeclaration decl=create.variable_decl(t);
          decl.add((DeclarationStatement)v);
          ASTDeclaration vars[]=decl.flatten();
          if (vars.length==1) return vars[0];
        } else if (v instanceof NameExpression){
          String name=((NameExpression)v).getName();
          return create.field_decl(name,t);
        }
      } else {
        String name=getIdentifier(ctx,1);
        return create.field_decl(name,t);
      }
    }
    return null;    
  }

}
