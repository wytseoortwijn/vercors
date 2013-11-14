package vct.antlr4.parser;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import hre.ast.FileOrigin;
import hre.ast.Origin;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import pv.parser.PVFullLexer;

import vct.col.ast.ASTNode;
import vct.col.ast.ASTSequence;
import vct.col.ast.BeforeAfterAnnotations;
import vct.col.ast.BlockStatement;
import vct.col.ast.CompilationUnit;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.VariableDeclaration;
import vct.col.util.ASTFactory;
import vct.parsers.CLexer;
import vct.parsers.CParser.AdditiveExpressionContext;
import vct.util.Syntax;

import static hre.System.*;

public class VCTVisitor implements ParseTreeVisitor<ASTNode> {

  protected final Syntax syntax;
  protected final ASTFactory<ParseTree> create=new ASTFactory<ParseTree>();
  protected final BufferedTokenStream tokens;
  protected final String filename;
  protected String current_filename;
  protected CompilationUnit unit;
  protected final org.antlr.v4.runtime.Parser parser;
  protected final int id_token;
  protected final int ch_comment;
  protected final int ch_control;
  protected final int ch_line_direction;
  private HashSet<Integer> attached_comments=new HashSet<Integer>();
  private HashSet<Integer> interpreted_directions=new HashSet<Integer>();
  protected HashMap<String,Class<?>> context=new HashMap<String,Class<?>>();

  public VCTVisitor(Syntax syntax,String filename,BufferedTokenStream tokens,
      org.antlr.v4.runtime.Parser parser, int identifier, Class<?> lexer_class){
    this.syntax=syntax;
    this.filename=filename;
    current_filename=filename;
    this.tokens=tokens;
    this.parser=parser;
    this.id_token=identifier;
    unit=new CompilationUnit(filename);
    ch_comment=getStaticInt(lexer_class,"COMMENT");
    ch_control=getStaticInt(lexer_class,"CONTROL");
    ch_line_direction=getStaticInt(lexer_class,"LINEDIRECTION");
    Class<?> parser_classes[]=parser.getClass().getDeclaredClasses();
    for(Class<?> cl:parser_classes){
      context.put(cl.getName(),cl);
    }
  }

  
  private int line_offset;
  
  public Origin origin(Token tok1,Token tok2){
    List<Token> direction=tokens.getHiddenTokensToLeft(tok1.getTokenIndex(),ch_line_direction);
    if (direction!=null) {
      for(Token tok:direction){
        int id=tok.getTokenIndex();
        if (interpreted_directions.contains(id)) continue;
        interpreted_directions.add(id);
        String line[]=tok.getText().split("([ \t])+");
        Debug("line %d maps to line %s of file %s",tok.getLine(),line[1],line[2]);
        line_offset=Integer.parseInt(line[1])-tok.getLine()-1;
        current_filename=line[2].substring(1,line[2].length()-1);
        
      }
      Debug("line offset in %s is %d",current_filename,line_offset);
    }
    return new FileOrigin(current_filename,line_offset+tok1.getLine(),tok1.getCharPositionInLine()+1,
        line_offset+tok2.getLine(),tok2.getCharPositionInLine()+tok2.getStopIndex()-tok2.getStartIndex()+1);
    
  }

  public static int getStaticInt(Class<?> cl,String field){
    try {
      Field f=cl.getDeclaredField(field);
      return f.getInt(null);
    } catch (NoSuchFieldException e) {
      e.printStackTrace();
    } catch (SecurityException e) {
      e.printStackTrace();
    } catch (IllegalArgumentException e) {
      e.printStackTrace();
    } catch (IllegalAccessException e) {
      e.printStackTrace();
    }
    throw hre.System.Failure("class has no static field %s",field);
  }
  
  public void enter(ParseTree node){
    create.enter();
    Origin origin;
    if (node instanceof ParserRuleContext){
      ParserRuleContext ctx=(ParserRuleContext)node;
      origin=origin(ctx.start,ctx.stop);
    } else  if (node instanceof TerminalNode) {
      Token tok=((TerminalNode)node).getSymbol();
      origin=origin(tok,tok);
    } else {
      throw Failure("unknown parse tree node: %s",node.getClass());
    }
    create.setOrigin(origin);
  }

  public void leave(ParseTree node, ASTNode res) {
    if (//res instanceof vct.col.ast.MethodInvokation ||
        res instanceof vct.col.ast.LoopStatement){
      BeforeAfterAnnotations loc=(BeforeAfterAnnotations)res;
      BlockStatement block;
      block=loc.get_before();
      scan_loop_comments_before(block,node);
      block=loc.get_after();
      scan_comments_after(block,node);
    }
    create.leave();
  }
  
  public void scan_to(ASTSequence<?> unit,ParseTree tree){
    try {
      scan_to_rec(unit,tree);
    } catch(MissingCase mc) {
      Warning("in tree %s:",tree.toStringTree(parser));
      throw mc;
    }
  }
  public void scan_to(ASTSequence<?> unit,ParserRuleContext ctx,int from,int upto){
    for(int i=from;i<upto;i++){
      try {
        BlockStatement temp=new BlockStatement();
        scan_to_rec(temp,ctx.getChild(i));
        scan_comments_before(unit,ctx.getChild(i));
        for(ASTNode n:temp){
          n.clearParent();
          unit.add(n);
        }
      } catch(MissingCase mc) {
        Warning("in tree %s:",ctx.getChild(i).toStringTree(parser));
        throw mc;
      }
    }
    if (upto>from){
      scan_comments_after(unit,ctx.getChild(upto-1));
    }
  }
  public void scan_loop_comments_before(ASTSequence<?> unit,ParseTree tree){
    Token tok;
    if (tree instanceof TerminalNode){
      tok=((TerminalNode)tree).getSymbol();
    } else {
      tok=((ParserRuleContext)tree).start;
    }
    List<Token> comments=tokens.getHiddenTokensToLeft(tok.getTokenIndex(),ch_comment);
    boolean take=false;
    if (comments!=null) for(Token tk:comments){
      int id=tk.getTokenIndex();
      if (!attached_comments.contains(id)){
        if (!take){
          take=tk.getText().contains("loop_invariant");
        }
        if (take) {
          attached_comments.add(id);
          Debug("attaching %s",tk.getText());
          unit.add(comment(tk));
        } else {
          Debug("skipping %s",tk.getText());
        }
      } else {
        Debug("skipping %s",tk.getText());
      }
    }    
  }
  public void scan_comments_before(ASTSequence<?> unit,ParseTree tree){
    Token tok;
    if (tree instanceof TerminalNode){
      tok=((TerminalNode)tree).getSymbol();
    } else {
      tok=((ParserRuleContext)tree).start;
    }
    List<Token> comments=tokens.getHiddenTokensToLeft(tok.getTokenIndex(),ch_comment);
    if (comments!=null) for(Token tk:comments){
      int id=tk.getTokenIndex();
      if (!attached_comments.contains(id)){
        attached_comments.add(id);
        Debug("attaching %s",tk.getText());
        unit.add(comment(tk));
      } else {
        Debug("skipping %s",tk.getText());
      }
    }    
  }
  public void scan_comments_after(ASTSequence<?> unit,ParseTree tree){
    Token tok;
    if (tree instanceof TerminalNode){
      tok=((TerminalNode)tree).getSymbol();
      if (tok.getType()<0) return; // EOF??
    } else {
      tok=((ParserRuleContext)tree).stop;
    }
    List<Token> comments=tokens.getHiddenTokensToRight(tok.getTokenIndex(),ch_comment);
    if (comments!=null) for(Token tk:comments){
      int id=tk.getTokenIndex();
      if (!attached_comments.contains(id)){
        attached_comments.add(id);
        Debug("attaching %s",tk.getText());
        unit.add(comment(tk));
      } else {
        Debug("skipping %s",tk.getText());
      }
    }    
  }
  
  private void scan_to_rec(ASTSequence<?> unit,ParserRuleContext ctx,int from,int upto){
    for(int i=from;i<upto;i++){
      BlockStatement temp=new BlockStatement();
      scan_to_rec(temp,ctx.getChild(i));
      scan_comments_before(unit,ctx.getChild(i));
      for(ASTNode n:temp){
        n.clearParent();
        unit.add(n);
      }
    }
    if (upto>from) scan_comments_after(unit,ctx.getChild(upto-1));
  }
  private void scan_to_rec(ASTSequence<?> unit,ParseTree tree){
    enter(tree);
    ASTNode res=tree.accept(this);
    if (res==null){
      res=visit(tree);
    }
    leave(tree,res);
    scan_comments_before(unit,tree);
    if (res==null){
      if (tree instanceof ParserRuleContext){
        ParserRuleContext ctx=(ParserRuleContext)tree;
        scan_to_rec(unit,ctx,0,ctx.getChildCount());
      } else if (tree instanceof TerminalNode){
        TerminalNode n=(TerminalNode)tree;
        if (n.getSymbol().getType()!=Recognizer.EOF){
          throw new MissingCase("missing case in %s: %s%ntree: %s%nat: %s",
              this.getClass(),tree.getClass(),tree.toStringTree(parser),
              create.getOrigin());
        }
      }
    } else {
      unit.add(res);
    }
  }
  
  public ASTNode comment(Token tk){
    create.enter();
    create.setOrigin(origin(tk,tk));
    ASTNode res=create.comment(tk.getText());
    create.leave();    
    return res;
  }
  
  public ASTNode convert(ParseTree arg0){
    enter(arg0);
    ASTNode res=arg0.accept(this);
    if (res==null){
      res=visit(arg0);
    }
    if (res==null){
      throw new MissingCase("missing case in %s: %s%ntree: %s%nat %s",
          this.getClass(),arg0.getClass(),arg0.toStringTree(parser),create.getOrigin());
    }
    leave(arg0,res);
    return res;
  }
    
  @Override
  public ASTNode visit(ParseTree arg0) {
    if (arg0 instanceof ParserRuleContext){
      Debug("Scanning using Syntax");
      ParserRuleContext ctx=(ParserRuleContext)arg0;
      if (ctx.children.size()==1){
        ParseTree tmp=ctx.getChild(0);
        if (tmp instanceof ParserRuleContext) {
          return convert(tmp);
        } else {
          for(PrimitiveType.Sort sort:PrimitiveType.Sort.values()){
            String text=syntax.getPrimitiveType(sort);
            if (text!=null && match(ctx,text)){
              return create.primitive_type(sort);
            }
          }
        }
        if (tmp instanceof TerminalNode){
          Token tok=((TerminalNode)tmp).getSymbol();
          if (tok.getType()==id_token) {
            return create.unresolved_name(tok.getText());
          }
          if(syntax.is_reserved(tok.getText())){
            return create.reserved_name(syntax.reserved(tok.getText()));
          }
        }
        return null;
        //throw Failure("missing case in %s: %s%ntree: %s",this.getClass(),arg0.getClass(),arg0.toStringTree(parser));
      }
      for(StandardOperator op:StandardOperator.values()){
        String pat[]=syntax.getPattern(op);
        if (pat!=null){
          Debug("Scanning for %s",op);
          //System.out.printf("pattern of %s:",op);
          //for(int k=0;k<pat.length;k++){
          //  System.out.printf(" %s",pat[k]);
          //}
          //System.out.printf("%n");
          if (match(ctx,pat)){
            int N=op.arity();
            ASTNode args[]=new ASTNode[N];
            int i=0;
            int j=0;
            while(j<N){
              if (pat[i]==null){
                args[j]=convert(arg0.getChild(i));
                j++;
              }
              i++;
            }
            return create.expression(op,args);
          }
        }
      }
      if (match(ctx,"(",null,")")){
        return convert(ctx,1);
      }
    } else if (arg0 instanceof TerminalNode){
      Token tok=((TerminalNode)arg0).getSymbol();
      if (tok.getType()==id_token) {
        return create.unresolved_name(tok.getText());
      }
    }
    return null;
    //throw Failure("missing case in %s: %s%ntree: %s",this.getClass(),arg0.getClass(),arg0.toStringTree(parser));
  }

  @Override
  public ASTNode visitChildren(RuleNode arg0) {
    throw Failure("illegal call to %s.visitChildren",this.getClass());
  }

  @Override
  public ASTNode visitErrorNode(ErrorNode arg0) {
    return visit(arg0);
  }

  @Override
  public ASTNode visitTerminal(TerminalNode arg0) {
    return visit(arg0);
  }

  protected ASTNode convert(ParserRuleContext ctx,int i){
    return convert(ctx.children.get(i));
  }
  protected ASTNode[] convert_all(ParserRuleContext ctx){
    int N;
    if (ctx.children==null) N=0; else N=ctx.children.size();
    ASTNode[] res=new ASTNode [N];
    for(int i=0;i<N;i++){
      res[i]=convert(ctx,i);
    }
    return res;
  }
  protected ASTNode[] convert_range(ParserRuleContext ctx,int from,int upto){
    int N=upto-from;
    ASTNode[] res=new ASTNode [N];
    for(int i=0;i<N;i++){
      res[i]=convert(ctx,from+i);
    }
    return res;
  }
  
  protected ASTNode[] convert_list(ParserRuleContext ctx,String open,String sep,String close){
    int N=ctx.getChildCount();
    if (match(0,true,ctx,open)&&match(N-1,true,ctx,close)){
      return convert_list(ctx,1,N-1,sep);
    }
    return null;
  }

  
  protected ASTNode[] convert_list(ParserRuleContext ctx,String sep){
    if (ctx==null || ctx.children==null) {
      return new ASTNode[0];
    } else {
      return convert_list(ctx,0,ctx.getChildCount(),sep);
    }
  }
  protected ASTNode[] convert_list(ParserRuleContext ctx,int from,int upto,String sep){
    int N=(upto-from+1)/2;
    ASTNode[] res=new ASTNode [N];
    for(int i=0;i<N;i++){
      res[i]=convert(ctx,from+2*i);
      if (i+1<N && !match(from+2*i+1,true,ctx,sep)){
        Debug("bad separator");
        return null;
      }
    }
    return res;
  }

  protected static boolean match(ParserRuleContext ctx,Object ... pattern){
    return match(0,false,ctx,pattern);
  }
  protected static boolean match(int ofs,boolean prefix,ParserRuleContext ctx,Object ... pattern){
    if (ctx.children==null) return pattern.length==0 && ofs==0;
    if (ctx.children.size()<ofs+pattern.length) return false;
    if (!prefix && ctx.children.size()>ofs+pattern.length) return false;
    for(int i=0;i<pattern.length;i++){
      if (pattern[i]==null) continue;
      ParseTree item=ctx.children.get(ofs+i);
      if (pattern[i] instanceof String){
        if (item.toString().equals(pattern[i])) continue;
        return false;
      }
      if (pattern[i] instanceof Class){
        if(((Class)(pattern[i])).isInstance(item)) continue;
        return false;
      }
      Abort("cannot match %s",pattern[i].getClass());
    }
    return true;
  }
  
  protected String getIdentifier(ParserRuleContext ctx, int i) {
    ParseTree node=ctx.children.get(i);
    if (node==null) Fail("child %d does not exist",i);
    while(node instanceof ParserRuleContext){
      ParserRuleContext tmp=(ParserRuleContext)node;
      if (tmp.children.size()==1){
        node=tmp.getChild(0);
      } else {
        Fail("not a nested identifier%n%s",node.toStringTree(parser));
      }
    }
    if (node instanceof TerminalNode){
      Token tok=((TerminalNode)node).getSymbol();
      if (tok.getType()==id_token) {
        return tok.getText();
      }
    }
    Fail("child %d is not an identifier",i);
    return null;
  }
  
  public Contract getContract(ParserRuleContext ctx){
    ContractBuilder cb=new ContractBuilder();
    for(ParseTree t:ctx.children){
      if (t instanceof ParserRuleContext){
        ParserRuleContext clause=(ParserRuleContext)t;
        enter(clause);
        if (match(clause,"requires",null,";")){
          cb.requires(convert(clause,1));
        } else if (match(clause,"ensures",null,";")){
          cb.ensures(convert(clause,1));
        } else if (match(clause,"given",null,";")){
          ASTNode decl=convert(clause,1);
          if (decl instanceof DeclarationStatement){
            cb.given((DeclarationStatement)convert(clause,1));
          } else if (decl instanceof VariableDeclaration){
            cb.given((VariableDeclaration)convert(clause,1));
          }
        } else if (match(clause,"yields",null,";")){
          ASTNode decl=convert(clause,1);
          if (decl instanceof DeclarationStatement){
            cb.yields((DeclarationStatement)convert(clause,1));
          } else if (decl instanceof VariableDeclaration){
            cb.yields((VariableDeclaration)convert(clause,1));
          }          
        }  else {
          throw hre.System.Failure("bad clause %s",t);
        }
        leave(clause,null);
      } else {
        throw hre.System.Failure("bad clause %s",t);
      }
    }
    Contract res=cb.getContract(false);
    res.setOrigin(origin(ctx.start,ctx.stop));
    return res;    
  }

}
