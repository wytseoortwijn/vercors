package vct.antlr4.parser;

import hre.ast.FileOrigin;
import hre.io.FifoStream;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import vct.col.ast.*;
import vct.col.rewrite.AbstractRewriter;
import vct.parsers.CMLLexer;
import vct.parsers.CMLParser;
import static hre.System.*;
import static vct.col.ast.ASTSpecialDeclaration.Kind.Comment;

import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.Lexer;

/**
 * Rewrite an AST with specifications in the form of comments
 * to an AST with specifications in the from of ASTs. 
 */
public class CommentRewriter extends AbstractRewriter {

  private CommentParser parser;
  private Lexer lexer;
  
  public CommentRewriter(ProgramUnit source, CommentParser parser) {
    super(source);
    this.parser=parser;
  }

  private ArrayList<ASTSpecialDeclaration> queue=new ArrayList<ASTSpecialDeclaration>();
  private Contract contract;

  private InputStream grabQueue(){
    final FifoStream fifo=new FifoStream(4096);
    final ArrayList<ASTSpecialDeclaration> my_queue=new ArrayList<ASTSpecialDeclaration>(queue);
    queue.clear();
    new Thread(){
      @Override
      public void run(){
        PrintStream out=new PrintStream(fifo.getOutputStream());
        int lines=0;
        for (ASTSpecialDeclaration s:my_queue){
          String comment=s.args[0].toString();
          if (comment.startsWith("//@")){
            FileOrigin o=(FileOrigin)s.getOrigin();
            //System.out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            //System.out.println(comment.substring(3));
            parser.ec.mark_ofs(lines,o.getName(),o.getFirstLine()-2);
            out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            for(int S=3+o.getFirstColumn();S>0;S--){
              out.print(" ");
            }
            out.println(comment.substring(3));
            lines+=3;
          } else if (comment.startsWith("/*@")){
            int N;
            if (comment.endsWith("@*/")){
              N=3;
            } else {
              N=2;
            }
            FileOrigin o=(FileOrigin)s.getOrigin();
            //System.out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            //System.out.println(comment.substring(3,comment.length()-N));
            parser.ec.mark_ofs(lines,o.getName(),o.getFirstLine()-2);
            out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            for(int S=N+o.getFirstColumn();S>0;S--){
              out.print(" ");
            }
            out.println(comment.substring(3,comment.length()-N));
            lines+=3;
            for(int i=0;i<comment.length();i++){
              if (comment.charAt(i)=='\n') lines++;
            }
          }
        }
        out.close();
      }
    }.start();
    return fifo.getInputStream();
  }
  @Override
  public void enter(ASTNode node){
    super.enter(node);
    if ((!(node instanceof ASTSpecialDeclaration) || ((ASTSpecialDeclaration)node).kind!=Comment) && !(node instanceof ConstantExpression)){
      if (queue.size()>0){
        contract=parser.contract(current_sequence(),grabQueue());
      }
    }
  }
  
  @Override
  public void visit(ASTClass c){
    ContractBuilder cb=new ContractBuilder();
    rewrite(c.getContract(),cb);
    c.setContract(null);
    if (contract!=null){
      rewrite(contract,cb);
      contract=null;
    }
    super.visit(c);
    c=(ASTClass)result;
    c.setContract(cb.getContract());
    if (queue.size()>0) {
      Contract c2=parser.contract(c,grabQueue());
      if (c2!=null) {
        throw Failure("at %s: Dangling contract at the end of class %s",c2.getOrigin(),c.getName());
      }
    }
    result=c;
  }
  @Override
  public void visit(Method m){
    if (contract!=null){
      if (m.getContract()!=null){
        throw Failure("refusing to erase existing contract");
      }
      m.setContract(contract);
      contract=null;
    }
    super.visit(m);
    if (m.annotated()){
      ASTNode tmp=result;
      for(ASTNode ann:m.annotations()){
        tmp.attach(rewrite(ann));
      }
      if (queue.size()>0){
    	parser.annotations(tmp,grabQueue());
      }
      result=tmp;
    }
    
  }
  
  @Override
  public void visit(ASTSpecialDeclaration s){
    switch(s.kind){
    case Comment:{
      String comment=s.args[0].toString();
      Debug("comment %s",comment);
      if (comment.startsWith("/*@")||comment.startsWith("//@")){
        queue.add(s);
        result=null;
      } else {
        super.visit(s);
      }
      break;
    }
    default:
      super.visit(s);
    }
  }
  
  @Override
  public void visit(LoopStatement s){
    BlockStatement new_before=create.block();
    BlockStatement new_after=create.block();
    super.visit(s);
    s=(LoopStatement)result;
    BlockStatement old_before=s.get_before();
    BlockStatement old_after=s.get_after();
    s.set_before(new_before);
    s.set_after(new_after);
    filter(s,new_before,new_after,new_before,old_before);
    filter(s,new_before,new_after,new_after,old_after);
  }
  
  private void filter(LoopStatement s,BlockStatement new_before, BlockStatement new_after,
      BlockStatement new_current, BlockStatement old_current)
  {
    for(ASTNode n:old_current){
      n.clearParent();
      if (n instanceof ASTSpecialDeclaration){
        //Warning("filtering %s",((ASTSpecial)n).kind);
        switch (((ASTSpecialDeclaration)n).kind) {
        case Invariant:
          Debug("appending invariant");
          s.appendInvariant(((ASTSpecialDeclaration)n).args[0]);
          break;
        case Contract:
          Debug("appending contract");
          s.appendContract((Contract)((ASTSpecialDeclaration)n).args[0]);
          break;
        default:
          new_current.add(n);
        }
      } else {
        new_current.add(n);
      }
    }
    
  }
  @Override
  public void visit(BlockStatement block){
    BlockStatement save=currentBlock;
    currentBlock=create.block();
    for(ASTNode item:block){
      currentBlock.add(rewrite(item));
    }
    if (queue.size()>0) {
      Contract c=parser.contract(currentBlock,grabQueue());
      if (c!=null) {
        currentBlock.add_statement(create.special_decl(ASTSpecialDeclaration.Kind.Contract, c));
      }
    }
    result=currentBlock;
    currentBlock=save;
  }

}
