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
import static vct.col.ast.ASTSpecial.Kind.Comment;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.Lexer;

public class CommentRewriter extends AbstractRewriter {

  private CommentParser parser;
  private Lexer lexer;
  
  public CommentRewriter(ProgramUnit source, CommentParser parser) {
    super(source);
    this.parser=parser;
  }

  private ArrayList<ASTSpecial> queue=new ArrayList<ASTSpecial>();
  private Contract contract;

  private InputStream grabQueue(){
    final FifoStream fifo=new FifoStream(4096);
    final ArrayList<ASTSpecial> my_queue=new ArrayList<ASTSpecial>(queue);
    queue.clear();
    new Thread(){
      @Override
      public void run(){
        PrintStream out=new PrintStream(fifo.getOutputStream());
        for (ASTSpecial s:my_queue){
          String comment=s.args[0].toString();
          if (comment.startsWith("//@")){
            FileOrigin o=(FileOrigin)s.getOrigin();
            //System.out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            //System.out.println(comment.substring(3));
            out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            for(int S=3+o.getFirstColumn();S>0;S--){
              out.print(" ");
            }
            out.println(comment.substring(3));
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
            out.printf("# %d \"%s\"%n",o.getFirstLine(),o.getName());
            for(int S=N+o.getFirstColumn();S>0;S--){
              out.print(" ");
            }
            out.println(comment.substring(3,comment.length()-N));
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
    if (!(node instanceof ASTSpecial) || ((ASTSpecial)node).kind!=Comment){
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
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Comment:{
      String comment=s.args[0].toString();
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
    BlockStatement filtered=create.block();
    super.visit(s);
    s=(LoopStatement)result;
    BlockStatement before=s.get_before();
    s.set_before(filtered);
    for(ASTNode n:before){
      n.clearParent();
      if (n instanceof ASTSpecial && ((ASTSpecial)n).kind==ASTSpecial.Kind.Invariant){
        s.appendInvariant(((ASTSpecial)n).args[0]);
      } else {
        filtered.add(n);
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
    if (queue.size()>0) parser.contract(currentBlock,grabQueue());
    result=currentBlock;
    currentBlock=save;
  }

}
