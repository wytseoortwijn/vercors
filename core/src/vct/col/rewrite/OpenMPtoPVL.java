package vct.col.rewrite;

import hre.HREError;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;

import org.antlr.v4.runtime.tree.ParseTree;

import vct.antlr4.parser.OMPParser;
import vct.antlr4.parser.OMPoption;
import vct.antlr4.parser.OMPpragma;
import vct.col.ast.*;
import vct.col.ast.ASTSpecialDeclaration.Kind;
import vct.col.ast.PrimitiveType.Sort;

interface PPLProgram {

  boolean static_schedule();

  boolean nowait();

}

class PPLCompose implements PPLProgram {
  
  public final PPLProgram P1;
  public final PPLOperator op;
  public final PPLProgram P2;
  
  public PPLCompose(PPLProgram P1,PPLOperator op,PPLProgram P2){
    this.P1=P1;
    this.op=op;
    this.P2=P2;
    if(op==PPLOperator.Fuse){
      PPLProgram Pred=P1;
      while(Pred instanceof PPLCompose){
        Pred=((PPLCompose)Pred).P2;
      }
      ((PPLParallel)P2).fused=((PPLParallel)Pred).number;
    }
    if (op==PPLOperator.Sequential){
      Set<Integer> all=get_nums(P1);
      add_nums(P2,all);
    }
  }

  private void add_nums(PPLProgram P, Set<Integer> all) {
    if (P instanceof PPLCompose){
      PPLCompose C=(PPLCompose)P;
      add_nums(C.P1,all);
      add_nums(C.P2,all);
      return;
    }
    if (P instanceof PPLParallel){
      PPLParallel par=(PPLParallel)P;
      par.preds.addAll(all);
      return;
    }
    throw new HREError("missing case %s",P.getClass());
  }

  private Set<Integer> get_nums(PPLProgram P) {
    if (P instanceof PPLCompose){
      PPLCompose C=(PPLCompose)P;
      Set<Integer> res=get_nums(C.P1);
      res.addAll(get_nums(C.P2));
      return res;
    }
    if (P instanceof PPLParallel){
      PPLParallel par=(PPLParallel)P;
      Set<Integer> res=new HashSet();
      res.add(par.number);
      return res;
    }
    throw new HREError("missing case %s",P.getClass());
  }

  @Override
  public boolean static_schedule() {
    return P1.static_schedule() && P2.static_schedule();
  }

  @Override
  public boolean nowait() {
    return P1.nowait() && P2.nowait();
  }
  
}

class PPLParallel implements PPLProgram {
  private static final AtomicInteger count=new AtomicInteger();
  
  public final OMPoption[] options;
  public final Contract contract;
  public final DeclarationStatement[] decls;
  public final BlockStatement body;
  public final int number;
  
  public int fused=0;
  public Set<Integer> preds=new HashSet();
  
  public PPLParallel(OMPoption[] options,Contract contract,BlockStatement body,DeclarationStatement ... decls){
    this.options=options;
    this.decls=decls;
    this.body=body;
    this.contract=contract;
    number=count.incrementAndGet();
  }

  @Override
  public boolean static_schedule() {
    return OMPoption.static_schedule(options);
  }

  @Override
  public boolean nowait() {
    return OMPoption.nowait(options);
  }

}

enum PPLOperator { Sequential, Fuse, Parallel }

public class OpenMPtoPVL extends AbstractRewriter {

  public OpenMPtoPVL(ProgramUnit source) {
    super(source);
  }

  public void visit(BlockStatement block){
    enterCurrentBlock(create.block());
    do_block(block.getStatements(),0,block.getLength());
    result=leaveCurrentBlock();
  }
  
  @Override
  public void visit(Method m){
    switch(m.name){
    case "omp_get_thread_num":
    case "omp_get_num_threads":
      Warning("removing method %s",m.name);
      return;
    default:
      super.visit(m);
      return;
    }
  }
    
  public void do_block(ASTNode statements[],int from,int upto){
    for(int i=from;i<upto;i++){
      ASTNode s=statements[i];
      if(s.isDeclaration(ASTSpecialDeclaration.Kind.Pragma)){
        String pragma=((ASTSpecialDeclaration)s).args[0].toString();
        System.err.printf("pragma [%s]%n",pragma);
        if (pragma.startsWith("omp")){
          pragma=pragma.substring(3).trim();
          OMPpragma command=OMPParser.parse(pragma);
          System.err.printf("type is %s%n",command.kind);
          boolean parallel=false;
          switch(command.kind){
          case Parallel:
            if (statements[i+1] instanceof BlockStatement){
              ASTNode src_block[]=((BlockStatement)statements[i+1]).getStatements();
              i=i+1;
              BlockStatement dst_block=create.block();
              ContractBuilder cb=new ContractBuilder();
              int lo=0;int hi=src_block.length;
              while(lo<hi && (src_block[lo] instanceof ASTSpecialDeclaration)){
                ASTSpecialDeclaration d=(ASTSpecialDeclaration)src_block[lo];
                switch(d.kind){
                case Requires:
                  cb.requires(rewrite(d.args[0]));
                  lo++;
                  continue;
                case Ensures:
                  cb.ensures(rewrite(d.args[0]));
                  lo++;
                  continue;
                default:
                  break;
                }
                break;
              }
              while(hi > lo && (src_block[hi-1] instanceof ASTSpecialDeclaration)){
                ASTSpecialDeclaration d=(ASTSpecialDeclaration)src_block[hi-1];
                switch(d.kind){
                case Ensures:
                  cb.ensures(rewrite(d.args[0]));
                  hi--;
                  continue;
                default:
                  break;
                }
                break;
              }
              PPLProgram ppl_program=do_ppl(src_block,lo,hi);
              currentBlock.add(create.region(cb.getContract(),ppl_to_ordered(ppl_program)));
              continue;
            } else {
              create.enter(s);
              Fail("illegally placed pragma: omp %s",pragma);
            }
          case ParallelFor:{
            PPLProgram ppl_program=do_for(command.options,statements[i+1]);
            i=i+1;
            currentBlock.add(create.region(null,ppl_to_ordered(ppl_program)));
            continue;
          }
          case For:
            Fail("pragma omp for is not allowed at the top level");
          default:
            Abort("Cannot translate pragma: omp %s",pragma);
          }
        } else {
          currentBlock.add(rewrite(s));
        }
      } else {
        currentBlock.add(rewrite(s));
      }
    }
  }

  private PPLProgram do_for(OMPoption[] options, ASTNode S) {
    if (!(S instanceof LoopStatement)){
      Fail("omp for only applies to loops");
    }
    LoopStatement loop=(LoopStatement)S;
    String var_name="iii";
    ASTNode lo=create.constant(0);
    ASTNode hi=create.constant(481);
    
    ASTNode init=loop.getInitBlock();
    if (init.isa(StandardOperator.Assign)){
      OperatorExpression tmp=(OperatorExpression)init;
      var_name=tmp.getArg(0).toString();
      lo=rewrite(tmp.getArg(1));
    } else if (init instanceof DeclarationStatement){
      DeclarationStatement tmp=(DeclarationStatement)init;
      var_name=tmp.name;
      lo=tmp.getInit();
    } else {
      Fail("missing case in for initialisation");
    }
    OperatorExpression cond=(OperatorExpression)loop.getEntryGuard();
    hi=rewrite(cond.getArg(1));
    
    DeclarationStatement range=create.field_decl(var_name,
        create.primitive_type(Sort.Integer),
        create.expression(StandardOperator.RangeSeq,lo,hi));
    BlockStatement body=(BlockStatement)rewrite(loop.getBody());
    return new PPLParallel(options,rewrite(loop.getContract()),body,range);
  }

  private PPLProgram do_ppl(ASTNode[] src_block, int lo, int hi) {
    ArrayList<PPLProgram> parts=new ArrayList();
    for(int i=lo;i<hi;i++){
      if (src_block[i].isDeclaration(ASTSpecialDeclaration.Kind.Pragma)){
        String pragma=((ASTSpecialDeclaration)src_block[i]).args[0].toString();
        System.err.printf("pragma [%s]%n",pragma);
        if (!pragma.startsWith("omp")){
          Warning("ignoring statement %d",i);
          continue;
        }
        pragma=pragma.substring(3).trim();
        OMPpragma command=OMPParser.parse(pragma);
        System.err.printf("type is %s%n",command.kind);
        switch(command.kind){
        case For:{
          while(i+1<hi && src_block[i+1].isDeclaration(Kind.Comment)){
            i=i+1;
          }
          if (!(i+1<hi)){
            Fail("pragma without subsequent statement");
          }
          parts.add(do_for(command.options,src_block[i+1]));
          i=i+1;
          continue;
        }
        case ParallelFor:
        case Parallel:
          Fail("pragma omp parallel is not allowed at the task list level");
          continue;
        default:
          Abort("Cannot translate pragma: omp %s",pragma);
        }
      } else {
        Warning("ignoring statement %d",i);
      }
    }
    PPLOperator op[]=new PPLOperator[parts.size()];
    for(int i=0;i+1<parts.size();i++){
      PPLProgram P1=parts.get(i);
      PPLProgram P2=parts.get(i+1);
      if (P1.static_schedule()&&P1.nowait()&&P2.static_schedule()){
        op[i]=PPLOperator.Fuse;
      } else if (P1.nowait()){
        op[i]=PPLOperator.Parallel;
      } else {
        op[i]=PPLOperator.Sequential;
      }
    }
    PPLProgram res=null;
    int i=0;
    int N=parts.size()-1;
    op[N]=PPLOperator.Sequential;
    do {
      if(res!=null) i=i+1;
      PPLProgram par=null;
      do {
        if (par!=null) i=i+1;
        PPLProgram fuse=parts.get(i);
        while(op[i]==PPLOperator.Fuse){
          i=i+1;
          fuse=new PPLCompose(fuse,PPLOperator.Fuse,parts.get(i));
        }
        if (par==null){
          par=fuse;
        } else {
          par=new PPLCompose(par,PPLOperator.Parallel,fuse);
        }
      } while(i<N && op[i]==PPLOperator.Parallel);
      if (res==null){
        res=par;
      } else {
        res=new PPLCompose(res,PPLOperator.Sequential,par);
      }
    } while(i<N);
    return res;
  }

  private ParallelBlock[] ppl_to_ordered(PPLProgram ppl_program) {
    ArrayList<ParallelBlock> blocks=new ArrayList();
    scan(blocks,ppl_program);
    return blocks.toArray(new ParallelBlock[0]);
  }

  private void scan(ArrayList<ParallelBlock> blocks, PPLProgram ppl_program) {
    if (ppl_program instanceof PPLParallel){
      PPLParallel par=(PPLParallel)ppl_program;
      ArrayList<ASTNode> dep_list=new ArrayList();
      if(par.fused>0){
        dep_list.add(create.invokation(null,null,"omp_"+par.fused,
            create.unresolved_name(par.decls[0].name)));
      } else {
        for(int no:par.preds){
          dep_list.add(create.unresolved_name("omp_"+no));
        }
      }
      ASTNode deps[]=dep_list.toArray(new ASTNode[0]);
      blocks.add(create.parallel_block("omp_"+par.number,par.contract,par.decls,par.body,deps));
      return;
    }
    if (ppl_program instanceof PPLCompose){
      PPLCompose par=(PPLCompose)ppl_program;
      scan(blocks,par.P1);
      scan(blocks,par.P2);
      return;
    }
    throw new HREError("missing case %s",ppl_program.getClass());
  }

  private Stack<BlockStatement> currentBlockStack=new Stack();
  
  private BlockStatement leaveCurrentBlock() {
    BlockStatement res=currentBlock;
    currentBlock=currentBlockStack.pop();
    return res;
  }

  private void enterCurrentBlock(BlockStatement block) {
    currentBlockStack.push(currentBlock);
    currentBlock=block;
  }
  
}
