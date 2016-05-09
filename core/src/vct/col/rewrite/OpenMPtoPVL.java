package vct.col.rewrite;

import java.util.Stack;

import org.antlr.v4.runtime.tree.ParseTree;

import vct.antlr4.parser.OMPParser;
import vct.antlr4.parser.OMPpragma;
import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;

public class OpenMPtoPVL extends AbstractRewriter {

  public OpenMPtoPVL(ProgramUnit source) {
    super(source);
  }

  public void visit(BlockStatement block){
    enterCurrentBlock(create.block());
    do_block(block.getStatements(),0,block.getLength());
    result=leaveCurrentBlock();
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
              enterCurrentBlock(dst_block);
              do_block(src_block,lo,hi);
              leaveCurrentBlock();
              DeclarationStatement range=create.field_decl("omp_iter",
                  create.primitive_type(Sort.Integer),
                  create.expression(StandardOperator.RangeSeq,create.constant(0),create.unresolved_name("NUM_TRHEADS")));
              ParallelBlock pblock=create.parallel_block("omp_main",
                  cb.getContract(),
                  new DeclarationStatement[]{ range },
                  dst_block);
              currentBlock.add(create.region(pblock));
              continue;
            } else {
              create.enter(s);
              Fail("illegally placed pragma: omp %s",pragma);
            }
          case ParallelFor:
            parallel=true;
          case For:
            if (statements[i+1] instanceof LoopStatement){
              LoopStatement loop=(LoopStatement)statements[i+1];
              i=i+1;
              String var_name="iii";
              ASTNode lo=create.constant(0);
              ASTNode hi=create.constant(481);
              
              OperatorExpression init=(OperatorExpression)loop.getInitBlock();
              var_name=init.getArg(0).toString();
              lo=rewrite(init.getArg(1));
              OperatorExpression cond=(OperatorExpression)loop.getEntryGuard();
              hi=rewrite(cond.getArg(1));
              
              DeclarationStatement range=create.field_decl(var_name,
                  create.primitive_type(Sort.Integer),
                  create.expression(StandardOperator.RangeSeq,lo,hi));
              BlockStatement body=(BlockStatement)rewrite(loop.getBody());
              if (!parallel){
                body= create.block(
                  create.ifthenelse(create.expression(StandardOperator.EQ,
                    create.expression(StandardOperator.IterationOwner,
                        create.local_name(var_name),
                        create.local_name("NUM_TRHEADS"),
                        create.expression(StandardOperator.Minus,hi,lo)
                    ),create.local_name("omp_iter")),body));
              }
              ParallelBlock pblock=create.parallel_block("omp_main",
                  rewrite(loop.getContract()),
                  new DeclarationStatement[]{ range },
                  body
              );
              currentBlock.add(create.region(pblock));        
              continue;
            } else {
              create.enter(s);
              Fail("illegally placed pragma omp %s",pragma);
            }          
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
