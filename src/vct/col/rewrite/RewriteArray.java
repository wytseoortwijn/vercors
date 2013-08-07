package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Hashtable;

import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.BindingExpression;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.BlockStatement;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.IntegerValue;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static vct.col.ast.PrimitiveType.Sort.Array;
import static vct.col.ast.PrimitiveType.Sort.Cell;
import static vct.col.ast.PrimitiveType.Sort.Sequence;
import vct.col.ast.ProgramUnit;
import vct.col.util.SimpleTypeCheck;

public class RewriteArray extends AbstractRewriter {

  protected static final String SUB_ARRAY = "__sub_array_";
  private boolean in_loop_invariant=false;
  private LoopStatement current_loop;
  private ArrayList<ASTNode> ensures_block;
  private Hashtable<String,ArrayList<ASTNode>> requires_table=new Hashtable<String,ArrayList<ASTNode>>();
  
  public RewriteArray(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(LoopStatement s) {
    //checkPermission(s);
    LoopStatement res=new LoopStatement();
    ASTNode tmp;
    tmp=s.getInitBlock();
    if (tmp!=null) res.setInitBlock(tmp.apply(this));
    tmp=s.getUpdateBlock();
    if (tmp!=null) res.setUpdateBlock(tmp.apply(this));
    tmp=s.getEntryGuard();
    if (tmp!=null) res.setEntryGuard(tmp.apply(this));
    tmp=s.getExitGuard();
    if (tmp!=null) res.setExitGuard(tmp.apply(this));
    in_loop_invariant=true;
    LoopStatement tmp_loop=current_loop;
    current_loop=res;
    for(ASTNode inv:s.getInvariants()){
      res.appendInvariant(inv.apply(this));
    }
    current_loop=tmp_loop;
    in_loop_invariant=false;
    tmp=s.getBody();
    res.setBody(tmp.apply(this));
    res.set_before(rewrite(s.get_before()));
    res.set_after(rewrite(s.get_after()));
    res.setOrigin(s.getOrigin());
    result=res; return ;
  }

  @Override
  public void visit(PrimitiveType t){
    switch(t.sort){
      case Array:
      {
        result=create.primitive_type(Sequence,create.primitive_type(Cell,rewrite(t.getArg(0))));
        break;
      }
      default:
        super.visit(t);
    }
  }
  
  @Override
  public void visit(OperatorExpression e){
    if (e.getOperator()==StandardOperator.ArrayPerm){
      Type t=(Type)(e.getArg(0).getType().getArg(0));
      ASTNode array_name=e.getArg(0);
      
      // Given a sub-array...
      String name=SUB_ARRAY+(++count);
      Type type=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t)));
      if (in_requires){
        currentContractBuilder.given(create.field_decl(name,type));
        requires_table.put(name,new ArrayList<ASTNode>());
      } else if (in_ensures) {
        currentContractBuilder.yields(create.field_decl(name,type));
      } else if (in_loop_invariant) {
        currentBlock.add_statement(create.field_decl(name,type));
      } else {
        Fail("ArrayPerm in unknown/unimplemented context");
      }
      boolean singleton=false;
      if (e.getArg(3) instanceof ConstantExpression){
        ConstantExpression c=(ConstantExpression)e.getArg(3);
        if (c.getValue() instanceof IntegerValue){
          singleton=((IntegerValue)c.getValue()).value==1;
        }
      }
      ASTNode tmp;
      DeclarationStatement args[]=new DeclarationStatement[1];
      args[0]=create.field_decl(name+"_i",create.primitive_type(Sort.Integer));
      ASTNode res=create.binder(
          BindingExpression.Binder.FORALL,
          null,
          args,
          create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name(name+"_i")),
              create.expression(StandardOperator.LT,create.local_name(name+"_i"),
                  create.expression(StandardOperator.Size,rewrite(array_name))
              )
          ),
          create.expression(StandardOperator.NEQ,
              create.expression(StandardOperator.Subscript,
                  rewrite(array_name),
                  create.local_name(name+"_i")
              ),
              create.reserved_name(ASTReserved.Null)
          )
      );
      
      
      
      // the size of the sub-array is count.
      tmp=create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.local_name(name)),
          rewrite(e.getArg(3))
      );
      if (in_requires){
        currentContractBuilder.requires(tmp);
        requires_table.get(name).add(create.expression(StandardOperator.Assume, tmp));
      } else if (in_ensures) {
        currentContractBuilder.ensures(tmp);
        ensures_block.add(create.expression(StandardOperator.Assume, tmp));
      } else if (in_loop_invariant) {
        currentBlock.add_statement(create.expression(StandardOperator.Assume, tmp));
        current_loop.appendInvariant(tmp);
      } else {
        Fail("ArrayPerm in unknown/unimplemented context");
      }

      DeclarationStatement decl[]=new DeclarationStatement[1];
      String vname="_auto_i_";
      decl[0]=create.field_decl(vname,create.primitive_type(PrimitiveType.Sort.Integer));
      if (singleton){
        tmp=create.expression(StandardOperator.And,
              create.expression(StandardOperator.LT,
                  rewrite(e.getArg(1)),
                  create.expression(StandardOperator.Size,rewrite(array_name))
              ),
              create.expression(StandardOperator.EQ,
                  create.expression(StandardOperator.Subscript,create.unresolved_name(name),create.constant(0)),
                  create.expression(StandardOperator.Subscript,rewrite(array_name),rewrite(e.getArg(1))
              )
            )             
        );
      } else {
        tmp=new BindingExpression(
            Binder.FORALL,
            create.primitive_type(PrimitiveType.Sort.Boolean),
            decl,
            create.expression(StandardOperator.And,
                create.expression(StandardOperator.LTE,create.constant(0),create.local_name(vname)),
                create.expression(StandardOperator.LT,create.local_name(vname),
                    create.expression(StandardOperator.Size,create.unresolved_name(name)))
            ),
            create.expression(StandardOperator.EQ,
                create.expression(StandardOperator.Subscript,
                    create.unresolved_name(name),create.local_name(vname)),
                create.expression(StandardOperator.Subscript,rewrite(array_name),
                   create.expression(StandardOperator.Plus,rewrite(e.getArg(1)),
                       create.expression(StandardOperator.Mult,rewrite(e.getArg(2)),
                           create.local_name(vname)
                       )
                   )
                )             
            )
        );
        tmp.setOrigin(e.getOrigin());
      }
      if (in_requires){
        currentContractBuilder.requires(tmp);
        requires_table.get(name).add(create.expression(StandardOperator.Assume, tmp));
      } else if (in_ensures) {
        currentContractBuilder.ensures(tmp);
        ensures_block.add(create.expression(StandardOperator.Assume, tmp));
      } else if (in_loop_invariant) {
        currentBlock.add_statement(create.expression(StandardOperator.Assume, tmp));
        current_loop.appendInvariant(tmp);
      } else {
        Fail("ArrayPerm in unknown/unimplemented context");
      }
      if (!singleton){
        tmp=new BindingExpression(
            Binder.FORALL,
            create.primitive_type(PrimitiveType.Sort.Boolean),
            decl,
            create.expression(StandardOperator.And,
              create.expression(StandardOperator.And,
                create.expression(StandardOperator.LTE,rewrite(e.getArg(1)),create.local_name(vname)),
                create.expression(StandardOperator.LT,create.local_name(vname),
                    create.expression(StandardOperator.Plus,rewrite(e.getArg(1)),
                        create.expression(StandardOperator.Mult,rewrite(e.getArg(2)),
                            rewrite(e.getArg(3))
                        )
                    )
                    )
              ),
              create.expression(StandardOperator.EQ,
                  create.expression(StandardOperator.Mod,create.local_name(vname),rewrite(e.getArg(2))),
                  rewrite(e.getArg(1))
              )
            ),
            create.expression(StandardOperator.EQ,
                create.expression(StandardOperator.Subscript,
                    rewrite(array_name),create.local_name(vname)),
                create.expression(StandardOperator.Subscript,create.unresolved_name(name),
                   create.expression(StandardOperator.Div,
                       create.expression(StandardOperator.Minus,
                           create.local_name(vname),
                           rewrite(e.getArg(1))
                       ),
                       rewrite(e.getArg(2))
                   )
                )             
            )
        );
        tmp.setOrigin(e.getOrigin());
        if (in_requires){
          currentContractBuilder.requires(tmp);
          requires_table.get(name).add(create.expression(StandardOperator.Assume, tmp));
        } else if (in_ensures) {
          currentContractBuilder.ensures(tmp);
          ensures_block.add(create.expression(StandardOperator.Assume, tmp));
        } else if (in_loop_invariant) {
          currentBlock.add_statement(create.expression(StandardOperator.Assume, tmp));
        } else {
          Fail("ArrayPerm in unknown/unimplemented context");
        }
      }
      // permission on the sub-array.
      tmp=create.expression(StandardOperator.Perm,
          create.dereference(
              create.expression(StandardOperator.Subscript,
                  create.local_name(name),
                  create.reserved_name(ASTReserved.Any)
              ), "item"
          ),
          rewrite(e.getArg(4))
      );
      res=create.expression(StandardOperator.Star,res,tmp);
      
      result=res;
      return;
    }
    if (e.getOperator()==StandardOperator.Perm && e.getArg(0).isa(StandardOperator.Subscript)){
      if (!(((OperatorExpression)e.getArg(0)).getArg(1).isReserved(ASTReserved.Any))){
        Fail("Cannot use Perm for array elements, use ArrayPerm instead.");
      }
    }
    super.visit(e);
    if (e.getOperator()==StandardOperator.Subscript && ((PrimitiveType)e.getArg(0).getType()).sort==Array){
       result=create.dereference(result,"item");
    } else if (e.getOperator()==StandardOperator.Perm
             && (e.getArg(0) instanceof OperatorExpression)
             && (((OperatorExpression)e.getArg(0)).getOperator()==StandardOperator.Subscript)
             && (((OperatorExpression)e.getArg(0)).getArg(1).isReserved(ASTReserved.Any))
    ){
      ASTNode res=result;
      DeclarationStatement decl[]=new DeclarationStatement[1];
      String arrayname=((OperatorExpression)e.getArg(0)).getArg(0).toString();
      String name="_auto_i_";
      decl[0]=create.field_decl(name,create.primitive_type(PrimitiveType.Sort.Integer));
      ASTNode tmp=new BindingExpression(
          Binder.FORALL,
          create.primitive_type(PrimitiveType.Sort.Boolean),
          decl,
          create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name(name)),
              create.expression(StandardOperator.LT,create.local_name(name),
                  create.expression(StandardOperator.Size,create.unresolved_name(arrayname)))
          ),
          create.expression(StandardOperator.NEQ,
              create.expression(StandardOperator.Subscript,create.unresolved_name(arrayname),create.local_name(name))
              ,create.reserved_name(ASTReserved.Null))
      );
      tmp.setOrigin(result.getOrigin());
      result=create.expression(StandardOperator.Star,res,tmp);
    }
  }
  
  private int count=0;
  
  @Override
  public void visit(BindingExpression e){
    if (e.binder==BindingExpression.Binder.STAR){
      Fail("resource conjunctions are not allowed at the array rewriting stage");
    }
    super.visit(e);
  }
  
  @Override
  public void visit(Method m){
    //checkPermission(m);
    String name=m.getName();
    int N=m.getArity();
    currentContractBuilder=new ContractBuilder();
    DeclarationStatement args[]=rewrite(m.getArgs());
    Contract mc=m.getContract();
    if (mc!=null){
      ensures_block=new ArrayList<ASTNode>();
      rewrite(mc,currentContractBuilder);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    ASTNode body=rewrite(m.getBody());
    if (mc!=null && body instanceof BlockStatement){
      BlockStatement block=(BlockStatement)body;
      for (ASTNode stat:ensures_block){
        block.add_statement(copy_rw.rewrite(stat));
      }
    }
    Contract c=currentContractBuilder.getContract();
    currentContractBuilder=null;
    result=create.method_kind(kind, rt, c, name, args, m.usesVarArgs(), body);
  }
  
  @Override
  public ProgramUnit rewriteAll(){
    ProgramUnit phase1=super.rewriteAll();
    phase1=new Standardize(phase1).rewriteAll();
    new SimpleTypeCheck(phase1).check();
    return new RewriteArrayArguments(phase1,requires_table).rewriteAll();
  }

}

class RewriteArrayArguments extends AbstractRewriter {
  private Hashtable<String,ArrayList<ASTNode>> requires_table;
  private int count=0;
  
  public RewriteArrayArguments(ProgramUnit source,Hashtable<String,ArrayList<ASTNode>> requires_table) {
    super(source);
    this.requires_table=requires_table;
  }

  @Override
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    Contract c=m.getContract();
    if (c!=null){
      BlockStatement init_block=e.get_before();
      if (init_block==null) init_block=create.block(); else init_block=rewrite(init_block);
      BlockStatement exit_block=e.get_after();
      if (exit_block==null) exit_block=create.block(); else exit_block=rewrite(exit_block);
      for(DeclarationStatement decl:c.given){
        String given_name=decl.getName();
        if (given_name.startsWith(RewriteArray.SUB_ARRAY)){
          String let_name=given_name+"_"+(++count);
          currentBlock.add_statement(create.field_decl(let_name, rewrite(decl.getType())));
          Hashtable<NameExpression,ASTNode> map=new Hashtable<NameExpression,ASTNode>();
          map.put(create.local_name(given_name),create.local_name(let_name));
          Substitution sigma=new Substitution(source(),map);
          for (ASTNode s:requires_table.get(given_name)){
            ASTNode tmp=sigma.rewrite(s);
            tmp.setFlag(ASTFlags.GHOST,true);
            currentBlock.add_statement(tmp);
          }
          ASTNode tmp=create.assignment(create.label(given_name),create.local_name(let_name));
          init_block.add_statement(tmp);
        }
      }
      for(DeclarationStatement decl:c.yields){
        String given_name=decl.getName();
        if (given_name.startsWith(RewriteArray.SUB_ARRAY)){
          String let_name=given_name+"_"+(++count);
          currentBlock.add_statement(create.field_decl(let_name, rewrite(decl.getType())));
          Hashtable<NameExpression,ASTNode> map=new Hashtable<NameExpression,ASTNode>();
          map.put(create.local_name(given_name),create.local_name(let_name));
          Substitution sigma=new Substitution(source(),map);
          ASTNode tmp=create.assignment(create.local_name(let_name),create.label(given_name));
          exit_block.add_statement(tmp);     
        }
      }
      MethodInvokation call=create.invokation(rewrite(e.object), rewrite(e.dispatch), e.method, rewrite(e.getArgs()));
      call.set_before(init_block);
      call.set_after(exit_block);
      result=call;
    } else {
      super.visit(e);
    }
  }
}