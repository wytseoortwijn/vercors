package vct.col.rewrite;

import hre.ast.MessageOrigin;

import java.util.Stack;

import vct.col.ast.ASTNode;
import vct.col.ast.AssignmentStatement;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.FunctionType;
import vct.col.ast.IfStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.ReturnStatement;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

public class Flatten extends AbstractRewriter {

  public Flatten(ProgramUnit source) {
    super(source);
  }

  /* TODO check for pure expression while copying! */
  private AbstractRewriter copy_pure=new AbstractRewriter(source());
  
  private Stack<BlockStatement> block_stack=new Stack<BlockStatement>();
  private BlockStatement current_block=null;
  private BlockStatement declaration_block=null;
  private static long counter=0;
  
  public void visit(BlockStatement s){
    int N=s.getLength();
    block_stack.push(current_block);
    current_block=create.block();
    visit_body(s);
    result=current_block;
    current_block=block_stack.pop();
  }

  public void visit(MethodInvokation e) {
    Debug("call to %s",e.method);
    ASTNode object=rewrite(e.object);
    int N=e.getArity();
    ASTNode args[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      args[i]=e.getArg(i).apply(this);
    }
    String name="__flatten_"+(++counter);
    if (e.getType()==null){
      Abort("result type of call unknown at %s",e.getOrigin());
    }
    if (e.getType().isVoid()){
      result=create.invokation(object,rewrite(e.dispatch),e.method,args);
      ((MethodInvokation)result).set_before(copy_rw.rewrite(e.get_before()));
      ((MethodInvokation)result).set_after(copy_rw.rewrite(e.get_after()));
    } else {
      Debug("declaring variable %s (%s)",name,e.getType());
      ASTNode n=create.field_decl(name,e.getType());
      Debug("inserting in %s",declaration_block);
      declaration_block.add_statement(n);
      Debug("assigning resutl of call");
      MethodInvokation call=create.invokation(object,rewrite(e.dispatch),e.method,args);
      call.set_before(copy_pure.rewrite(e.get_before()));
      call.set_after(copy_pure.rewrite(e.get_after()));
      for(NameExpression lbl:e.getLabels()){
        Debug("FLATTEN: copying label %s",lbl);
        call.addLabel(lbl);
      }
      current_block.add_statement(create.assignment(create.local_name(name),call));
      Debug("return variable name");
      result=create.local_name(name);
      auto_labels=false;
    }
  }
 
  public void visit(OperatorExpression e){
    if (e.getType()==null) Abort("untyped operator %s in clause at %s",e.getOperator(),e.getOrigin());
    switch(e.getOperator()){
    case PreIncr:
    case PreDecr:
    {
      StandardOperator op=e.getOperator()==StandardOperator.PreIncr?StandardOperator.Plus:StandardOperator.Minus;
      ASTNode arg=e.getArg(0);
      ASTNode arg_out=arg.apply(this);
      String name="__flatten_"+(++counter);
      declaration_block.add_statement(create.field_decl(name,e.getType(),null));
      current_block.add_statement(create.assignment(arg_out,create.expression(op,arg_out,create.constant(1))));
      current_block.add_statement(create.assignment(create.local_name(name),arg_out));
      result=create.local_name(name);
      return;
    }
    case PostIncr:
    case PostDecr:
    {
      StandardOperator op=e.getOperator()==StandardOperator.PostIncr?StandardOperator.Plus:StandardOperator.Minus;
      ASTNode arg=e.getArg(0);
      ASTNode arg_out=arg.apply(this);
      String name="__flatten_"+(++counter);
      declaration_block.add_statement(create.field_decl(name,e.getType(),null));
      current_block.add_statement(create.assignment(create.local_name(name),arg_out));
      current_block.add_statement(create.assignment(arg_out,create.expression(op,arg_out,create.constant(1))));
      result=create.local_name(name);
      return;
    }
    case Assert:
    case Assume:
    case Fold:
    case HoarePredicate:
    case Unfold:
    {
      result=e.apply(copy_pure);
      return;      
    }
    default:
      super.visit(e);
      return;
    }
  }
  
  public void visit(DeclarationStatement s){
    Type t=s.getType();
    ASTNode tmp=t.apply(this);
    if (tmp instanceof Type){
      t=(Type)tmp;
    } else {
      throw new Error("type AST rewrote to non-type AST");
    }
    String name=s.getName();
    ASTNode init=s.getInit();
    if (init!=null) {
      current_block.add_statement(create.field_decl(name,t,null));
      init=init.apply(this);
      result=create.assignment(create.local_name(name),init);
    } else {
      result=create.field_decl(name,t,null);
    }
  }
  
  private ASTNode add_as_var(ASTNode e){
    String name="__flatten_"+(++counter);
    if (e.getType()==null){
      Abort("result type unknown at %s",e.getOrigin());
    }
    Type t=e.getType();
    if (t.getOrigin()==null){
      Warning("fixing null origin near %s",e.getOrigin());
      t.setOrigin(new MessageOrigin("Flatten.add_as_var fix near %s",e.getOrigin()));
    }
    ASTNode n=create.field_decl(name,t);
    declaration_block.add_statement(n);
    ASTNode ee=e.apply(this);
    current_block.add_statement(create.assignment(create.local_name(name),ee));
    return create.local_name(name);
  }

  public void visit(ReturnStatement s){
    ASTNode e=s.getExpression();
    if (e!=null){
      e=add_as_var(e);
      result=create.return_statement(e);
    } else {
      result=create.return_statement();
    }
    ((ReturnStatement)result).set_after(copy_rw.rewrite(s.get_after()));
  }
  private void visit_body(ASTNode body){
    if (body instanceof BlockStatement){
      BlockStatement s=(BlockStatement)body;
      int N=s.getLength();
      for(int i=0;i<N;i++){
        ASTNode stat=s.getStatement(i);
        if (stat instanceof ReturnStatement){
          // TODO: properly implement this with exec before and exec after.
          ASTNode last=stat.apply(this);
          for(i++;i<N;i++){
            visit_body(s.getStatement(i));
          }
          current_block.add_statement(last);
        } else {
          visit_body(s.getStatement(i));
        }
      }
    } else {
      current_block.add_statement(body.apply(this));
    }
  }
  
  public void visit(IfStatement s) {
    IfStatement res=new IfStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getCount();
    for(int i=0;i<N;i++){
      ASTNode guard=s.getGuard(i);
      if (guard!=IfStatement.else_guard) guard=guard.apply(copy_pure);
      block_stack.push(current_block);
      current_block=create.block();
      visit_body(s.getStatement(i));
      res.addClause(guard,current_block);
      current_block=block_stack.pop();
    }
    result=res; return ;
  }

  public void visit(Method m) {
    switch(m.kind){
    case Predicate:
    case Pure:
      result=copy_pure.rewrite(m);
      return;
    default:
      break;
    }
    String name=m.getName();
    int N=m.getArity();
    DeclarationStatement args[]=copy_pure.rewrite(m.getArgs());
    Contract mc=m.getContract();
    Contract c=null;
    if (mc!=null){
      ASTNode pre=mc.pre_condition.apply(copy_pure);
      ASTNode post=mc.post_condition.apply(copy_pure);
      c=new Contract(copy_pure.rewrite(mc.given),copy_pure.rewrite(mc.yields),
          copy_pure.rewrite(mc.modifies),pre,post);
    }
    Method.Kind kind=m.kind;
    Method res=create.method_kind(m.getOrigin(), kind,rewrite(m.getReturnType()) , c, name, args, m.usesVarArgs(),null);
    ASTNode body=m.getBody();
    if (body!=null) {
      if (body instanceof BlockStatement) {
        // if block
        block_stack.push(current_block);
        current_block=create.block();
        declaration_block=current_block;
        visit_body(body);
        res.setBody(current_block);
        current_block=block_stack.pop();
      } else {
        // if expression (pure function or predicate!)
        res.setBody(body.apply(copy_pure));
      }
    }
    result=res;
  }
  
  @Override
  public void visit(LoopStatement s) {
    //checkPermission(s);
    LoopStatement res=new LoopStatement();
    ASTNode tmp;
    tmp=s.getInitBlock();
    if (tmp!=null) res.setInitBlock(tmp.apply(copy_pure));
    tmp=s.getUpdateBlock();
    if (tmp!=null) res.setUpdateBlock(tmp.apply(copy_pure));
    tmp=s.getEntryGuard();
    if (tmp!=null) res.setEntryGuard(tmp.apply(copy_pure));
    tmp=s.getExitGuard();
    if (tmp!=null) res.setExitGuard(tmp.apply(copy_pure));
    for(ASTNode inv:s.getInvariants()){
      res.appendInvariant(inv.apply(copy_pure));
    }
    tmp=s.getBody();
    res.setBody(tmp.apply(this));
    res.setOrigin(s.getOrigin());
    res.set_before(copy_rw.rewrite(s.get_before()));
    res.set_after(copy_rw.rewrite(s.get_after()));
    result=res; return ;
  }

  @Override
  public void visit(Dereference e){
    if (e.object instanceof OperatorExpression
        && ((OperatorExpression)e.object).getOperator()==StandardOperator.Subscript
    ){
      ASTNode obj=e.object.apply(this);
      String name="__flatten_"+(++counter);
      declaration_block.add_statement(create.field_decl(name,e.object.getType(),null));
      current_block.add_statement(create.assignment(create.local_name(name),obj));
      result=create.dereference(create.local_name(name),e.field);
    } else {
      super.visit(e);
    }
  }
}
