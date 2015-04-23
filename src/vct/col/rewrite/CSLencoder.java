package vct.col.rewrite;

import java.util.HashMap;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.*;

public class CSLencoder extends AbstractRewriter {

  public CSLencoder(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(ASTClass cl){
    String name=cl.getName();
    if (name.startsWith("Atomic")){
      ASTClass res=create.ast_class(name, ASTClass.ClassKind.Plain,null, null,null);
      for(DeclarationStatement decl:cl.dynamicFields()){
        res.add_dynamic(rewrite(decl));
      }
      for(Method m:cl.dynamicMethods()){
        if (m.kind==Method.Kind.Constructor){
          res.add_dynamic(rewrite(m));
        }
      }
      result=res;
    } else {
      super.visit(cl);
    }
  }

  private AtomicInteger count=new AtomicInteger();
  
  @Override
  public void visit(MethodInvokation e){
    Method m=e.getDefinition();
    ASTClass cl=(ASTClass)m.getParent();
    String name=cl.getName();
    if (!(e.object instanceof ClassType) && name.startsWith("Atomic")){
      int no=count.incrementAndGet();
      String result_name="csl_result_"+no;
      String return_label="csl_return_"+no;
      /*
      String m_call_name="csl_call_"+no;
      String m_check_name="csl_check_"+no;
      ContractBuilder m_call_cb=new ContractBuilder();
      ContractBuilder m_check_cb=new ContractBuilder();
      BlockStatement  m_check_body=create.block();
      m_check_cb.requires(create.invokation(null,null,"csl_invariant"));
      m_check_body.add(create.expression(StandardOperator.Unfold,create.invokation(null,null,"csl_invariant")));
      
      boolean procedure=m.getReturnType().isVoid();
      
      if (!procedure){
        m_check_body.add(create.field_decl("check_result",rewrite(m.getReturnType())));
      }
      for(ASTNode s:e.get_before()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          ASTNode tmp=((ASTSpecial)s).args[0];
          m_call_cb.requires(rewrite(tmp));
          m_check_cb.requires(rewrite(tmp));
        } else {
          m_check_body.add(rewrite(s));
        }
      }
      HashMap<NameExpression, ASTNode> map=new HashMap<NameExpression, ASTNode>();
      map.put(create.reserved_name(ASTReserved.This), rewrite(e.object));
      int N=m.getArity();
      for(int i=0;i<N;i++){
        map.put(create.local_name(m.getArgument(i)),rewrite(e.getArg(i)));
      }
      Substitution sigma=new Substitution(source(), map);
      for(ASTNode s:((BlockStatement)m.getBody())){
        if (s instanceof ReturnStatement){
          ReturnStatement r=(ReturnStatement)s;
          ASTNode loc=create.local_name("check_result");
          ASTNode val=sigma.rewrite(r.getExpression());
          m_check_body.add(create.assignment(loc, val));
        } else {
          m_check_body.add(sigma.rewrite(s));
        }
      }
      for(ASTNode s:e.get_after()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          ASTNode tmp=((ASTSpecial)s).args[0];
          m_call_cb.ensures(rewrite(tmp));
          m_check_cb.ensures(rewrite(tmp));
        } else {
          m_check_body.add(rewrite(s));
        }       
      }
      
      m_check_body.add(create.expression(StandardOperator.Fold,create.invokation(null,null,"csl_invariant")));
      if (!procedure){
        m_check_body.add(create.return_statement(create.local_name("check_result")));
      }
      m_check_cb.ensures(create.invokation(null,null,"csl_invariant"));
      Method m_call=create.method_decl(
          rewrite(m.getReturnType()), m_call_cb.getContract(), m_call_name,
          rewrite(m.getArgs()), null);
      currentClass.add(m_call);
      Method m_check=create.method_decl(
          rewrite(m.getReturnType()), m_check_cb.getContract(), m_check_name,
          rewrite(m.getArgs()), m_check_body);
      currentClass.add(m_check);
      result=create.invokation(null, e.dispatch, m_call_name, rewrite(e.getArgs()));
      */
      BlockStatement block=currentBlock;
      if (!m.getReturnType().isVoid()){
        block.add(create.field_decl(result_name,rewrite(m.getReturnType())));
      }
      block.add(create.special(ASTSpecial.Kind.Inhale,create.invokation(null,null,"csl_invariant")));
      block.add(create.expression(StandardOperator.Unfold,create.invokation(null,null,"csl_invariant")));
      for(ASTNode s:e.get_before()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          // skip
        } else {
          block.add(rewrite(s));
        }
      }
      InlineMethod inline=new InlineMethod(source());
      inline.inline(block,result_name,return_label,m,e.object,e.getArgs(),e.getOrigin());    
      block.add(create.special(ASTSpecial.Kind.Label,create.label(return_label)));
      Hashtable map=new Hashtable();
      Substitution sigma=new Substitution(source(),map);
      map.put(create.reserved_name(ASTReserved.Result),create.local_name(result_name));
      for(ASTNode s:e.get_after()){
        if (s.isSpecial(ASTSpecial.Kind.Transfer)){
          // skip
        } else {
          block.add(sigma.rewrite(rewrite(s)));
        }
      }
      block.add(create.expression(StandardOperator.Fold,create.invokation(null,null,"csl_invariant")));
      block.add(create.special(ASTSpecial.Kind.Exhale,create.invokation(null,null,"csl_invariant")));
      if (m.getReturnType().isVoid()){
        result=create.comment("// dummy");
      } else {
        result=create.local_name(result_name);
      }
    } else {
      super.visit(e);
    }
    
  }
  
  
}
