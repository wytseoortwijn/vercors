package vct.col.rewrite;

import java.util.HashMap;
import java.util.Map;

import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.FunctionType;
import vct.col.ast.Method;
import vct.col.ast.NameExpression;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;

public class FinalizeArguments extends AbstractRewriter {

  public FinalizeArguments(ProgramUnit source) {
    super(source);
  }

  public void visit(Method m) {
    HashMap<NameExpression,ASTNode> subst=new HashMap<NameExpression, ASTNode>();
    ASTNode body=m.getBody();
    if (body==null){
      super.visit(m);
      return;
    }
    String name=m.getName();
    int N=m.getArity();
    String old_args[]=new String[N];
    String new_args[]=new String[N];
    Type  type_args[]=new Type[N];
    for(int i=0;i<N;i++){
      old_args[i]=m.getArgument(i);
      new_args[i]="__"+old_args[i];
      type_args[i]=m.getArgType(i);
    }
    FunctionType t=new FunctionType(type_args,m.getReturnType());
    t.setOrigin(m);
    Method.Kind kind=m.kind;
    Method res=new Method(kind,name,new_args,t);
    res.setOrigin(m.getOrigin());
    BlockStatement block=new BlockStatement();
    block.setOrigin(body);
    for(int i=0;i<N;i++){
      Type arg_type=t.getArgument(i);
      block.add_statement(create.field_decl(old_args[i],arg_type));
    }
    for(int i=0;i<N;i++){
      NameExpression old_name=create.local_name(old_args[i]);
      ASTNode new_name=create.local_name(new_args[i]);
      block.add_statement(create.assignment(old_name,new_name));
      subst.put(old_name,new_name);
    }
    Contract mc=m.getContract();
    Contract c=null;
    if (mc!=null){
      Substitution sigma=new Substitution(source(),subst);
      ASTNode pre=mc.pre_condition.apply(sigma);
      ASTNode post=mc.post_condition.apply(sigma);
      c=new Contract(mc.given,mc.yields,rewrite(mc.modifies),pre,post);
    }
    if (c!=null) res.setContract(c);
    { // this flattening could also be done by a generic pass.
      BlockStatement orig=(BlockStatement)body;
      for(int i=0;i<orig.getLength();i++){
        block.add_statement(orig.getStatement(i).apply(this));
      }
    }
    res.setBody(block);
    result=res;
  }

}
