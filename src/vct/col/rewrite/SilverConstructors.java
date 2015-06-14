package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Hashtable;

import vct.col.ast.*;

public class SilverConstructors extends AbstractRewriter {

  public SilverConstructors(ProgramUnit source) {
    super(source);
  }

  private boolean in_cons;
  
  private static final String return_name="created_object";
  @Override
  public void visit(Method m){
    if (m.kind==Method.Kind.Constructor){
      in_cons=true;
      Type returns=create.class_type("Ref");
      Contract contract=rewrite(m.getContract());
      String name="create_"+m.name;
      DeclarationStatement args[]=rewrite(m.getArgs());
      BlockStatement body=create.block();
      ArrayList<NameExpression> fields=new ArrayList();
      for(DeclarationStatement decl:((ASTClass)m.getParent()).dynamicFields()){
        fields.add(create.unresolved_name(decl.name));
      }
      body.add(create.field_decl(return_name,returns));
      body.add(create.assignment(create.unresolved_name(return_name),
          create.expression(StandardOperator.NewSilver,fields.toArray(new ASTNode[0]))));
      body.add(rewrite(m.getBody()));        
      body.add(create.return_statement(create.unresolved_name(return_name)));
      result=create.method_kind(Method.Kind.Plain, returns, contract, name, args, body);
      result.setStatic(true);
      in_cons=false;
    } else {
      super.visit(m);
    }
  }
  
  @Override
  public void visit(NameExpression n){
    if (in_cons && n.isReserved(ASTReserved.This)){
      if (in_ensures){
        result=create.reserved_name(ASTReserved.Result);
      } else {
        result=create.local_name(return_name);
      }
    } else {
      super.visit(n);
    }
  }
  
  @Override
  public void visit(MethodInvokation s){
    if (s.method.equals("Ref")){
      result=create.invokation(null,null,"create_Ref",rewrite(s.getArgs()));
    } else {
      super.visit(s);
    }
  }
  
  @Override
  public void visit(ASTSpecial e){
    switch(e.kind){
      case Fork:
      case Join:
      {
        ASTClass cl=source().find(((ClassType)e.args[0].getType()).getNameFull());
        Method run=cl.find("run",(ClassType) e.args[0].getType(), new Type[0] , false);
        Contract c=run.getContract();
        Hashtable<NameExpression, ASTNode> map=new Hashtable<NameExpression, ASTNode>();
        Substitution sigma=new Substitution(source(),map);
        map.put(create.reserved_name(ASTReserved.This),rewrite(e.args[0]));
        if (e.kind==ASTSpecial.Kind.Fork){
          result=create.special(ASTSpecial.Kind.Exhale,sigma.rewrite(c.pre_condition));
        } else {
          result=create.special(ASTSpecial.Kind.Inhale,sigma.rewrite(c.post_condition));
        }
        break;
      }
      default:
        super.visit(e);
        break;
    }
  }
}
