// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.boogie;

import hre.ast.TrackingOutput;
import vct.col.ast.*;

/**
 * This class contains a pretty printer for Boogie programs.
 * 
 * @author sccblom
 *
 */
public class BoogiePrinter extends AbstractBoogiePrinter {
  
  public BoogiePrinter(TrackingOutput out){
    super(BoogieSyntax.getBoogie(),out);
  }

  public void visit(Method m){
    FunctionType t=m.getType();
    int N=t.getArity();
    String result_type=t.getResult().toString();
    String name=m.getName();
    if (result_type.equals("pred")){
      throw new Error("Boogie does not allow predicates");
    }
    out.printf("procedure %s(",name);
    if (N>0) {
      out.printf("%s: ",m.getArgument(0));
      t.getArgument(0).accept(this);
      for(int i=1;i<N;i++){
        out.printf(",%s: ",m.getArgument(i));
        t.getArgument(i).accept(this);
      }
    }
    out.printf(") returns (");
    if (!result_type.equals("Void")){
        out.printf("__result: ");
        t.getResult().accept(this);
    }
    out.lnprintf(")");
    Contract contract=m.getContract();
    if (contract!=null){
      visit(contract);
      post_condition=contract.post_condition;
    }
//    if (all_fields!=null){
//      out.lnprintf("modifies %s;",all_fields);
//    }
    ASTNode body=m.getBody();
    body.accept(this);
    out.lnprintf("//end procedure %s",name);
    post_condition=null;
  }
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
      case Select:{
        ASTNode a0=e.getArg(0);
        ASTNode a1=e.getArg(1);
        if (a0 instanceof NameExpression && a1 instanceof NameExpression){
          String s0=((NameExpression)a0).toString();
          String s1=((NameExpression)a1).toString();
          if (s0.equals("model")){
            if (s1.equals("old")){
              out.print("old");
              return;
            }
            throw new Error("unknown keyword "+s1);
          }
        }
        // Let's hope this was a this. in case of Boogie!
        a1.accept(this);
        break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(NameExpression e){
    String s=e.toString();
    if (s.equals("\\result")){
      out.print("__result");
    } else if (s.equals("\\old")){
      out.print("old");
    } else {
      out.print(s);
    }
  }


  public void print(ASTClass cl){
    int N=cl.getStaticCount();
    int M=cl.getDynamicCount();
    if (N>0 && M>0) throw new Error("mixed static/dynamic "+N+"/"+M+" in boogie");
    if (N==1 && cl.getStatic(0) instanceof ASTClass){
      print((ASTClass)cl.getStatic(0));
    } else for(int i=0;i<N;i++){
      cl.getStatic(i).accept(this);
    }
    if (M==1 && cl.getDynamic(0) instanceof ASTClass){
      print((ASTClass)cl.getDynamic(0));
    } else for(int i=0;i<M;i++){
      cl.getDynamic(i).accept(this);
    }
  }
}
