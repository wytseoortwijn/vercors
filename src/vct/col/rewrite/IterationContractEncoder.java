package vct.col.rewrite;

import java.util.Hashtable;

import vct.col.ast.Contract;
import vct.col.ast.LoopStatement;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;
import vct.col.util.ASTUtils;
import vct.col.util.NameScanner;

public class IterationContractEncoder extends AbstractRewriter {

  public IterationContractEncoder(ProgramUnit arg) {
    super(arg);
  }

  public void visit(LoopStatement s){
    Contract c=s.getContract();
    if (c!=null && (c.pre_condition != c.default_true || c.post_condition != c.default_true)){
      Warning("processing iteration contract");
      Hashtable<String,Type> vars=new Hashtable<String,Type>();
      s.getBody().accept(new NameScanner(vars));
      c.accept(new NameScanner(vars));
      Hashtable<String,Type> iters=new Hashtable<String,Type>();
      s.getUpdateBlock().accept(new NameScanner(iters));
      for(String var:iters.keySet()){
        System.err.printf("iter %s : %s%n", var,iters.get(var));
      }
      String args="";
      String glue="";
      for(String var:vars.keySet()){
        System.err.printf("var %s : %s%n", var,vars.get(var));
        if (iters.containsKey(var)) continue;
        args+=glue+var;
        glue=",";
      }
      result=create.comment("// TODO: loop_main("+args+")");
    } else {
      super.visit(s);
    }
  }
}
