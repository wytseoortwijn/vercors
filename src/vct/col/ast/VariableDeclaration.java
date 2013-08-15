package vct.col.ast;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import vct.col.rewrite.AbstractRewriter;
import vct.col.rewrite.MultiSubstitution;
import vct.util.ClassName;

public class VariableDeclaration extends ASTNode {

  public final Type basetype;
  private ArrayList<DeclarationStatement> vars=new ArrayList<DeclarationStatement>();
  
  public VariableDeclaration(Type basetype){
    this.basetype=basetype;
  }
  
  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

  public void add(DeclarationStatement decl){
    vars.add(decl);
  }
  
  public Iterable<DeclarationStatement> get(){
    return vars;
  }

  public DeclarationStatement[] flatten() {
    ArrayList<DeclarationStatement> list=new ArrayList();
    Map<String,Type> map=new HashMap();
    AbstractRewriter rw=new MultiSubstitution(null,map);
    map.put("basetype",basetype);
    rw.create.setOrigin(getOrigin());
    for(DeclarationStatement d:vars){
      DeclarationStatement tmp=rw.create.field_decl(d.getName(),rw.rewrite(d.getType()), rw.copy_rw.rewrite(d.getInit()));
      if (isValidFlag(ASTFlags.STATIC)){
        tmp.setStatic(isStatic());
      }
      list.add(tmp);
    }
    return list.toArray(new DeclarationStatement[0]);
  }
}
