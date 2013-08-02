// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.col.ast;

import hre.ast.MessageOrigin;

import java.util.*;

import vct.col.ast.Method.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.rewrite.MultiSubstitution;
import vct.col.rewrite.Substitution;
import vct.util.ClassName;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Warning;

/**
 * Method Declaration.
 * @author sccblom
 *
 */
public class Method extends ASTDeclaration {
  /** Enumeration of kinds of methods. */
  public static enum Kind{
    Constructor,
    Predicate,
    Pure,
    Plain
  };
 
  private final Type return_type;
  private final DeclarationStatement args [];
  private final boolean var_args;
  private Hashtable <String,Contract> spec=new Hashtable();
  private ASTNode body;
  public final Kind kind;
  
  public boolean usesVarArgs(){
    return var_args;
  }
  
  public Method(String name,Type return_type,Contract contract,DeclarationStatement args[],boolean varArgs,ASTNode body){
    this(Kind.Plain,name,return_type,contract,args,varArgs,body);
  }

  public Method(Kind kind, String name,String args[],boolean many,FunctionType t){
    super(name);
    this.return_type=t.getResult();
    this.args=new DeclarationStatement[args.length];
    this.var_args=many;
    for(int i=0;i<args.length;i++){
      this.args[i]=new DeclarationStatement(args[i],t.getArgument(i));
      this.args[i].setParent(this);
      this.args[i].setOrigin(new MessageOrigin("dummy origin for argument "+i));
    }
    this.kind=kind;
  }
  
  public Method(Kind kind, String name,Type return_type,Contract contract,DeclarationStatement args[],boolean varArgs,ASTNode body){
    super(name);
    this.return_type=return_type;
    this.args=Arrays.copyOf(args,args.length);
    this.var_args=varArgs;
    for(int i=0;i<args.length;i++){
      if (this.args[i].getParent()==null) this.args[i].setParent(this);
    }
    this.body=body;
    this.kind=kind;
    setContract(contract);
  }

  public Kind getKind(){ return kind; }
    
  public String getName(){ return name; }

  public int getArity(){ return args.length; }

  public String getArgument(int i){ return args[i].getName(); }

  public Type getArgType(int i){ return args[i].getType(); }

  public void setContract(Contract contract){
    setContract("this",contract);
  }
  
  public void setContract(String tag,Contract contract){
    if (contract==null) {
      spec.remove(tag);
      return;
    }
    spec.put(tag,contract);
    for(DeclarationStatement d:contract.given){
      d.setParent(this);
    }
    for(DeclarationStatement d:contract.yields){
      d.setParent(this);
    }
  }
  
  public Contract getContract(String tag){
    return spec.get(tag);
  }
  
  public Contract getContract(){
    return spec.get("this");
  }
  
  public void setBody(ASTNode body){
    this.body=body;
  }
  public ASTNode getBody(){
    return body;
  }
  public DeclarationStatement[] getArgs() {
    return args;
  }
  public Type getReturnType() {
    return return_type;
  }

  public Type[] getArgType() {
    Type res[]=new Type[args.length];
    for(int i=0;i<args.length;i++){
      res[i]=args[i].getType();
    }
    return res;
  }

  public MultiSubstitution getSubstitution(ClassType object_type) {
    Map<String,Type> map=new HashMap<String,Type>();
    MultiSubstitution sigma=new MultiSubstitution(null,map);
    if (object_type==null){
      Debug("missing object type");
      return sigma;      
    }
    if (object_type.args==null){
      Debug("object type has no arguments");
      return sigma;
    }
    if (getParent()==null){
      Debug("missing parent");
      return sigma;
    }
    Contract c=((ASTClass)getParent()).getContract();
    if (c==null) {
      Debug("missing contract");
      return sigma;
    }
    Debug("building map...");
    for(int i=0;i<c.given.length&&i<object_type.args.length;i++){
      if (c.given[i].getType().isPrimitive(Sort.Class)){
        Debug("%s = %s",c.given[i].getName(),object_type.args[i]);
        map.put(c.given[i].getName(),(Type)object_type.args[i]);
      } else {
        Debug("skipping %s",c.given[i].getName());
      }
    }
    return sigma;
  }

  @Override
  public ClassName getDeclName() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected <T> void accept_simple(ASTVisitor<T> visitor) {
    visitor.visit(this);
  }

}


