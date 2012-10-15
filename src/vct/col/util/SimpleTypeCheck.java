package vct.col.util;

import vct.col.ast.*;
import vct.col.ast.NameExpression.Kind;
import vct.col.ast.PrimitiveType.Sort;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

public class SimpleTypeCheck extends AbstractVisitor<Type> {

  public void check(ASTNode node){
    ASTVisitor checker=new PostVisit(this);
    node.accept(checker);
  }
  
  private ASTClass namespace;
  
  public SimpleTypeCheck(ASTClass namespace){
    this.namespace=namespace;
  }
  public void visit(ConstantExpression e){
    if (e.getType()==null) Abort("untyped constant %s",e);
  }
  public void visit(ClassType t){
    ASTClass cl=namespace.find(t.getNameFull());
    if (cl==null) Fail("type error: class "+t.getFullName()+" not found"); 
    t.setType(t);
  }
 
  public void visit(MethodInvokation e){
    if (e.object==null) Abort("unresolved method invokation at "+e.getOrigin());
    if (e.object.getType()==null) Abort("object has no type at %s",e.object.getOrigin());
    if (!(e.object.getType() instanceof ClassType)) Abort("invokation on non-class");
    ClassType object_type=(ClassType)e.object.getType();
    int N=e.getArity();
    for(int i=0;i<N;i++){
      if (e.getArg(i).labels()>0) {
        for(int j=i+1;j<N;j++){
          if (e.getArg(j).labels()==0) Fail("positional argument following named argument");
        }
        N=i;
        break;
      }
    }
    Type type[]=new Type[N];
    for(int i=0;i<N;i++){
      type[i]=e.getArg(i).getType();
      if (type[i]==null) Abort("argument %d has no type.",i);
    }
    ASTClass cl=namespace.find(object_type.getNameFull());
    if (cl==null) Fail("could not find class %s",object_type.getFullName());
    Method m=cl.find(e.method.getName(),type);
    if (m==null) {
      String parts[]=e.method.getName().split("_");
      if (parts.length==3 && parts[1].equals("get")){
        // TODO: check if parts[0] is a predicate.
        DeclarationStatement field=cl.find_field(parts[2]);
        if (field!=null) {
          Warning("assuming %s is implicit getter function",e.method.getName());
          e.setType(field.getType());
        }
        return;
      }
      String tmp="";
      if (N>0){
        tmp=type[0].toString();
        for(int i=1;i<N;i++){
          tmp=tmp+","+type[i].toString();
        }
      }
      Fail("could not find method %s(%s) in class %s at %s",e.method.getName(),tmp,object_type.getFullName(),e.getOrigin());
    }
    switch(m.kind){
    case Constructor:
      e.setType((Type)e.object);
      break;
    default:
      e.setType(m.getReturnType());
      break;
    }
    e.setDefinition(m);
  }
  
  public void visit(AssignmentStatement s){
    ASTNode loc=s.getLocation();
    ASTNode val=s.getExpression();
    Type loc_type=loc.getType();
    if (loc_type==null) Abort("Location has no type.");
    Type val_type=val.getType();
    if (val_type==null) Abort("Value has no type has no type.");
    if (!(loc_type.equals(val_type) || loc_type.supertypeof(val_type))) {
      Abort("Types of location (%s) and value (%s) do not match at %s.",loc_type,val_type,s.getOrigin());
    }
  }
  
  public void visit(DeclarationStatement s){
    String name=s.getName();
    Type t=s.getType();
    ASTNode e=s.getInit();
    if (e!=null && !t.equals(e.getType())) {
      Abort("type of %s (%s) does not match its initialization (%s)",name,t,e.getType());
    }
  }
  
  public void visit(Method m){
    String name=m.getName();
    ASTNode body=m.getBody();
    Contract contract=m.getContract();
    if (contract!=null){
      if (contract.pre_condition.getType()==null) Abort("untyped pre condition"); // TODO check boolean.
      if (contract.post_condition.getType()==null) Abort("untyped post condition"); // TODO check boolean.
    }
    if (body!=null && (body instanceof BlockStatement)) {
      //TODO: determine type of block
      return;
    }
    if (body!=null) {
      Type bt=body.getType();
      if (bt==null) Abort("untyped body of %s has class %s",name,body.getClass());
      if (!bt.equals(m.getReturnType()))
      Abort("body of %s does not match result type",name);
    }
  }
  public void visit(NameExpression e){
    Kind kind = e.getKind();
    String name=e.getName();
    switch(kind){
    case Argument:
    case Local:
        if (e.getType()==null) {
          Abort("type of local variable %s has not been set",name);
        }
        break;
      case Field:
      case Method:
        if (e.getType()!=null){
          Abort("type of member %s has been set illegally",name);
        }
        break;
      case Reserved:
        if (name.equals("this")){
          if (e.getType()==null) Abort("type of this has not been set");
          break;
        } else if (name.equals("null")){
          e.setType(new ClassType("<<null>>"));
          break;
        } else if (name.equals("\\result")){
          if (e.getType()==null) Abort("type of result has not been set");
          break;
        }
        Abort("missing case for reserved name %s",name);
        break;
      case Unresolved:
        Abort("unresolved name %s found during type check at %s",name,e.getOrigin());
        break;
      case Label:
        e.setType(new ClassType("<<label>>"));
        break;
      default:
        Abort("missing case for kind %s",kind);
        break;
    }
  }
  public void visit(OperatorExpression e){
    StandardOperator op=e.getOperator();
    switch(op){
    case And:
    case Star:
    case Or:
    case Implies:
    case IFF:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null || !t1.isBoolean()) Fail("type of left argument unknown at "+e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (!t2.isBoolean()) Fail("type of right argument is %s rather than boolean at %s",t2,e.getOrigin());
      e.setType(new PrimitiveType(Sort.Boolean));
      break;
    }
    case PointsTo:
    case Perm:
    case Value:
      // TODO: check arguments
      e.setType(new PrimitiveType(Sort.Boolean));
      break;
    case Fork:
    case Join:
      // TODO: check arguments
      e.setType(new PrimitiveType(Sort.Void));
      break;
    case Select:
    {
      NameExpression field=(NameExpression)e.getArg(1);
      Type object_type=e.getArg(0).getType();
      if (object_type==null) Fail("type of object unknown at "+e.getOrigin());
      if (!(object_type instanceof ClassType)) Abort("cannot select members of non-object type.");
      if (((ClassType)object_type).getFullName().equals("<<label>>")){
        //TODO: avoid this kludge to not typing labeled arguments
        e.setType(object_type);
        break;
      }
      Debug("resolving class "+((ClassType)object_type).getFullName()+" "+((ClassType)object_type).getNameFull().length);
      ASTClass cl=namespace.find(((ClassType)object_type).getNameFull());
      if (cl==null) Fail("could not find class %s",((ClassType)object_type).getFullName());
      Debug("looking in class "+cl.getName());
      DeclarationStatement decl=cl.find_field(field.getName());
      if (decl==null) Fail("Field %s not found in class %s",field.getName(),((ClassType)object_type).getFullName());
      e.setType(decl.getType());
      break;
    }
    case Assign:
    {
      if (e.getArg(0) instanceof NameExpression){
        NameExpression name=(NameExpression)e.getArg(0);
        if (name.getKind()==NameExpression.Kind.Label) break;
      }
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at "+e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at "+e.getOrigin());
      if (t1.getClass()!=t2.getClass()) {
        Fail("Types of left and right-hand side arguments in assignment are incomparable at "+e.getOrigin());
      }
      e.setType(t1);
      break;
    }    
    case EQ:
    case NEQ:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at "+e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at "+e.getOrigin());
      if (t1.getClass()!=t2.getClass()) {
        Fail("Types of left and right-hand side argument are uncomparable at "+e.getOrigin());
      }
      e.setType(new PrimitiveType(Sort.Boolean));
      break;
    }
    case ITE:
    {
      Type t=e.getArg(0).getType();
      if (!t.isBoolean()){
        Abort("First argument of if-the-else must be boolean at "+e.getOrigin());
      }
      Type t1=e.getArg(1).getType();
      if (t1==null) Fail("type of left argument unknown at "+e.getOrigin());
      Type t2=e.getArg(2).getType();
      if (t2==null) Fail("type of right argument unknown at "+e.getOrigin());
      if (t1.getClass()!=t2.getClass()) {
        Fail("Types of left and right-hand side argument are uncomparable at "+e.getOrigin());
      }
      e.setType(t1);      
      break;
    }
    case Not:
    {
      Type t=e.getArg(0).getType();
      if (!t.isBoolean()){
        Abort("Argument of negation must be boolean at "+e.getOrigin());
      }
      e.setType(t);
      break;
    }
    case PreIncr:
    case PreDecr:
    case PostIncr:
    case PostDecr:
    case UMinus:
    case UPlus:
    {
      Type t=e.getArg(0).getType();
      if (!t.isInteger()){
        Fail("Argument of %s must be boolean at %s",op,e.getOrigin());
      }
      e.setType(t);
      break;
    }
    case Plus:
    case Minus:
    case Mult:
    case Div:
    case Mod:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at %s",e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (t1.supertypeof(t2)){
        e.setType(t1);
      } else if (t2.supertypeof(t1)){
        e.setType(t1);
      } else {
        Fail("Types of left and right-hand side argument are uncomparable at %s",e.getOrigin());
      }
      break;
    }
    case GTE:
    case LTE:
    case LT:
    case GT:
    {
      Type res=new PrimitiveType(Sort.Byte);
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at %s",e.getOrigin());
      if (!t1.supertypeof(res)) Fail("type of first argument of %s is wrong at %s",op,e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (!t2.supertypeof(res)) Fail("type of second argument of %s is wrong at %s",op,e.getOrigin());
      if (t1.getClass()!=t2.getClass()) {
        Fail("Types of left and right-hand side argument are uncomparable at %s",e.getOrigin());
      }
      e.setType(new PrimitiveType(Sort.Boolean));      
      break;
    }
    case DirectProof:{
      e.setType(new PrimitiveType(Sort.Void));
      break;
    }
    case Assert:
    case Fold:
    case HoarePredicate:
    case Unfold:
    case Assume:
    {
      Type t=e.getArg(0).getType();
      if (t==null) Fail("type of argument is unknown at %s",e.getOrigin());
      if (!t.isBoolean()){
        Fail("Argument of %s must be boolean at %s",op,e.getOrigin());
      }
      e.setType(new PrimitiveType(Sort.Void));      
      break;
    }
    case Old:
    {
      Type t=e.getArg(0).getType();
      if (t==null) Fail("type of argument is unknown at %s",e.getOrigin());
      e.setType(t);      
      break;
    }
    case Continue:
    {
      Type t=e.getArg(0).getType();
      if (t!=null) Fail("argument of %s should not have type %s",op,t);
      e.setType(new PrimitiveType(Sort.Void));  
      break;
    }
    case New:
    {
      ASTNode t=e.getArg(0);
      if (!(t instanceof ClassType)) Fail("argument to new is not a class type");
      e.setType((Type)t);
      break;
    }
    default:
      Abort("missing case of operator %s",op);
      break;
    }
  }
  public void visit(BlockStatement s){
    // TODO: consider if type should be type of last statement. 
  }
  public void visit(IfStatement s){
    int N=s.getCount();
    for(int i=0;i<N;i++){
      Type t=s.getGuard(i).getType();
      if (t==null || !(t instanceof PrimitiveType) || (((PrimitiveType)t).sort!=Sort.Boolean)){
        Fail("Guard %d of if statement is not a boolean at %s",i,s.getOrigin());
      }
    }
    // TODO: consider if this can be an if expression.... 
  }
  public void visit(ReturnStatement s){
    // TODO: check expression against method type.
  }
  public void visit(ASTClass c){
    // TODO: type checks on class.
  }
  
  public void visit(LoopStatement s) {
    for(ASTNode inv:s.getInvariants()){
      Type t=inv.getType();
      if (t==null || !(t instanceof PrimitiveType) || (((PrimitiveType)t).sort!=Sort.Boolean)){
        Abort("loop invariant is not a boolean");
      }
    }
    ASTNode tmp;
    tmp=s.getEntryGuard();
    if (tmp!=null) {
      Type t=tmp.getType();
      if (t==null || !(t instanceof PrimitiveType) || (((PrimitiveType)t).sort!=Sort.Boolean)){
        Abort("loop entry guard is not a boolean");
      }
    }
    tmp=s.getExitGuard();
    if (tmp!=null) {
      Type t=tmp.getType();
      if (t==null || !(t instanceof PrimitiveType) || (((PrimitiveType)t).sort!=Sort.Boolean)){
        Abort("loop exit guard is not a boolean");
      }      
    }
  }

}
