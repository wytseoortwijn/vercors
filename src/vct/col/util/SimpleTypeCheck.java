package vct.col.util;

import java.util.Arrays;

import vct.col.ast.*;
import vct.col.ast.NameExpression.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.rewrite.MultiSubstitution;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

public class SimpleTypeCheck extends RecursiveVisitor<Type> {

  public void check(){
    for(ASTClass cl:source().classes()){
      cl.accept(this);
    }
  }

  public SimpleTypeCheck(ProgramUnit arg){
    super(arg);
  }

  public void visit(ConstantExpression e){
    Debug("constant %s",e);
    super.visit(e);
    if (e.getType()==null) Abort("untyped constant %s",e);
  }
  public void visit(ClassType t){
    super.visit(t);
    Debug("class type %s",t);
    String name[]=t.getNameFull();
    if (name.length==1){
      VariableInfo info=variables.lookup(name[0]);
      if (info!=null){
        Debug("kind is %s",info.kind);
        t.setType(t);
        return;
      } else {
        Debug("not a variable");
      }
    }
    ASTClass cl=source().find(t.getNameFull());
    if (cl==null) {
      Method m=null;
      if (name.length>1){
        m=source().find_predicate(t.getNameFull());
      }
      if (m==null){
        if (name.length >1){
          m=source().find_predicate(Arrays.copyOf(name, name.length-1));
        }
      }
      if (m==null &&
          !(name.length==3 && name[0].equals("java") && name[1].equals("lang") && name[2].equals("Object"))
          && !(name.length==1 && name[0].equals("Object"))){
        Fail("type error: class (or predicate) "+t.getFullName()+" not found");
      }
    }
    t.setType(t);
  }
 
  public void visit(MethodInvokation e){
    super.visit(e);
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
    ASTClass cl=source().find(object_type.getNameFull());
    if (cl==null) Fail("could not find class %s",object_type.getFullName());
    Method m=cl.find(e.method,object_type,type);
    while(m==null && cl.super_classes.length>0){
      cl=source().find(cl.super_classes[0].getNameFull());
      m=cl.find(e.method,object_type,type);
    }
    if (m==null) {
      String parts[]=e.method.split("_");
      if (parts.length==3 && parts[1].equals("get")){
        // TODO: check if parts[0] is a predicate.
        DeclarationStatement field=cl.find_field(parts[2]);
        if (field!=null) {
          Warning("assuming %s is implicit getter function",e.method);
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
      Fail("could not find method %s(%s) in class %s at %s",e.method,tmp,object_type.getFullName(),e.getOrigin());
    }
    switch(m.kind){
    case Constructor:
      e.setType((Type)e.object);
      break;
    default:
      {
        MultiSubstitution sigma=m.getSubstitution(object_type);
        e.setType(sigma.rewrite(m.getReturnType()));
        break;
      }
    }
    e.setDefinition(m);
    if (e.get_before()!=null) e.get_before().accept(this);
    if (e.get_after()!=null) e.get_after().accept(this);
  }
  
  public final void check_loc_val(Type loc_type,ASTNode val){
    if (loc_type==null) Abort("Location has no type.");
    Type val_type=val.getType();
    if (val_type==null) Abort("Value has no type has no type.");
    if (loc_type.toString().equals("<<label>>")) return;
    if (!(loc_type.equals(val_type)
        ||loc_type.supertypeof(source(), val_type)
        ||loc_type.isNumeric()&&val_type.isNumeric()
    )){
      Fail("Types of location (%s) and value (%s) do not match.",loc_type,val_type);
    }    
  }
  public void visit(AssignmentStatement s){
    ASTNode val=s.getExpression();
    val.accept(this);
    Type val_type=val.getType();
    if (val_type==null) Abort("Value has no type has no type.");
    if (val_type.toString().equals("<<label>>")) return;
    s.getLocation().accept(this);
    check_loc_val(s.getLocation().getType(),s.getExpression());
  }
  
  public void visit(DeclarationStatement s){
    super.visit(s);
    String name=s.getName();
    Type t=s.getType();
    ASTNode e=s.getInit();
    if (e!=null) {
      check_loc_val(t,e);
    }
  }
  
  public void visit(Method m){
    super.visit(m);
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
    super.visit(e);
    Debug("%s name %s",e.getKind(),e.getName());
    Kind kind = e.getKind();
    String name=e.getName();
    switch(kind){
      case Unresolved:{
        VariableInfo info=variables.lookup(name);
        if (info!=null) {
          Debug("unresolved %s name %s found during type check",info.kind,name);
          e.setKind(info.kind);
          kind=info.kind;
        }
      }
    }
    switch(kind){
      case Argument:
      case Local:
      case Field:{
        VariableInfo info=variables.lookup(name);
        if (info==null) {
          Abort("%s name %s is undefined",kind,name);
        }
        if (info.kind!=kind){
          if ((kind==NameExpression.Kind.Local && info.kind==NameExpression.Kind.Argument)
            ||(kind==NameExpression.Kind.Argument && info.kind==NameExpression.Kind.Local)){
            Debug("mismatch of kinds %s/%s for name %s",kind,info.kind,name);
          } else {
            Abort("mismatch of kinds %s/%s for name %s",kind,info.kind,name);
          }
        }
        DeclarationStatement decl=(DeclarationStatement)info.reference;
        e.setType(decl.getType());
        break;
      }
      case Method:
        if (e.getType()!=null){
          Abort("type of member %s has been set illegally",name);
        }
        break;
      case Reserved:
        if (name.equals("this")){
          ASTClass cl=current_class();
          if (cl==null){
            Fail("use of keyword this outside of class context");
          }
          e.setType(new ClassType(cl.getFullName()));
          break;
        } else if (name.equals("null")){
          e.setType(new ClassType("<<null>>"));
          break;
        } else if (name.equals("nil")){
          // TODO: put in correct type: seq<??> or seq<E>.
          e.setType(new ClassType("<<null>>"));
          break;
        } else if (name.equals("\\result")||name.equals("result")){
          Method m=current_method();
          if (m==null){
            Fail("Use of result keyword outside of a method context.");
          }
          e.setType(m.getReturnType());
          break;
        } else if (name.equals("super")){
          ASTClass cl=current_class();
          if (cl==null){
            Fail("use of keyword super outside of class context");
          }
          if (cl.super_classes.length==0) {
            Fail("class %s does not have a super type",cl.getName());
          }
          e.setType(cl.super_classes[0]);
          break;
        } else if (name.equals("*")) {
          e.setType(new PrimitiveType(Sort.Integer));
          break;
        }
        Abort("missing case for reserved name %s",name);
        break;
      case Unresolved:{
        Abort("unresolved name %s found during type check at %s",name,e.getOrigin());
        break;
      }
      case Label:
        e.setType(new ClassType("<<label>>"));
        break;
      default:
        Abort("missing case for kind %s",kind);
        break;
    }
  }
  public void visit(OperatorExpression e){
    super.visit(e);
    Debug("operator %s",e.getOperator());
    StandardOperator op=e.getOperator();
    switch(op){
    case Instance:
    case SubType:
    case SuperType:
    {
      e.setType(new PrimitiveType(Sort.Boolean));
      break;      
    }
    case Cast:
    {
      ASTNode t=e.getArg(0);
      if (t instanceof Type) {
        e.setType((Type)t);
      } else {
        Fail("cannot cast to non-type %s",t.getClass());
      }
      break;
    }
    case And:
    case Star:
    case Or:
    case Implies:
    case IFF:
    case Wand:
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
    case ArrayPerm:
      // TODO: check arguments
      e.setType(new PrimitiveType(Sort.Boolean));
      break;
    case Fork:
    case Join:
      // TODO: check arguments
      e.setType(new PrimitiveType(Sort.Void));
      break;
    case Assign:
    case AddAssign:
    case SubAssign:
    case MulAssign:
    case DivAssign:
    case RemAssign:
    case AndAssign:
    case XorAssign:
    case OrAssign:
    case ShlAssign:
    case ShrAssign:
    case SShrAssign:
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
      if (!t1.comparableWith(source(),t2)) {
        Fail("Types of left and right-hand side argument are uncomparable: %s/%s",t1,t2);
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
      if (!t.isNumeric()){
        Fail("Argument of %s must be a numeric type",op);
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
      if (!t1.isNumeric()){
        Fail("First argument of %s is %s rather than a numeric type",op,t1);
      }
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (!t2.isNumeric()){
        Fail("Second argument of %s is %s rather than a numeric type",op,t2);
      }
      e.setType(t1);
      break;
    }
    case BitAnd:
    case BitOr:
    case BitNot:
    case BitXor:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at %s",e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (t1.equalSize(t2)){
        e.setType(t1);
      } else {
        Fail("Types of left and right-hand side argument are different (%s/%s).",t1,t2);
      }
      break;
    }
    case RightShift:
    case LeftShift:
    case UnsignedRightShift:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of left argument unknown at %s",e.getOrigin());
      if (!t1.isIntegerType()){
        Fail("First argument of %s must be integer type, not %s",op,t1);
      }
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (!t2.isIntegerType()){
        Fail("Second argument of %s must be integer type, not %s",op,t2);
      }
      e.setType(t1);
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
      if (!t1.supertypeof(null, res)) Fail("type of first argument of %s is wrong at %s",op,e.getOrigin());
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of right argument unknown at %s",e.getOrigin());
      if (!t2.supertypeof(null, res)) Fail("type of second argument of %s is wrong at %s",op,e.getOrigin());
      if (t1.getClass()!=t2.getClass()) {
        Fail("Types of left and right-hand side argument are uncomparable at %s",e.getOrigin());
      }
      e.setType(new PrimitiveType(Sort.Boolean));      
      break;
    }
    case Access:
    case DirectProof:
    {
      e.setType(new PrimitiveType(Sort.Void));
      break;
    }
    case Fold:
    case Unfold:
    case Open:
    case Close:
    {
      ASTNode arg=e.getArg(0);
      if (!(arg instanceof MethodInvokation)){
        Fail("At %s: argument of [%s] must be a predicate invokation.",arg.getOrigin(),op);
      }
      MethodInvokation prop=(MethodInvokation)arg;
      if (prop.getDefinition().kind != Method.Kind.Predicate){
        Fail("At %s: argument of [%s] must be predicate and not %s",arg.getOrigin(),op,prop.getDefinition().kind);
      }
      e.setType(new PrimitiveType(Sort.Void));      
      break;
    }
    case Use:
    case QED:
    case Apply:
    case Assert:
    case HoarePredicate:
    case Assume:
    case Witness:
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
    case Subscript:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of base unknown at %s",e.getOrigin());
      if (!(t1 instanceof PrimitiveType)) Fail("base must be array or sequence type.");
      PrimitiveType t=(PrimitiveType)t1;
      switch(t.sort){
        case Sequence:
        case Array:
        {
          t1=(Type)t.getArg(0);
          break;
        }
        default: Fail("base must be array or sequence type.");
      }
      Type t2=e.getArg(1).getType();
      if (t2==null) Fail("type of subscript unknown at %s",e.getOrigin());
      if (!t2.isInteger()) {
        Fail("subcript has type %s rather than integer",t2);
      }
      e.setType(t1);
      break;
    }
    case Head:{
      Type t=e.getArg(0).getType();
      if (t==null) Fail("type of argument is unknown at %s",e.getOrigin());
      if (!t.isPrimitive(Sort.Sequence)) Fail("argument of head is not a sequence");
      e.setType((Type)t.getArg(0));      
      break;      
    }
    case Tail:{
      Type t=e.getArg(0).getType();
      if (t==null) Fail("type of argument is unknown at %s",e.getOrigin());
      if (!t.isPrimitive(Sort.Sequence)) Fail("argument of tail is not a sequence");
      e.setType(t);      
      break;      
    }
    case Size:
    {
      Type t=e.getArg(0).getType();
      if (t==null) Fail("type of argument is unknown at %s",e.getOrigin());
      if (!t.isPrimitive(Sort.Sequence)) Fail("argument of size is not a sequence");
      e.setType(new PrimitiveType(Sort.Integer));      
      break;
    }
    case Nil:
    {
      e.setType(new PrimitiveType(Sort.Sequence,e.getArg(0)));
      break;
    }
    case Append:
    {
      Type t1=e.getArg(0).getType();
      if (t1==null) Fail("type of first argument is unknown at %s",e.getOrigin());
      if (!t1.isPrimitive(Sort.Sequence)) Fail("argument of size is not a sequence");
      Type t2=e.getArg(0).getType();
      if (t2==null) Fail("type of second argument is unknown at %s",e.getOrigin());
      if (!t2.isPrimitive(Sort.Sequence)) Fail("argument of size is not a sequence");
      if (!t1.getArg(0).equals(t2.getArg(0))){
        Fail("different sequence types in append"); 
      }
      e.setType(t1);
      break;
    }
    case Build:
    {
      ASTNode args[]=e.getArguments();
      if (args.length==0 || !(args[0] instanceof Type)){
        Abort("Build without type argument");
      }
      Type t=(Type)args[0];
      e.setType(t);
      t=(Type)t.getArg(0);
      for(int i=1;i<args.length;i++){
        Type tt=args[i].getType();
        if (tt==null){
          Abort("untyped build argument %d",i);
        }
        if (t.equals(tt)) continue;
        if (t.supertypeof(source(), tt)) continue;
        Abort("cannot use %s to initialize %s",tt,t);
      }
      break;
    }
    default:
      Abort("missing case of operator %s",op);
      break;
    }
  }
  
  public void visit(Dereference e){
    super.visit(e);
    Type object_type=e.object.getType();
    if (object_type==null) Fail("type of object unknown at "+e.getOrigin());
    if (object_type instanceof PrimitiveType){
      if (e.field.equals("length")){
        e.setType(new PrimitiveType(Sort.Integer));
        return;
      }
      if (e.field.equals("item")){
        e.setType((Type)object_type.getArg(0));
        return;
      }
      Fail("%s is not a pseudo field.",e.field);
    }
    if (!(object_type instanceof ClassType)) {
      Fail("cannot select member %s of non-object type %s",e.field,object_type.getClass());
    }
    if (((ClassType)object_type).getFullName().equals("<<label>>")){
      //TODO: avoid this kludge to not typing labeled arguments
      e.setType(object_type);
    } else {
      Debug("resolving class "+((ClassType)object_type).getFullName()+" "+((ClassType)object_type).getNameFull().length);
      ASTClass cl=source().find(((ClassType)object_type).getNameFull());
      if (cl==null) Fail("could not find class %s",((ClassType)object_type).getFullName());
      Debug("looking in class "+cl.getName());
      DeclarationStatement decl=cl.find_field(e.field,true);
      if (decl==null) Fail("Field %s not found in class %s",e.field,((ClassType)object_type).getFullName());
      e.setType(decl.getType());
    }
  }

  public void visit(BlockStatement s){
    super.visit(s);
    // TODO: consider if type should be type of last statement. 
  }
  public void visit(IfStatement s){
    super.visit(s);
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
    super.visit(s);
    // TODO: check expression against method type.
  }
  public void visit(ASTClass c){
    super.visit(c);
    // TODO: type checks on class.
  }
  
  @Override
  public void visit(LoopStatement s) {
    super.visit(s);
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
  
  @Override
  public void visit(BindingExpression e){
    super.visit(e);
    //result=create.binder(e.binder, rewrite(e.getDeclarations()), rewrite(e.select), rewrite(e.main));
    Type t;
    if (e.select!=null){
      t=e.select.getType();
      if (t==null){
        Abort("Selection in binding expression without type.");
      }
      if (!t.isBoolean()){
        Fail("Selector in binding expression is not a boolean.");
      }
    }
    t=e.main.getType();
    if (t==null){
      Abort("Binding expression without type.");
    }
    
    e.setType(new PrimitiveType(Sort.Boolean));
  }

}
