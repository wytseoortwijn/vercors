package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.ASTUtils;
import static hre.System.*;

/**
 * Explicit permission encoding.
 * 
 * @author Stefan Blom
 *
 */
public class ExplicitPermissionEncoding extends AbstractRewriter {
  public ExplicitPermissionEncoding(ProgramUnit source) {
    super(source);
  }

  public AbstractRewriter copy_rw=new AbstractRewriter(source()){
    public void visit(NameExpression name){
      if (name.getKind()==NameExpression.Kind.Label){
        result=new NameExpression(name.getName());
        result.setOrigin(create.getOrigin());
      } else {
        super.visit(name);
      }
    }
  };
  
  public void visit(DeclarationStatement s) {
    Type t=s.getType();
    ASTNode tmp;
    if (t instanceof ClassType) {
      ClassType ct=(ClassType)t;
      String name[]=ct.getNameFull();
      switch(name.length){
      case 2 : tmp=create.class_type(name[0]+"_"+name[1]); break;
      default : tmp=create.class_type(name); break;
      }
    } else {
      tmp=t.apply(copy_rw);
    }
    t=(Type)tmp;
    String name=s.getName();
    ASTNode init=s.getInit();
    if (init!=null) init=init.apply(this);
    DeclarationStatement res=new DeclarationStatement(name,t,init);
    res.setOrigin(s.getOrigin());
    result=res; return ;
  }

  public void visit(Method m){
    final String class_name=((ASTClass)m.getParent()).getName();
    if (m.kind==Method.Kind.Predicate){
      ASTClass pred_class=(ASTClass)(new PredicateClassGenerator(source(),currentClass)).rewrite((ASTNode)m);
      Contract c=((ASTClass)m.getParent()).getContract();
      if (c!=null){
        pred_class.setContract(copy_rw.rewrite(c));
      }
      target().addClass(pred_class.getFullName(),pred_class);
      result=null;
    } else {
      current_method=m;
      Contract c=m.getContract();
      if (c==null) c=ContractBuilder.emptyContract();
      final ContractBuilder cb=new ContractBuilder();
      cb.given(rewrite(c.given));
      final ArrayList<DeclarationStatement> args=new ArrayList<DeclarationStatement>();
      for(DeclarationStatement arg:m.getArgs()){
        args.add(rewrite(arg));
      }
      ClauseEncoding clause_rw;
      clause_rw=new ClauseEncoding(source()){
        public void visit(MethodInvokation i){
          if (i.labels()==1){
            NameExpression lbl=i.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(i.object.getType()+"_"+i.method);
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(i);
            //decl.setFlag(ASTFlags.GHOST, true);
            //args.add(decl);
            cb.given(decl);
          }
          super.visit(i);
        }        
      };
      cb.requires(c.pre_condition.apply(clause_rw));
      clause_rw=new ClauseEncoding(source()){
        public void visit(MethodInvokation i){
          if (i.labels()==1){
            NameExpression lbl=i.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(i.object.getType()+"_"+i.method);
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(i);
            //decl.setFlag(ASTFlags.GHOST, true);
            //decl.setFlag(ASTFlags.OUT_ARG, true);
            //args.add(decl);
            cb.yields(decl);
          }
          super.visit(i);
        }
      };
      cb.ensures(c.post_condition.apply(clause_rw));
      ASTNode body=rewrite(m.getBody());
      Method res=new Method(m.kind,m.getName(),m.getReturnType(), cb.getContract(), args.toArray(new DeclarationStatement[0]), body);
      res.setOrigin(m);
      result=res;
      current_method=null;
    }
  }
  
  public void visit(final LoopStatement s){
    final BlockStatement block=create.block();
    AbstractRewriter clause_rw=new ClauseEncoding(source()){
      public void visit(MethodInvokation i){
        if (i.labels()==1){
          NameExpression lbl=i.getLabel(0);
          String label_name=lbl.getName();
          String pred_name=i.method;
          String class_name=((ASTClass)i.getDefinition().getParent()).getName();
          Type t=create.class_type(class_name+"_"+pred_name);
          DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t);
          decl.setOrigin(s);
          decl.setFlag(ASTFlags.GHOST, true);
          block.add_statement(decl);
        }
        super.visit(i);
      }        
    };
    LoopStatement res=new LoopStatement();
    ASTNode tmp;
    tmp=s.getInitBlock();
    if (tmp!=null) res.setInitBlock(tmp.apply(this));
    tmp=s.getUpdateBlock();
    if (tmp!=null) res.setUpdateBlock(tmp.apply(this));
    tmp=s.getEntryGuard();
    if (tmp!=null) res.setEntryGuard(tmp.apply(this));
    tmp=s.getExitGuard();
    if (tmp!=null) res.setExitGuard(tmp.apply(this));
    for(ASTNode inv:s.getInvariants()){
      res.appendInvariant(inv.apply(clause_rw));
    }
    tmp=s.getBody();
    res.setBody(tmp.apply(this));
    res.setOrigin(s.getOrigin());
    res.set_before(copy_rw.rewrite(s.get_before()));
    res.set_after(rewrite(s.get_after()));
    block.add_statement(res);
    result=block;
  }
  
  private Method current_method;
  
  public void visit(NameExpression name){
    if (name.getKind()==NameExpression.Kind.Label){
      result=new NameExpression(name.getName());
      result.setOrigin(create.getOrigin());
//      if (current_method!=null && current_method.getContract().hasLabel(name.getName())){
//        result=new NameExpression(name.getName());
//        result.setOrigin(create.getOrigin());
//        return;
 //     }
      return;
    }
    super.visit(name);
  }
  
  public void visit(OperatorExpression e){
    switch (e.getOperator()){
    case Unfold:{
      ASTNode arg1=e.getArg(0);
      if (arg1.labels()==1){
        for(NameExpression lbl:arg1.getLabels()){
          result=create.expression(e.getOperator(),
              create.invokation(create.local_name(lbl.getName()), false, "valid")
              );
          return;
        }
      } else {
        super.visit(e);
      }
      break;
    }
    case Fold:{
      ASTNode arg1=e.getArg(0);
      if (arg1.labels()==1){
        NameExpression lbl=arg1.getLabel(0);
        MethodInvokation pred=(MethodInvokation)arg1;
        String pred_name=pred.method;
        String class_name=((ASTClass)pred.getDefinition().getParent()).getName();
        Type t=create.class_type(class_name+"_"+pred_name);
        ArrayList<ASTNode> args=new ArrayList();
        args.add(pred.object.apply(copy_rw));
        for (ASTNode arg:pred.getArgs()){
          args.add(arg.apply(copy_rw));
        }
        result=create.assignment(create.local_name(lbl.getName()),
                create.new_object(t,args.toArray(new ASTNode[0])));
        result.setGhost(true);
          //    create.new_object(type, args));
          //result=create.expression(e.getOperator(),
          //    create.invokation(create.local_name(lbl.getName()), false, ("valid"))
          //    );
        return;
      } else {
        super.visit(e);
      }
      break;
    }
    default:
      super.visit(e);
      break;
    }
  }
}

class ClauseEncoding extends AbstractRewriter {

  public ClauseEncoding(ProgramUnit source) {
    super(source);
  }

  public AbstractRewriter copy_rw=new AbstractRewriter(source()){
    public void visit(NameExpression name){
      if (name.getKind()==NameExpression.Kind.Label){
        result=new NameExpression(name.getName());
        result.setOrigin(create.getOrigin());
      } else {
        super.visit(name);
      }
    }
  };

  public void visit(MethodInvokation i) {
    if (i.getDefinition()==null){
      Warning("Ignoring missing definition of %s",i.method);
      result=copy_rw.rewrite(i);
    } else if (i.getDefinition().getKind()!=Method.Kind.Predicate){
      result=copy_rw.rewrite(i);
    } else {
      if (i.labels()==0){
        Abort("At %s: every predicate invokation must be labeled.",i.getOrigin());
      }
      NameExpression lbl=i.getLabel(0);
      ASTNode body=create.expression(StandardOperator.NEQ,create.unresolved_name(lbl.getName()),create.reserved_name("null"));
      body=create.expression(StandardOperator.Star,body,
          create.invokation(create.unresolved_name(lbl.getName()), false, ("valid")));
      body=create.expression(StandardOperator.Star,body,
          create.invokation(
              create.unresolved_name(lbl.getName()),
              false,
              ("check"),
              rewrite(i.object,i.getArgs())
          ));
      
      result=body;
      auto_labels=false;
    }
  }
}

class PredicateClassGenerator extends AbstractRewriter {
  public AbstractRewriter copy_rw=new AbstractRewriter(source()){};
  private String class_name;
  private String pred_name;
  private ASTClass pred_class;
  private boolean in_use=false;
  private int condition_level=0;
  private Method pred_decl;
  private ASTClass master;
  private HashSet<String> protected_fields=new HashSet<String>();
  
  public PredicateClassGenerator(ProgramUnit source,ASTClass master){
    super(source);
    this.master=master;
  }
  
  public void visit(Method m){
    if (in_use) {
      Abort("Predicate class generator already in use.");
    }
    in_use=true;
    pred_decl=m;
    
    class_name=((ASTClass)m.getParent()).getName();
    pred_name=m.getName();
    String pred_class_name=class_name+"_"+pred_name;
    pred_class=create.ast_class(pred_class_name,ClassKind.Plain,null,null);
    String tmp[]=((ASTClass)m.getParent()).getFullName();
    Type class_type=create.class_type(tmp);
    tmp[tmp.length-1]=pred_class_name;
    Type pred_type=create.class_type(tmp);
    
    // Start with ref field:
    pred_class.add_dynamic(create.field_decl("ref",class_type));
    DeclarationStatement args[]=m.getArgs();
    ASTNode cons_req=create.expression(StandardOperator.NEQ,create.unresolved_name("ref"),create.reserved_name("null"));
    // Note that permission for fields will be added later.
    
    // Add arguments as fields:
    for (int i=0;i<args.length;i++){
      pred_class.add_dynamic(args[i].apply(copy_rw));
      if (args[i].getType().isPrimitive(PrimitiveType.Sort.Fraction)){
        cons_req=create.expression(StandardOperator.Star,cons_req,
            create.expression(StandardOperator.LT,create.constant(0),create.unresolved_name(args[i].getName()))
            );
        cons_req=create.expression(StandardOperator.Star,cons_req,
            create.expression(StandardOperator.LTE,create.unresolved_name(args[i].getName()),create.constant(100))
            );
      }
    }
    
    // Rewrite the body, which will cause fields to be created.
    ASTNode valid_body;
    if (m.getBody()==null){
      pred_class.add_dynamic(create.predicate("abstract_valid", null , new DeclarationStatement[0] ));
      valid_body=create.invokation(null,false, ("abstract_valid"), new DeclarationStatement[0]);
    } else {
      valid_body=rewrite(m.getBody());
    }
    valid_body=create.expression(StandardOperator.Star,cons_req,valid_body);
    // Add permissions to read/write all fields:
    for(DeclarationStatement field:pred_class.dynamicFields()){
      valid_body=create.expression(StandardOperator.Star,
          create.expression(StandardOperator.Perm,create.field_name(field.getName()),create.constant(100))
          ,valid_body);
     
    }
    // Add valid predicate;
    pred_class.add_dynamic(create.predicate("valid", valid_body , new DeclarationStatement[0] ));
    
    // Prepare check function;
    ContractBuilder cb=new ContractBuilder();
    cb.requires(create.invokation(null,false, ("valid"), new DeclarationStatement[0]));
    ASTNode check_body=create.expression(StandardOperator.EQ,create.field_name("ref"),create.local_name("object"));
    for (DeclarationStatement decl:m.getArgs()){
      ASTNode field=create.dereference(create.reserved_name("this"),decl.getName());
      check_body=create.expression(StandardOperator.And,check_body,
          create.expression(StandardOperator.EQ,field,create.local_name(decl.getName())));
    }
    DeclarationStatement check_decls[]=rewrite(create.field_decl("object",class_type),m.getArgs());
    // Add check function;
    pred_class.add_dynamic(create.function_decl(
        create.primitive_type(Sort.Boolean),
        cb.getContract(),
        "check",
        check_decls,
        check_body
    ));
    
    // Prepare constructor
    final BlockStatement cons_body=create.block();
    final ArrayList<DeclarationStatement> cons_decls=new ArrayList();
    cb=new ContractBuilder();
    cb.ensures(create.invokation(null,false, ("valid"), new ASTNode[0]));
    int N=m.getArity();
    ASTNode check_args[]=new ASTNode[N+1];
    {
      cons_decls.add(create.field_decl("ref",class_type));
      ASTNode field=create.dereference(create.reserved_name("this"),"ref");
      check_args[0]=create.local_name("ref");
      cons_body.add_statement(create.assignment(field, check_args[0]));
    }
    for(int i=0;i<N;i++){
      cons_decls.add(create.field_decl(m.getArgument(i),m.getArgType(i)));
      ASTNode field=create.dereference(create.reserved_name("this"),m.getArgument(i));
      check_args[i+1]=create.local_name(m.getArgument(i));
      cons_body.add_statement(create.assignment(field, check_args[i+1]));
    }
    cb.requires(cons_req);
    if (m.getBody()!=null) {
      cb.requires(m.getBody().apply(new ClauseEncoding(source()){
        public void visit(NameExpression e){
          if (e.getKind()==NameExpression.Kind.Reserved && e.getName()=="this"){
            result=create.local_name("ref");
          } else {
            super.visit(e);
          }
        }
        public void visit(MethodInvokation i){
          super.visit(i);
          if (i.labels()==1){
            String name=i.getLabel(0).getName();
            ClassType type=(ClassType)i.object.getType();
            String type_name[]=type.getNameFull();
            type_name[type_name.length-1]+="_"+i.method;
            type=create.class_type(type_name);
            DeclarationStatement decl=create.field_decl(name,type);
            decl.setGhost(true);
            cons_decls.add(decl);
            ASTNode field=create.dereference(create.reserved_name("this"),name);
            cons_body.add_statement(create.assignment(field, create.local_name(name)));
          }
        }
      }));
    } else {
      cons_body.add_statement(create.expression(StandardOperator.Assume,
          create.invokation(create.reserved_name("this"),false, ("abstract_valid"), new ASTNode[0])));
    }
    cb.ensures(create.invokation(null,false, ("check"), check_args));
    cons_body.add_statement(create.expression(StandardOperator.Fold,
        create.invokation(create.reserved_name("this"),false, ("valid"), new ASTNode[0])));
    for(String field_name:protected_fields){
      ASTNode getter_args[]=new ASTNode[N+1];
      for(int i=0;i<N;i++){
        getter_args[i]=create.local_name(pred_decl.getArgument(i));
        getter_args[i].addLabel(create.label(pred_decl.getArgument(i)));
      }
      getter_args[N]=create.reserved_name("this");
      getter_args[N].addLabel(create.label("req"));
      cb.ensures(create.expression(StandardOperator.EQ,
          create.invokation(
              create.local_name("ref"),
              false ,
              (pred_name+"_get_"+field_name),
              getter_args
          ),
          create.expression(StandardOperator.Old,
              create.dereference(create.local_name("ref"),field_name)
          )
      ));
    }
    // Add constructor;
    pred_class.add_dynamic(create.method_kind(Method.Kind.Constructor,
        create.primitive_type(Sort.Void),
        cb.getContract(),
        pred_class_name,
        cons_decls.toArray(new DeclarationStatement[0]),
        cons_body
    ));
    
    // Add getters;
    ArrayList<Method> getters=new ArrayList<Method>();
    for(DeclarationStatement field:pred_class.dynamicFields()){
      cb=new ContractBuilder();
      cb.requires(create.invokation(null,false, ("valid"), new DeclarationStatement[0]));
      getters.add(create.function_decl(
          field.getType(),
          cb.getContract(),
          "get_"+field.getName(),
          new DeclarationStatement[0],
          create.field_name(field.getName())));
    }
    for(Method decl:getters){
      pred_class.add_dynamic(decl);
    }
    result=pred_class;
  }

  public void visit(MethodInvokation call){
    String field_name=null;
    if (call.object instanceof Dereference) {
      field_name=((Dereference)call.object).field;
    } else if (call.object instanceof NameExpression){
      field_name=((NameExpression)call.object).getName();
      if (!field_name.equals("this")) {
        Abort("unexpected field name %s",field_name);
      }
    } else {
      Abort("could not get field name at %s",call.object.getOrigin());
    }
    String label_name=call.getLabel(0).getName();
    if (pred_class.find_field(label_name)!=null){
      Abort("label %s declared twice",label_name);
    }
    String tmp[]=((ClassType)call.object.getType()).getNameFull();
    
    Type class_type=create.class_type(tmp);
    tmp[tmp.length-1]=tmp[tmp.length-1]+"_"+call.method;
    Type pred_type=create.class_type(tmp);

    pred_class.add_dynamic(create.field_decl(label_name,pred_type));
    
/*  
    valid_body=create.expression(StandardOperator.Star,valid_body,
        create.expression(StandardOperator.Perm,create.field_name(name),create.constant(100))
        );
    ASTNode ref_name=create.expression(StandardOperator.Select,create.field_name("ref"),create.field_name(name));
    valid_body=create.expression(StandardOperator.Star,valid_body,
        create.expression(StandardOperator.IFF,
            create.expression(StandardOperator.EQ,create.field_name(name),create.reserved_name("null")),
            create.expression(StandardOperator.EQ,ref_name,create.reserved_name("null"))
        )
    );
    ASTNode temp_body=create.invokation(create.field_name(name), false, ("valid"));
    temp_body=create.expression(StandardOperator.Star,temp_body,
        create.expression(StandardOperator.EQ,
            ref_name,
            create.invokation(create.field_name(name),false ,("get_ref"))
        )
    );
    DeclarationStatement decls[]=call.getDefinition().getArgs();
    ASTNode call_args[]=call.getArgs();
    for(int j=0;j<call_args.length;j++){
      temp_body=create.expression(StandardOperator.Star,temp_body,
          create.expression(StandardOperator.EQ,
              create.invokation(create.field_name(name), false, ("get_"+decls[j].getName())),
              call_args[j].apply(copy_rw)
          )
      );      
    }

    valid_body=create.expression(StandardOperator.Star,valid_body,
        create.expression(StandardOperator.Implies,
            create.expression(StandardOperator.NEQ,create.field_name(name),create.reserved_name("null")),
            temp_body
        )
    );         
*/
    ASTNode exists=create.expression(StandardOperator.NEQ,create.field_name(label_name),create.reserved_name("null")); 
    ASTNode valid=create.invokation(create.field_name(label_name), false, ("valid"));
    ASTNode check=create.invokation(create.field_name(label_name), false, ("check"),
        rewrite(call.object,call.getArgs()));
    auto_labels=false;
    result=create.expression(StandardOperator.Star,create.expression(StandardOperator.Star,exists,valid),check);
  }
  
/*
 *   public void visit(OperatorExpression e){
 
    switch (e.getOperator()){
    case Perm:
      ASTNode args[]=e.getArguments();
      result=create.expression(StandardOperator.Perm,args[],args[1].apply(this));
      break;
    default:
      super.visit(e);
      break;
    }
  }
  
  */
  
  public void visit(NameExpression e){
    NameExpression.Kind kind=e.getKind();
    String name=e.getName();
    switch(kind){
      case Local:
      case Argument:
        result=create.name(NameExpression.Kind.Unresolved,name);
        break;
      case Reserved:{
        if (name.equals("this")){
          result=create.dereference(create.reserved_name("this"),"ref");
          break;
        }
      }
      default:
        result=create.name(kind,name);
        break;
    }
  }
  
  public void visit(OperatorExpression e){
    switch(e.getOperator()){
      case Perm:
      case PointsTo:
        if (condition_level==0){
          ASTNode tmp=e.getArg(0);
          if (tmp instanceof Dereference){
            Dereference field=(Dereference)tmp;
            tmp=field.object;
            if (tmp instanceof NameExpression && ((NameExpression)tmp).getName().equals("this")){
              String name=field.field;
              Warning("adding getter %s_get_%s",pred_name,name);
              ContractBuilder cb=new ContractBuilder();
              cb.given(copy_rw.rewrite(pred_decl.getArgs()));
              cb.given(create.field_decl("req",create.class_type(class_name+"_"+pred_name)));
              cb.requires(create.expression(StandardOperator.NEQ,
                  create.local_name("req"),create.reserved_name("null")));
              cb.requires(
                  create.invokation(
                      create.local_name("req"),false,
                      ("valid"),new ASTNode[0]
                  )
              );
              int N=pred_decl.getArity();
              ASTNode args[]=new ASTNode[N+1];
              args[0]=create.reserved_name("this");
              for(int i=0;i<N;i++){
                args[i+1]=create.local_name(pred_decl.getArgument(i));
              }
              cb.requires(
                  create.invokation(
                      create.local_name("req"),false,
                      ("check"),
                      args
                  )
              );
              protected_fields.add(name);
              Method getter=create.function_decl(
                  field.getType(),
                  cb.getContract(),
                  pred_name+"_get_"+name,
                  new DeclarationStatement[0],
                  create.block(
                      create.expression(StandardOperator.Unfold,
                          create.invokation(
                              create.local_name("req"),false,
                              ("valid"),new ASTNode[0]
                          )
                      ),
                      create.return_statement(copy_rw.rewrite(field))
                  )
              );
              master.add_dynamic(getter);
            }
          }
        }
        super.visit(e);
        return;
      case Implies:
        condition_level++;
        super.visit(e);
        condition_level--;
        return;        
      default:
        super.visit(e);
        return;
    }
  }
}
