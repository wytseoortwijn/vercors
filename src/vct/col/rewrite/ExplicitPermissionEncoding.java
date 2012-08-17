package vct.col.rewrite;

import java.util.ArrayList;
import java.util.Arrays;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
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
  public AbstractRewriter copy_rw=new AbstractRewriter(){};
  
  public void visit(Method m){
    final String class_name=((ASTClass)m.getParent()).getName();
    if (m.kind==Method.Kind.Predicate){
      ASTClass pred_class=(ASTClass)(new PredicateClassGenerator()).rewrite(m);
      currentPackage.add_static(pred_class);
    } else {
      current_method=m;
      Contract c=m.getContract();
      ContractBuilder cb=new ContractBuilder();
      if (c!=null && c.given!=null){
        cb.given(rewrite_and_cast(c.given));
      }
      final ArrayList<DeclarationStatement> args=new ArrayList<DeclarationStatement>();
      for(DeclarationStatement arg:m.getArgs()){
        args.add(rewrite_and_cast(arg));
      }
      ClauseEncoding clause_rw;
      clause_rw=new ClauseEncoding(){
        public void visit(MethodInvokation i){
          if (i.labels()==1){
            NameExpression lbl=i.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(class_name+"_"+i.method.getName());
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(i);
            decl.setFlag(ASTFlags.GHOST, true);
            args.add(decl);
          }
          super.visit(i);
        }        
      };
      cb.requires(c.pre_condition.apply(clause_rw));
      clause_rw=new ClauseEncoding(){
        public void visit(MethodInvokation i){
          if (i.labels()==1){
            NameExpression lbl=i.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(class_name+"_"+i.method.getName());
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(i);
            decl.setFlag(ASTFlags.GHOST, true);
            decl.setFlag(ASTFlags.OUT_ARG, true);
            args.add(decl);
          }
          super.visit(i);
        }
      };
      cb.ensures(c.post_condition.apply(clause_rw));
      ASTNode body=rewrite_nullable(m.getBody());
      Method res=new Method(m.kind,m.getName(),m.getReturnType(), cb.getContract(), args.toArray(new DeclarationStatement[0]), body);
      res.setOrigin(m);
      result=res;
      current_method=null;
    }
  }
  
  private Method current_method;
  
  public void visit(NameExpression name){
    if (name.getKind()==NameExpression.Kind.Label){
      if (current_method!=null && current_method.getContract().hasLabel(name.getName())){
        result=create.local_name(name.getName());
        return;
      }
    }
    super.visit(name);
  }
  
  public void visit(OperatorExpression e){
    switch (e.getOperator()){
    case Unfold:
    case Fold:
      ASTNode arg1=e.getArg(0);
      if (arg1.labels()==1){
        for(NameExpression lbl:arg1.getLabels()){
          result=create.expression(e.getOperator(),
              create.invokation(create.local_name(lbl.getName()), false, create.method_name("valid"))
              );
          return;
        }
      } else {
        super.visit(e);
      }
      break;
    default:
      super.visit(e);
      break;
    }
  }
}

class ClauseEncoding extends AbstractRewriter {

  public AbstractRewriter copy_rw=new AbstractRewriter(){};

  public void visit(MethodInvokation i) {
    if (i.getDefinition().getKind()!=Method.Kind.Predicate){
      result=copy_rw.rewrite(i);
    } else {
      if (i.labels()==0){
        Abort("Every predicate invokation must be labeled.");
      }
      NameExpression lbl=i.getLabel(0);
      ASTNode body=create.expression(StandardOperator.NEQ,create.method_name(lbl.getName()),create.reserved_name("null"));
      body=create.expression(StandardOperator.Star,body,
          create.invokation(create.local_name(lbl.getName()), false, create.method_name("valid")));
      body=create.expression(StandardOperator.Star,body,
          create.invokation(
              create.local_name(lbl.getName()),
              false,
              create.method_name("check"),
              rewrite(i.object,i.getArgs())
          ));
      
      result=body;
      auto_labels=false;
    }
  }
}

class PredicateClassGenerator extends AbstractRewriter {
  public AbstractRewriter copy_rw=new AbstractRewriter(){};
  private String class_name;
  private String pred_name;
  private ASTClass pred_class;
  private boolean in_use=false;
 
  public void visit(Method m){
    if (in_use) {
      Abort("Predicate class generator already in use.");
    }
    in_use=true;
    
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
    ASTNode valid_body=create.expression(StandardOperator.NEQ,create.field_name("ref"),create.reserved_name("null"));
    // Note that permission for fields will be added later.
    
    // Add arguments as fields:
    for (int i=0;i<args.length;i++){
      pred_class.add_dynamic(args[i].apply(copy_rw));
      if (args[i].getType().isPrimitive(PrimitiveType.Sort.Fraction)){
        valid_body=create.expression(StandardOperator.Star,valid_body,
            create.expression(StandardOperator.LT,create.constant(0),create.field_name(args[i].getName()))
            );
        valid_body=create.expression(StandardOperator.Star,valid_body,
            create.expression(StandardOperator.LTE,create.field_name(args[i].getName()),create.constant(100))
            );
      }
    }
/*
    // Rewrite the body of the predicate:
    for(ASTNode part:ASTUtils.conjuncts(m.getBody())){
      if (part instanceof MethodInvokation){
        MethodInvokation call=(MethodInvokation)part;
        String name=((NameExpression)((OperatorExpression)call.object).getArg(1)).getName();
        if (pred_class.find_field(name)==null){
          pred_class.add_dynamic(create.field_decl(name,pred_type));
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
          ASTNode temp_body=create.invokation(create.field_name(name), false, create.method_name("valid"));
          temp_body=create.expression(StandardOperator.Star,temp_body,
              create.expression(StandardOperator.EQ,
                  ref_name,
                  create.invokation(create.field_name(name),false ,create.method_name("get_ref"))
              )
          );
          DeclarationStatement decls[]=call.getDefinition().getArgs();
          ASTNode call_args[]=call.getArgs();
          for(int j=0;j<call_args.length;j++){
            temp_body=create.expression(StandardOperator.Star,temp_body,
                create.expression(StandardOperator.EQ,
                    create.invokation(create.field_name(name), false, create.method_name("get_"+decls[j].getName())),
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
        }
      } else {
        valid_body=create.expression(StandardOperator.Star,valid_body,part.apply(this));
      }
    }    
*/

    // Rewrite the body, which will cause field to be created.
    valid_body=create.expression(StandardOperator.Star,valid_body,rewrite(m.getBody()));
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
    cb.requires(create.invokation(null,false, create.method_name("valid"), new DeclarationStatement[0]));
    ASTNode check_body=create.expression(StandardOperator.EQ,create.field_name("ref"),create.local_name("object"));
    for (DeclarationStatement decl:m.getArgs()){
      ASTNode field=create.expression(StandardOperator.Select,create.reserved_name("this"),create.field_name(decl.getName()));
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
    
    // Add getters;
    ArrayList<Method> getters=new ArrayList<Method>();
    for(DeclarationStatement field:pred_class.dynamicFields()){
      cb=new ContractBuilder();
      cb.requires(create.invokation(null,false, create.method_name("valid"), new DeclarationStatement[0]));
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
    if (call.object instanceof OperatorExpression) {
      field_name=((NameExpression)((OperatorExpression)call.object).getArg(1)).getName();
    } else {
      Abort("could not get field name at %s",call.object.getOrigin());
    }
    String label_name=call.getLabel(0).getName();
    if (pred_class.find_field(label_name)!=null){
      Abort("label %s declared twice",label_name);
    }
    String tmp[]=((ClassType)call.object.getType()).getNameFull();
    
    Type class_type=create.class_type(tmp);
    tmp[tmp.length-1]=tmp[tmp.length-1]+"_"+call.method.getName();
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
    ASTNode temp_body=create.invokation(create.field_name(name), false, create.method_name("valid"));
    temp_body=create.expression(StandardOperator.Star,temp_body,
        create.expression(StandardOperator.EQ,
            ref_name,
            create.invokation(create.field_name(name),false ,create.method_name("get_ref"))
        )
    );
    DeclarationStatement decls[]=call.getDefinition().getArgs();
    ASTNode call_args[]=call.getArgs();
    for(int j=0;j<call_args.length;j++){
      temp_body=create.expression(StandardOperator.Star,temp_body,
          create.expression(StandardOperator.EQ,
              create.invokation(create.field_name(name), false, create.method_name("get_"+decls[j].getName())),
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
    ASTNode valid=create.invokation(create.field_name(label_name), false, create.method_name("valid"));
    ASTNode check=create.invokation(create.field_name(label_name), false, create.method_name("check"),
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
    if (e.getKind()==NameExpression.Kind.Reserved && e.getName().equals("this")){
      result=create.field_name("ref");
    } else {
      super.visit(e);
    }
  }
}
