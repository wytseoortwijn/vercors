package vct.col.rewrite;

import java.util.ArrayList;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.ASTFlags;
import vct.col.ast.ASTNode;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.ASTUtils;
import static hre.System.*;

public class ExplicitPermissionEncoding extends AbstractRewriter {
  public AbstractRewriter copy_rw=new AbstractRewriter(){};
  public ClauseEncoding clause_rw=new ClauseEncoding();
  
  public void visit(Method m){
    String class_name=((ASTClass)m.getParent()).getName();
    if (m.kind==Method.Kind.Predicate){
      ASTClass pred_class=(ASTClass)(new PredicateClassGenerator()).rewrite(m);
      currentPackage.add_static(pred_class);
    } else {
      current_method=m;
      Contract c=m.getContract();
      ContractBuilder cb=new ContractBuilder();
      ArrayList<DeclarationStatement> args=new ArrayList<DeclarationStatement>();
      for(DeclarationStatement arg:m.getArgs()){
        args.add(rewrite_and_cast(arg));
      }
      for(ASTNode part:ASTUtils.conjuncts(c.pre_condition)){
        if (part instanceof MethodInvokation){
          MethodInvokation i=(MethodInvokation)part;
          if (i.labels()==1){
            NameExpression lbl=part.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(class_name+"_"+i.method.getName());
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(part);
            decl.setFlag(ASTFlags.GHOST, true);
            args.add(decl);
            cb.requires(i.apply(clause_rw));
          } else {
            cb.requires(part.apply(copy_rw));
          }
        } else {
          cb.requires(part.apply(copy_rw));
        }
      }
      for(ASTNode part:ASTUtils.conjuncts(c.post_condition)){
        if (part instanceof MethodInvokation){
          MethodInvokation i=(MethodInvokation)part;
          if (i.labels()==1){
            NameExpression lbl=part.getLabel(0);
            String pred_name=lbl.getName();
            Type t=create.class_type(class_name+"_"+i.method.getName());
            DeclarationStatement decl=new DeclarationStatement(lbl.getName(),t,create.reserved_name("null"));
            decl.setOrigin(part);
            decl.setFlag(ASTFlags.GHOST, true);
            decl.setFlag(ASTFlags.OUT_ARG, true);
            args.add(decl);
            //cb.ensures(create.expression(StandardOperator.NEQ,create.method_name(lbl.getName()),create.reserved_name("null")));
            //cb.ensures(create.invokation(create.local_name(lbl.getName()), false, create.method_name("valid")));
            cb.ensures(i.apply(clause_rw));
          } else {
            cb.ensures(part.apply(copy_rw));
          }
        } else {
          cb.ensures(part.apply(copy_rw));
        }
      }
      ASTNode body=m.getBody().apply(this);
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
    NameExpression lbl=i.getLabel(0);
    ASTNode body=create.expression(StandardOperator.NEQ,create.method_name(lbl.getName()),create.reserved_name("null"));
    body=create.expression(StandardOperator.Star,body,
        create.invokation(create.local_name(lbl.getName()), false, create.method_name("valid")));
    body=create.expression(StandardOperator.Star,body,
        create.expression(StandardOperator.EQ,
            create.invokation(create.local_name(lbl.getName()), false, create.method_name("get_ref")),
            i.object.apply(copy_rw)
        )
    );
    Method m=i.getDefinition();
    DeclarationStatement decls[]=m.getArgs();
    ASTNode args[]=i.getArgs();
    for(int j=0;j<args.length;j++){
      body=create.expression(StandardOperator.Star,body,
          create.expression(StandardOperator.EQ,
              create.invokation(create.local_name(lbl.getName()), false, create.method_name("get_"+decls[j].getName())),
              args[j].apply(copy_rw)
          )
      );      
    }
    result=body;
  }
}

class PredicateClassGenerator extends AbstractRewriter {
  public AbstractRewriter copy_rw=new AbstractRewriter(){};
  private String class_name;
  private String pred_name;
  private ASTClass pred_class;
  
  public void visit(Method m){
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
    ASTNode valid_body=create.expression(StandardOperator.Perm,create.field_name("ref"),create.constant(100));
    valid_body=create.expression(StandardOperator.Star,valid_body,
        create.expression(StandardOperator.NEQ,create.field_name("ref"),create.reserved_name("null"))
    );
    // Add arguments as fields:
    for (int i=0;i<args.length;i++){
      pred_class.add_dynamic(args[i].apply(copy_rw));
      valid_body=create.expression(StandardOperator.Star,valid_body,
          create.expression(StandardOperator.Perm,create.field_name(args[i].getName()),create.constant(100))
          );
      if (args[i].getType().isPrimitive(PrimitiveType.Sort.Fraction)){
        valid_body=create.expression(StandardOperator.Star,valid_body,
            create.expression(StandardOperator.LT,create.constant(0),create.field_name(args[i].getName()))
            );
        valid_body=create.expression(StandardOperator.Star,valid_body,
            create.expression(StandardOperator.LTE,create.field_name(args[i].getName()),create.constant(100))
            );
      }
    }
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
    
    // Add valid predicate;
    pred_class.add_dynamic(create.predicate("valid", valid_body , new DeclarationStatement[0] ));
    
    // Add getters;
    ArrayList<Method> getters=new ArrayList<Method>();
    for(DeclarationStatement field:pred_class.dynamicFields()){
      ContractBuilder cb=new ContractBuilder();
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
