package vct.col.rewrite;

import vct.col.ast.ASTNode;
import vct.col.ast.BindingExpression;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import static vct.col.ast.PrimitiveType.Sort.Array;
import static vct.col.ast.PrimitiveType.Sort.Cell;
import static vct.col.ast.PrimitiveType.Sort.Sequence;
import vct.col.ast.ProgramUnit;

public class RewriteArray extends AbstractRewriter {

  public RewriteArray(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public void visit(PrimitiveType t){
    switch(t.sort){
      case Array:
      {
        result=create.primitive_type(Sequence,create.primitive_type(Cell,rewrite(t.getArg(0))));
        break;
      }
      default:
        super.visit(t);
    }
  }
  
  @Override
  public void visit(OperatorExpression e){
    if (e.getOperator()==StandardOperator.ArrayPerm){
      Type t=(Type)(e.getArg(0).getType().getArg(0));
      ASTNode array_name=e.getArg(0);
      
      // Given a sub-array...
      String name="__sub_array_"+(++count);
      Type type=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t)));
      currentContractBuilder.given(create.field_decl(name,type));

      ASTNode tmp;
      // the size of the sub-array is count, before and after.
      tmp=create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.local_name(name)),
          rewrite(e.getArg(3))
      );
      currentContractBuilder.requires(tmp);
      currentContractBuilder.ensures(tmp);

      DeclarationStatement decl[]=new DeclarationStatement[1];
      String vname="_auto_i_";
      decl[0]=create.field_decl(vname,create.primitive_type(PrimitiveType.Sort.Integer));
      tmp=new BindingExpression(
          Binder.FORALL,
          create.primitive_type(PrimitiveType.Sort.Boolean),
          decl,
          create.expression(StandardOperator.Star,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name(vname)),
              create.expression(StandardOperator.LT,create.local_name(vname),
                  create.expression(StandardOperator.Size,create.unresolved_name(name)))
          ),
          create.expression(StandardOperator.EQ,
              create.expression(StandardOperator.Subscript,
                  create.unresolved_name(name),create.local_name(vname)),
              create.expression(StandardOperator.Subscript,rewrite(array_name),
                 create.expression(StandardOperator.Plus,rewrite(e.getArg(1)),
                     create.expression(StandardOperator.Mult,rewrite(e.getArg(2)),
                         create.local_name(vname)
                     )
                 )
              )             
          )
      );
      tmp.setOrigin(e.getOrigin());
      currentContractBuilder.requires(tmp);
      currentContractBuilder.ensures(tmp);
      tmp=new BindingExpression(
          Binder.FORALL,
          create.primitive_type(PrimitiveType.Sort.Boolean),
          decl,
          create.expression(StandardOperator.Star,
            create.expression(StandardOperator.Star,
              create.expression(StandardOperator.LTE,rewrite(e.getArg(1)),create.local_name(vname)),
              create.expression(StandardOperator.LT,create.local_name(vname),
                  create.expression(StandardOperator.Plus,rewrite(e.getArg(1)),
                      create.expression(StandardOperator.Mult,rewrite(e.getArg(2)),
                          rewrite(e.getArg(3))
                      )
                  )
                  )
            ),
            create.expression(StandardOperator.EQ,
                create.expression(StandardOperator.Mod,create.local_name(vname),rewrite(e.getArg(2))),
                rewrite(e.getArg(1))
            )
          ),
          create.expression(StandardOperator.EQ,
              create.expression(StandardOperator.Subscript,
                  rewrite(array_name),create.local_name(vname)),
              create.expression(StandardOperator.Subscript,create.unresolved_name(name),
                 create.expression(StandardOperator.Div,
                     create.expression(StandardOperator.Minus,
                         create.local_name(vname),
                         rewrite(e.getArg(1))
                     ),
                     rewrite(e.getArg(2))
                 )
              )             
          )
      );
      tmp.setOrigin(e.getOrigin());
      currentContractBuilder.requires(tmp);
      currentContractBuilder.ensures(tmp);

      // permission on the sub-array.
      ASTNode res=create.expression(StandardOperator.Perm,
          create.dereference(
              create.expression(StandardOperator.Subscript,
                  create.local_name(name),
                  create.reserved_name("*")
              ), "item"
          ),
          rewrite(e.getArg(4))
      );
      
      result=res;
      return;
    }
    super.visit(e);
    if (e.getOperator()==StandardOperator.Subscript && ((PrimitiveType)e.getArg(0).getType()).sort==Array){
       result=create.dereference(result,"item");
    } else if (e.getOperator()==StandardOperator.Perm
             && (e.getArg(0) instanceof OperatorExpression)
             && (((OperatorExpression)e.getArg(0)).getOperator()==StandardOperator.Subscript)
             && (((OperatorExpression)e.getArg(0)).getArg(1).toString().equals("*"))
    ){
      ASTNode res=result;
      DeclarationStatement decl[]=new DeclarationStatement[1];
      String arrayname=((OperatorExpression)e.getArg(0)).getArg(0).toString();
      String name="_auto_i_";
      decl[0]=create.field_decl(name,create.primitive_type(PrimitiveType.Sort.Integer));
      ASTNode tmp=new BindingExpression(
          Binder.FORALL,
          create.primitive_type(PrimitiveType.Sort.Boolean),
          decl,
          create.expression(StandardOperator.Star,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name(name)),
              create.expression(StandardOperator.LT,create.local_name(name),
                  create.expression(StandardOperator.Size,create.unresolved_name(arrayname)))
          ),
          create.expression(StandardOperator.NEQ,
              create.expression(StandardOperator.Subscript,create.unresolved_name(arrayname),create.local_name(name))
              ,create.reserved_name("null"))
      );
      tmp.setOrigin(result.getOrigin());
      result=create.expression(StandardOperator.Star,res,tmp);
    }
  }
  
  private int count=0;
  
  @Override
  public void visit(BindingExpression e){
    if (e.binder==BindingExpression.Binder.STAR){
      Type t=((OperatorExpression)e.main).getArg(0).getType();
      ASTNode array_name=((OperatorExpression)e.main).getArg(0);
      array_name=((OperatorExpression)array_name).getArg(0);
      ASTNode index_expr=((OperatorExpression)e.main).getArg(0);
      index_expr=((OperatorExpression)index_expr).getArg(1);
      
      String name="__sub_array_"+(++count);
      Type type=create.primitive_type(Sort.Sequence,create.primitive_type(Sort.Cell,rewrite(t)));
      currentContractBuilder.given(create.field_decl(name,type));
      ASTNode tmp;
      tmp=create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.local_name(name)),
          rewrite(((OperatorExpression)((OperatorExpression)e.select).getArg(1)).getArg(1))
      );
      currentContractBuilder.requires(tmp);
      tmp=create.binder(
          BindingExpression.Binder.FORALL,
          null,
          rewrite(e.getDeclarations()),
          rewrite(e.select),
          create.expression(StandardOperator.EQ,
              create.expression(StandardOperator.Subscript,
                  create.local_name(name),
                  create.local_name(e.getDeclaration(0).getName())
              ),
              create.expression(StandardOperator.Subscript,
                  rewrite(array_name),
                  rewrite(index_expr)
              )

          )
      );
      currentContractBuilder.requires(tmp);
      DeclarationStatement args[]=new DeclarationStatement[1];
      args[0]=create.field_decl("i",create.primitive_type(Sort.Integer));
      ASTNode res=create.binder(
          BindingExpression.Binder.FORALL,
          null,
          args,
          create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE,create.constant(0),create.local_name("i")),
              create.expression(StandardOperator.LT,create.local_name("i"),
                  create.expression(StandardOperator.Size,rewrite(array_name))
              )
          ),
          create.expression(StandardOperator.NEQ,
              create.expression(StandardOperator.Subscript,
                  rewrite(array_name),
                  create.local_name("i")
              ),
              create.reserved_name("null")
          )
      );
      tmp=create.expression(StandardOperator.Perm,
          create.dereference(
              create.expression(StandardOperator.Subscript,
                  create.local_name(name),
                  create.reserved_name("*")
              ), "item"
          ),
          rewrite(((OperatorExpression)e.main).getArg(1))
      );
      res=create.expression(StandardOperator.Star,res,tmp);
      
      //copy_rw.rewrite(returns)
      /*
      
      ContractBuilder cb=new ContractBuilder();
      
      cb.requires(create.binder(
          BindingExpression.Binder.FORALL,
          null,
          rewrite(e.getDeclarations()),
          rewrite(e.select),
          create.expression(StandardOperator.LT,
              rewrite(index_expr),
              create.expression(StandardOperator.Size,create.local_name("__from"))
          )
      ));
      
      cb.ensures(create.expression(StandardOperator.EQ,
          create.expression(StandardOperator.Size,create.reserved_name("\\result")),
          rewrite(((OperatorExpression)((OperatorExpression)e.select).getArg(1)).getArg(1))
      ));
      cb.ensures(create.binder(
          BindingExpression.Binder.FORALL,
          null,
          rewrite(e.getDeclarations()),
          rewrite(e.select),
          create.expression(StandardOperator.EQ,
              create.expression(StandardOperator.Subscript,
                  create.reserved_name("\\result"),
                  create.local_name(e.getDeclaration(0).getName())
              ),
              create.expression(StandardOperator.Subscript,
                  create.local_name("__from"),
                  rewrite(index_expr)
              )

          )
      ));
      Contract contract=cb.getContract();
      DeclarationStatement args[]=new DeclarationStatement[1];
      args[0]=create.field_decl("__from",copy_rw.rewrite(returns));
      Method m=create.function_decl(returns, contract, "__select_"+(++count), args, null);
      currentClass.add_dynamic(m);
      args[0]=create.field_decl("__selected_"+count,copy_rw.rewrite(returns),
          create.invokation(null,null,"__select_"+count,rewrite(array_name))
      );

      result=create.binder(BindingExpression.Binder.LET,
          null,
          null,//args
          null,
          create.expression(StandardOperator.Perm,
              create.dereference(
                  create.expression(StandardOperator.Subscript,
                      create.local_name("__selected_"+count),
                      create.reserved_name("*")
                  ), "item"
              ),
              rewrite(((OperatorExpression)e.main).getArg(1))
          )
      );
      */
      result=res;
    } else {
      super.visit(e);
    }
  }
}

