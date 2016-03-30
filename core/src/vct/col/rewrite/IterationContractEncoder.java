package vct.col.rewrite;

import hre.ast.BranchOrigin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map.Entry;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTReserved;
import vct.col.ast.BindingExpression;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.BlockStatement;
import vct.col.ast.ConstantExpression;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.ForEachLoop;
import vct.col.ast.IfStatement;
import vct.col.ast.IntegerValue;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.ast.Value;
import vct.col.ast.VariableDeclaration;
import vct.col.util.ASTFactory;
import vct.col.util.ASTUtils;
import vct.col.util.NameScanner;
import vct.col.util.OriginWrapper;

public class IterationContractEncoder extends AbstractRewriter {

  private AtomicInteger counter=new AtomicInteger();
    
  public IterationContractEncoder(ProgramUnit arg) {
    super(arg);
  }
    
  private int ConstantExpToInt(ConstantExpression e)
  {	
	  return ((IntegerValue)e.value).value;			  	
	  
  }  
  private boolean sidecondition_check(OperatorExpression e)  {
	   ///1. check the distance of dependence constant expressions 	  
		  if(e.getArg(2) instanceof ConstantExpression)
		  {	  			  							  	  						  				  		
			  return ConstantExpToInt((ConstantExpression)e.getArg(2)) > 0 ;			  		
		  } else{
			  return false;			  
			}					  			  	
	  }
  
  private String current_label;
  
  private Stack<ASTNode> guard_stack=new Stack();
  
  private class SendRecvInfo {
    final String label=current_label;
    final ArrayList<ASTNode> guards=new ArrayList(guard_stack);
    final ASTNode stat;
    public SendRecvInfo(ASTNode stat){
      this.stat=stat;
    }
  }
  
  private HashMap<String,SendRecvInfo> send_recv_map=new HashMap();
  
  @Override
  public void enter(ASTNode node){
    super.enter(node);
    if (node.labels()>0){
      current_label=node.getLabel(0).getName();
      Debug("current label is %s",current_label);
    }
  }
  
  @Override
  public void leave(ASTNode node){
    if (node.labels()>0){
      current_label=null;
    }
    super.leave(node);
  }
  
  public void visit(OperatorExpression e)
  { //DRB
	  
	  int N=counter.incrementAndGet();	  
	  ContractBuilder cb = new ContractBuilder();	  
	  Hashtable<String,Type> vars=new Hashtable<String,Type>();
	  BranchOrigin branch;
	  
	  switch(e.getOperator())
	  {
	  case Send:
	    if (current_label==null){
	      Fail("send in unlabeled position");
	    }
	    if (send_recv_map.get(current_label)!=null){
        Fail("more than one send/recv in block %s.",current_label);
	    }
	    send_recv_map.put(current_label,new SendRecvInfo(e));
		  // create method contract
		  //and call the method

		  //vct.util.Configuration.getDiagSyntax().print(System.out,e.getArg(0));
		  //System.out.printf("\n");		  
  		  
		  String send_name="send_body_"+N;
		  
	      ArrayList<DeclarationStatement> send_decl=new ArrayList();// declaration of parameters for send_check
	      ArrayList<ASTNode> send_args=new ArrayList();// the arguments to the host_check method
	      
	      vars=new Hashtable<String,Type>();
	      e.accept(new NameScanner(vars));
	      
	      for(String var:vars.keySet())	 
	      {
	          send_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
	          send_args.add(create.unresolved_name(var));
	      }
		  
	      cb = new ContractBuilder();		  		 
		  cb.requires(copy_rw.rewrite(e.getArg(0))); //update new contract
  
		  Method send_body=create.method_decl(
		          create.primitive_type(PrimitiveType.Sort.Void),
		          cb.getContract(), //method contract 
		          send_name,
		          send_decl.toArray(new DeclarationStatement[0]),
		          null // no body
		      );
		  
	      //Error management  --> line numbers, origins , ...
		  branch=new BranchOrigin("Send Statement",null);
	      OriginWrapper.wrap(null,send_body, branch);      
	      //Error management  --> line numbers, origins , ...	      
	      
		  //Check for side conditions 
		  if(!sidecondition_check(e))
		  {
		      super.visit(e);
		      Fail("\nThe distance of dependence in the \"send\" statement should be positive.");		      
		  }
		  ///Check for side conditions	      		  
		  
	      currentTargetClass.add_dynamic(send_body);
	      
	      result=create.invokation(null,null,send_name,send_args.toArray(new ASTNode[0]));	      
		  break;
	  case Recv:
		  // create method contract
		  // and call the method
		  // vct.util.Configuration.getDiagSyntax().print(System.out,e.getArg(0));//DRB		        		  		  
      if (current_label==null){
        Fail("recv in unlabeled position");
      }
      if (send_recv_map.get(current_label)!=null){
        Fail("more than one send/recv in block %s.",current_label);
      }
      send_recv_map.put(current_label,new SendRecvInfo(e));
		  
		  String recv_name="recv_body_"+N;		  	      
	      ArrayList<DeclarationStatement> recv_decl=new ArrayList();// declaration of parameters for send_check
	      ArrayList<ASTNode> recv_args=new ArrayList();// the arguments to the host_check method
	      
	      vars=new Hashtable<String,Type>();
	      e.accept(new NameScanner(vars));
	      
	      for(String var:vars.keySet())	 
	      {
	          recv_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
	          recv_args.add(create.unresolved_name(var));
	      }
		  
	      cb = new ContractBuilder();		  		 
		  cb.ensures(copy_rw.rewrite(e.getArg(0))); //update new contract
		  
		  Method recv_body=create.method_decl(
		          create.primitive_type(PrimitiveType.Sort.Void),
		          cb.getContract(), //method contract 
		          recv_name,
		          recv_decl.toArray(new DeclarationStatement[0]),
		          null // no body
		      );
		  
	      //Error management  --> line numbers, origins , ...
		  branch=new BranchOrigin("Recv Statement",null);
	      OriginWrapper.wrap(null,recv_body, branch);      
	      //Error management  --> line numbers, origins , ...
	      
	      //System.out.printf("generated %s at %s%n",recv_body.name,recv_body.getOrigin());

	      //Check for side conditions
		  		 
		  if(!sidecondition_check(e))
		  {			  
		      super.visit(e);
		      Fail("\nThe distance of dependence in the \"recv\" statement should be positive.");		      
		  }
		  ///Check for side conditions			  
	      currentTargetClass.add_dynamic(recv_body);	      
	      result=create.invokation(null,null,recv_name,recv_args.toArray(new ASTNode[0]));
	      		  
		  break;
	  default:
		  super.visit(e);
			  
	  }
	  
  }
  
  
  
  @Override
  public void visit(ForEachLoop s){
    Contract c=s.getContract();
    if (c==null) Fail("for each loop without iteration contract");
    Hashtable<String,Type> body_vars=free_vars(s.body,c,s.guard);
    //System.out.printf("free in %s are %s%n",s.body,body_vars);
    //Hashtable<String,Type> iters=new Hashtable<String,Type>();
    Hashtable<String,Type> main_vars=new Hashtable(body_vars);
    for(DeclarationStatement decl:s.decls){
      //iters.put(decl.name,decl.getType());
      main_vars.remove(decl.name);
    }

    int N=counter.incrementAndGet();
    String main_name="loop_main_"+N;
    String body_name="loop_body_"+N;
    ContractBuilder main_cb=new ContractBuilder();
    ContractBuilder body_cb=new ContractBuilder();

    for(ASTNode clause:ASTUtils.conjuncts(c.invariant, StandardOperator.Star)){
      Hashtable<String,Type> clause_vars=free_vars(clause);
      for(DeclarationStatement decl:s.decls){
        if (clause_vars.get(decl.name)!=null){
          Fail("illegal iteration invariant at %s",clause.getOrigin());
        }
      }
      if (clause.getType().isBoolean() || clause.isa(StandardOperator.Value)){
        main_cb.requires(rewrite(clause));
        main_cb.ensures(rewrite(clause));
        body_cb.requires(rewrite(clause));
        body_cb.ensures(rewrite(clause));
      } else {
        Fail("illegal iteration invariant at %s",clause.getOrigin());
      }
    }
    
    DeclarationStatement iter_decls[] = s.decls;
    outer:for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition, StandardOperator.Star)){
      if (clause.getType().isBoolean()){
        //for(DeclarationStatement decl:iter_decls){
          //if (ASTUtils.find_name(clause,decl.name)){
            main_cb.requires(create.forall(copy_rw.rewrite(s.guard), rewrite(clause) , iter_decls));
            //continue outer;
          //}
        //}
        //main_cb.requires(rewrite(clause));
      } else if (clause.isa(StandardOperator.ReducibleSum)){
        OperatorExpression expr=(OperatorExpression) clause;
        main_cb.requires(create.expression(StandardOperator.Perm,
            copy_rw.rewrite(expr.getArg(0)),
            create.reserved_name(ASTReserved.FullPerm)
        ));  
      } else if(is_a_quantified(clause,Binder.STAR,StandardOperator.ReducibleSum)){
        BindingExpression bclause=(BindingExpression)clause;
        OperatorExpression expr=(OperatorExpression)bclause.main;
        main_cb.requires(create.starall(
            bclause.select,
            create.expression(StandardOperator.Perm,
                copy_rw.rewrite(expr.getArg(0)),
                create.reserved_name(ASTReserved.FullPerm)
            ),
            bclause.getDeclarations()
        ));
      } else {
        main_cb.requires(create.starall(copy_rw.rewrite(s.guard), rewrite(clause) , iter_decls));
      }
    }
    outer:for(ASTNode clause:ASTUtils.conjuncts(c.post_condition, StandardOperator.Star)){
      if (clause.getType().isBoolean()){
        //for(DeclarationStatement decl:iter_decls){
          //if (ASTUtils.find_name(clause,decl.name)){
            main_cb.ensures(create.forall(copy_rw.rewrite(s.guard), rewrite(clause) , iter_decls));
            //continue outer;
          //}
        //}
        //main_cb.ensures(rewrite(clause));
      } else if (clause.isa(StandardOperator.Contribution)){
        OperatorExpression expr=(OperatorExpression) clause;
        main_cb.ensures(create.expression(StandardOperator.Perm,
            copy_rw.rewrite(expr.getArg(0)),
            create.reserved_name(ASTReserved.FullPerm)
        ));
        main_cb.ensures(create.expression(StandardOperator.EQ,
            copy_rw.rewrite(expr.getArg(0)),
            plus(create.expression(StandardOperator.Old,copy_rw.rewrite(expr.getArg(0))),
                 create.summation(copy_rw.rewrite(s.guard), rewrite(expr.getArg(1)) , iter_decls))
        ));
      } else if(is_a_quantified(clause,Binder.STAR,StandardOperator.Contribution)){
        BindingExpression bclause=(BindingExpression)clause;
        OperatorExpression expr=(OperatorExpression)bclause.main;
        main_cb.ensures(create.starall(
            bclause.select,
            create.expression(StandardOperator.Perm,
                copy_rw.rewrite(expr.getArg(0)),
                create.reserved_name(ASTReserved.FullPerm)
            ),
            bclause.getDeclarations()
        ));
        main_cb.ensures(create.forall(
            bclause.select,
            create.expression(StandardOperator.EQ,
                copy_rw.rewrite(expr.getArg(0)),
                plus(create.expression(StandardOperator.Old,copy_rw.rewrite(expr.getArg(0))),
                     create.summation(copy_rw.rewrite(s.guard), rewrite(expr.getArg(1)) , iter_decls))
            ),
            bclause.getDeclarations()
        ));        
      } else {
        main_cb.ensures(create.starall(copy_rw.rewrite(s.guard), rewrite(clause) , iter_decls));
      }
    }

    DeclarationStatement main_pars[]=gen_pars(main_vars);
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        main_cb.getContract(),
        main_name,
        main_pars,
        null
    ));
    body_cb.requires(rewrite(s.guard));
    body_cb.ensures(rewrite(s.guard));

    for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition, StandardOperator.Star)){
      if(clause.isa(StandardOperator.ReducibleSum)){
        OperatorExpression expr=(OperatorExpression) clause;
        body_cb.requires(create.expression(StandardOperator.PointsTo,
            copy_rw.rewrite(expr.getArg(0)),
            create.reserved_name(ASTReserved.FullPerm),
            create.constant(0)
        ));
      } else if(is_a_quantified(clause,Binder.STAR,StandardOperator.ReducibleSum)){
        BindingExpression bclause=(BindingExpression)clause;
        OperatorExpression expr=(OperatorExpression)bclause.main;
        body_cb.requires(create.starall(
            bclause.select,
            create.expression(StandardOperator.Perm,
                copy_rw.rewrite(expr.getArg(0)),
                create.reserved_name(ASTReserved.FullPerm)
            ),
            bclause.getDeclarations()
        ));
        body_cb.requires(create.forall(
            bclause.select,
            create.expression(StandardOperator.EQ,
                copy_rw.rewrite(expr.getArg(0)),
                create.constant(0)
            ),
            bclause.getDeclarations()
        ));
      } else {
        body_cb.requires(rewrite(clause));
      }
    }
    for(ASTNode clause:ASTUtils.conjuncts(c.post_condition, StandardOperator.Star)){
      if(clause.isa(StandardOperator.Contribution)){
        OperatorExpression expr=(OperatorExpression) clause;
        body_cb.ensures(create.expression(StandardOperator.PointsTo,
            rewrite(expr.getArg(0)),
            create.reserved_name(ASTReserved.FullPerm),
            rewrite(expr.getArg(1))
        ));       
      } else if(is_a_quantified(clause,Binder.STAR,StandardOperator.Contribution)){
        BindingExpression bclause=(BindingExpression)clause;
        OperatorExpression expr=(OperatorExpression)bclause.main;
        body_cb.ensures(create.starall(
            bclause.select,
            create.expression(StandardOperator.Perm,
                rewrite(expr.getArg(0)),
                create.reserved_name(ASTReserved.FullPerm)
            ),
            bclause.getDeclarations()
        ));
        body_cb.ensures(create.forall(
            bclause.select,
            create.expression(StandardOperator.EQ,
                rewrite(expr.getArg(0)),
                rewrite(expr.getArg(1))
            ),
            bclause.getDeclarations()
        ));
      } else {
        body_cb.ensures(rewrite(clause));
      }
    }
    
    DeclarationStatement body_pars[]=gen_pars(body_vars);
    currentTargetClass.add(create.method_decl(
        create.primitive_type(Sort.Void),
        body_cb.getContract(),
        body_name,
        body_pars,
        rewrite(s.body)
    ));
    String var_name=s.decls[s.decls.length-1].name;
    check_send_recv(body_pars, var_name, s.guard);  
    result=gen_call(main_name,main_vars);
  }
  
  private boolean is_a_quantified(ASTNode expr, Binder bd, StandardOperator op) {
    if (expr instanceof BindingExpression){
      BindingExpression b=(BindingExpression) expr;
      if (b.binder==bd){
        return b.main.isa(op);
      }
    }
    return false;
  }

  

  
  
  /* replaced by for each loop.
  @Override
  public void visit(LoopStatement loop){
	  
    Contract c=loop.getContract(); 
    
    if (c!=null && (c.pre_condition != c.default_true || c.post_condition != c.default_true)){
      Warning("processing iteration contract");
      Hashtable<String,Type> vars=free_vars(loop.getBody(),c,loop.getEntryGuard());
      Hashtable<String,Type> iters=new Hashtable<String,Type>();
      loop.getUpdateBlock().accept(new NameScanner(iters));
      
      for(String var:iters.keySet()){
    	  System.err.printf("iter %s : %s%n", var,iters.get(var));    	 
      }
      int N=counter.incrementAndGet();
      String main_name="loop_main_"+N;
      String body_name="loop_body_"+N;
      ArrayList<DeclarationStatement> main_decl=new ArrayList();// the declaration of parameters for host_check 
      ArrayList<ASTNode> main_args=new ArrayList();// the arguments to the host_check method
      ArrayList<DeclarationStatement> body_decl=new ArrayList();// declaration of parameters for body_check 
      
      /////////////////////////////////////////////// Encoding of loop to method call
      ContractBuilder cb=new ContractBuilder();

      ContractBuilder cb_main_loop=new ContractBuilder();

      ////create loop guard///////////////////////////////////////////////
      // lower bound of loop
      ASTNode low=loop.getInitBlock(); //get loop low bound
      if (low instanceof BlockStatement){
        low=((BlockStatement)low).getStatement(0);
      }
      String var_name=((DeclarationStatement)low).getName();
      low=((DeclarationStatement)low).getInit();
      // low
      // higher bound of the loop
      ASTNode high=loop.getEntryGuard(); //get loop high bound
      StandardOperator op=((OperatorExpression)high).getOperator();
      high=((OperatorExpression)high).getArg(1);
      // high
      ////create loop guard 
      ASTNode guard=create.expression(StandardOperator.Member,
          create.unresolved_name(var_name),
          create.expression(StandardOperator.RangeSeq,low,high)
      );           
      ////create loop guard///////////////////////////////////////////////
      
      //create (star)conjunction of invariant and append it to cb
      for(ASTNode clause:ASTUtils.conjuncts(c.invariant, StandardOperator.Star)){
        if (NameScanner.occurCheck(clause,var_name)){
          if (clause.getType().isBoolean()){
            cb.appendInvariant(create.forall(
                copy_rw.rewrite(guard),
                copy_rw.rewrite(clause),
                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.appendInvariant(create.forall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
          } else {
            cb.appendInvariant(create.starall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.appendInvariant(create.starall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
          }
        } else {
          cb.appendInvariant(copy_rw.rewrite(clause)); //update new contract
          cb_main_loop.appendInvariant(copy_rw.rewrite(clause)); //update new contract
        }
      }
      //create (star)conjunction of pre_condition and append it to cb
      //Required fix : check for side-effects and free variables
      for(ASTNode clause:ASTUtils.conjuncts(c.pre_condition, StandardOperator.Star)){
          if (NameScanner.occurCheck(clause,var_name)){
            if (clause.getType().isBoolean()){
              cb.requires(create.forall(
                  copy_rw.rewrite(guard),
                  copy_rw.rewrite(clause),
                  create.field_decl(var_name,create.primitive_type(Sort.Integer))));
              
              cb_main_loop.requires(create.forall(
                      copy_rw.rewrite(guard),
                      copy_rw.rewrite(clause),
                      create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            } else if (clause.isa(StandardOperator.Implies)){
                    OperatorExpression i_guard=(OperatorExpression)clause;
                    if(i_guard.getArg(0).isa(StandardOperator.EQ)) //==
                    {     
                      ASTNode lhs=((OperatorExpression)i_guard.getArg(0)).getArg(0);
                      ASTNode rhs=((OperatorExpression)i_guard.getArg(0)).getArg(1);
                      if (lhs.isName(var_name) && !ASTUtils.find_name(rhs,var_name)){
                        Warning("detected 'i==c ==> phi' pattern");
  	                      Hashtable<NameExpression,ASTNode> map=new Hashtable();
  	                      map.put(create.field_name(var_name),rhs);
  	                      Substitution sigma=new Substitution(source(),map);
  	                       
  	                      cb.requires(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
  	                      
  	                      cb_main_loop.requires(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
  	                                           
  	                      vct.util.Configuration.getDiagSyntax().print(System.out,sigma.rewrite(((OperatorExpression)clause).getArg(1)));   	                	                                           
                  	  }
                  	  else {
                  	    // TODO fix control flow to be able to return quantification.
                  	    Fail("unexpect equality");
                  	  }
                    }
                    else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.GT)){ // > what about >= (missing case )
                  	  //create new guard because of implication before the resource expression
                  	  ASTNode new_guard=create.expression(StandardOperator.And,
            	                create.expression(StandardOperator.LT,(((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/ * new lower bound* /,create.unresolved_name(var_name)),
            	                create.expression(op,create.unresolved_name(var_name),high)
            	            );
                        cb.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), / *the resource formula at the right hand of implication * /
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                        
                        cb_main_loop.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), / *the resource formula at the right hand of implication * /
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                    }
                    else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.LT)){
                      //create new guard because of implication before the resource expression
                      ASTNode new_guard=create.expression(StandardOperator.And,
                              create.expression(StandardOperator.LTE,low,create.unresolved_name(var_name)),
                              create.expression(StandardOperator.LT,create.unresolved_name(var_name),
                                  (((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/ * new lower bound* /)
                          );
                        cb.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), / *the other side of implication * /
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                        
                        cb_main_loop.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), / *the other side of implication * /
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                    }
          	  	else // < and >= (missing case) 
          	  		{        	        
          	  		// should be filled up 
          	  		Fail("%s: this form of implies is not supported in requires",((OperatorExpression)clause).getArg(0).getOrigin());
          	  		}
            }
            else  {
            cb.requires(create.starall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.requires(create.starall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
          }
        } else {
          cb.requires(copy_rw.rewrite(clause)); //update new contract

          cb_main_loop.requires(copy_rw.rewrite(clause)); //update new contract
        }
      }
      //Create (star)conjunction of post_condition and append it to cb
      //Required fix : check for side-effects and free variables
      for(ASTNode clause:ASTUtils.conjuncts(c.post_condition, StandardOperator.Star)){
         if (NameScanner.occurCheck(clause,var_name)){
          // check whether clause uses iteration variable.
           if (clause.getType().isBoolean()){ 
             cb.ensures(create.forall(
               copy_rw.rewrite(guard),
               copy_rw.rewrite(clause),
               create.field_decl(var_name,create.primitive_type(Sort.Integer))
             ));
             cb_main_loop.ensures(create.forall(
               copy_rw.rewrite(guard),
               copy_rw.rewrite(clause),
               create.field_decl(var_name,create.primitive_type(Sort.Integer))
             ));
           } else if (clause.isa(StandardOperator.Implies)){
                  OperatorExpression i_guard=(OperatorExpression)clause;
                  if(i_guard.getArg(0).isa(StandardOperator.EQ)) //==
                  {     
                    ASTNode lhs=((OperatorExpression)i_guard.getArg(0)).getArg(0);
                    ASTNode rhs=((OperatorExpression)i_guard.getArg(0)).getArg(1);
                    if (lhs.isName(var_name) && !ASTUtils.find_name(rhs,var_name)){
                      Warning("detected 'i==c ==> phi' pattern");
                        Hashtable<NameExpression,ASTNode> map=new Hashtable();
                        map.put(create.field_name(var_name),rhs);
                        Substitution sigma=new Substitution(source(),map);
                         
                        cb.ensures(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
                        
                        cb_main_loop.ensures(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
                                             
                        vct.util.Configuration.getDiagSyntax().print(System.out,sigma.rewrite(((OperatorExpression)clause).getArg(1))); 
                                                                
                    }
                    else {
                      // TODO fix control flow to be able to return quantification.
                      Fail("unexpect equality");
                    }
                 }
                  else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.GT)){ // > what about >= (missing case )
                    //create new guard because of implication before the resource expression
                    ASTNode new_guard=create.expression(StandardOperator.And,
                            create.expression(StandardOperator.LT,(((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/ * new lower bound* /,create.unresolved_name(var_name)),
                            create.expression(op,create.unresolved_name(var_name),high)
                        );
                      cb.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication * /
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                      
                      cb_main_loop.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication * /
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                  }
                  else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.LT)){
                    //create new guard because of implication before the resource expression
                    ASTNode new_guard=create.expression(StandardOperator.And,
                            create.expression(StandardOperator.LTE,low,create.unresolved_name(var_name)),
                            create.expression(StandardOperator.LT,create.unresolved_name(var_name),
                                (((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/* new lower bound* /)
                        );
                      cb.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication * /
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                      
                      cb_main_loop.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication * /
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                  }
             else // < and >= (missing case) 
        	  		{        	        
        	  		// should be filled up 
        	  		Fail("%s: this form of implies is not supported in ensures",((OperatorExpression)clause).getArg(0).getOrigin());
        	  		}
          } else {
            cb.ensures(create.starall(
                copy_rw.rewrite(guard),
                copy_rw.rewrite(clause),
                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.ensures(create.starall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
          }
        } else {
          cb.ensures(copy_rw.rewrite(clause)); //update new contract

          cb_main_loop.ensures(copy_rw.rewrite(clause)); //update new contract

        }
      }
      // generate arguments and declaration of body (body_decl) and whole loop (main_decl and main_args) 
      for(String var:vars.keySet()){
        System.err.printf("var %s : %s%n", var,vars.get(var));
        body_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
        if (iters.containsKey(var)) continue;
        main_decl.add(create.field_decl(var,copy_rw.rewrite(vars.get(var))));
        main_args.add(create.unresolved_name(var));
      }
      
      Method main_method=create.method_decl(
          create.primitive_type(PrimitiveType.Sort.Void), //return type

          cb_main_loop.getContract(),  //method contract 

          main_name,  //method name
          main_decl.toArray(new DeclarationStatement[0]),
          null);// no body
      
      //Error management  --> line numbers, origins , ...
      BranchOrigin branch=new BranchOrigin("Loop Contract",null);
      OriginWrapper.wrap(null,main_method, branch);
      //Error management  --> line numbers, origins , ...
      
      currentClass.add_dynamic(main_method);
      
      /////////////////////////////////////////////// Encoding of Iteration (loop body)to Method call 
      cb=new ContractBuilder();
      //cb.prependInvariant(guard);
      cb.requires(guard);
      cb.ensures(guard);
      rewrite(c,cb);   //copy c to cb  
      Method main_body=create.method_decl(
          create.primitive_type(PrimitiveType.Sort.Void),
          cb.getContract(), //method contract 
          body_name,
          body_decl.toArray(new DeclarationStatement[0]),
          rewrite(loop.getBody()) // loop body
      );
      //Error management  --> line numbers, origins , ... 
      branch=new BranchOrigin("Iteration Body",null);
      OriginWrapper.wrap(null,main_body, branch);      
      //Error management  --> line numbers, origins , ...
      
      System.out.printf("generated %s at %s%n",main_body.name,main_body.getOrigin());
      currentClass.add_dynamic(main_body);
      ///////////////////////////////////////////////
      
      result=create.invokation(null,null,main_name,main_args.toArray(new ASTNode[0]));
      
      //Error management  --> line numbers, origins , ...
      branch=new BranchOrigin("Parallel Loop",null);
      OriginWrapper.wrap(null,result, branch);
      //Check matching of send and recv.
      check_send_recv(body_decl.toArray(new DeclarationStatement[0]), var_name, guard);
    } else {
      super.visit(loop);
    }
  }

*/
  
  protected void check_send_recv(DeclarationStatement[] body_decl,
      String var_name, ASTNode guard) {
    ContractBuilder cb;
    BranchOrigin branch;
    for(String R:send_recv_map.keySet()){
      SendRecvInfo recv_entry=send_recv_map.get(R);
      if (recv_entry.stat.isa(StandardOperator.Recv)){
        OperatorExpression recv=(OperatorExpression)recv_entry.stat;
        String S=((NameExpression)recv.getArg(1)).getName();
        SendRecvInfo send_entry=send_recv_map.get(S);
        if (send_entry==null || !send_entry.stat.isa(StandardOperator.Send)){
          Fail("unmatched recv");
        }
        OperatorExpression send=(OperatorExpression)send_entry.stat;
        if (!R.equals(((NameExpression)send.getArg(1)).getName())){
          Fail("wrong label in send");
        }
        int dr=getConstant(recv.getArg(2));
        int ds=getConstant(send.getArg(2));
        if (dr!=ds){
          Fail("distances of send(%d) and recv(%d) are different",ds,dr);
        }
        // create shift substitution.
        HashMap<NameExpression,ASTNode> shift_map=new HashMap();
        NameExpression name=create.argument_name(var_name);
        shift_map.put(name,create.expression(StandardOperator.Minus,name,create.constant(dr)));
        Substitution shift=new Substitution(null,shift_map);
        // create guard check.
        cb=new ContractBuilder();
        cb.requires(guard);
        for(ASTNode g:recv_entry.guards){
          cb.requires(g);
        }
        cb.ensures(create.expression(StandardOperator.LTE,
            create.constant(dr),create.argument_name(var_name)
        ));
        for(ASTNode g:send_entry.guards){
          cb.ensures(shift.rewrite(g));
        }
        Method guard_method=create.method_decl(
            create.primitive_type(PrimitiveType.Sort.Void),
            cb.getContract(),
            String.format("guard_check_%s_%s",S,R),
            body_decl,
            create.block()
        );
        branch=new BranchOrigin("Guard Check",null);
        OriginWrapper.wrap(null,guard_method, branch);
        currentTargetClass.add_dynamic(guard_method);
        //create resource check
        cb=new ContractBuilder();
        cb.requires(guard);
        // lower bound is already guaranteed by guard check.
        //cb.requires(create.expression(StandardOperator.LTE,
        //    create.constant(dr),create.argument_name(var_name)
        //));
        for(ASTNode g:send_entry.guards){
          cb.requires(shift.rewrite(g));
        }
        for(ASTNode g:recv_entry.guards){
          cb.requires(g);
        }
        cb.requires(shift.rewrite(send.getArg(0)));
        for(ASTNode g:send_entry.guards){
          cb.ensures(shift.rewrite(g));
        }
        cb.ensures(copy_rw.rewrite(recv.getArg(0)));
        Method resource_method=create.method_decl(
            create.primitive_type(PrimitiveType.Sort.Void),
            cb.getContract(),
            String.format("resource_check_%s_%s",S,R),
            body_decl,
            create.block()
        );
        branch=new BranchOrigin("Resource Check",null);
        OriginWrapper.wrap(null,resource_method, branch);
        currentTargetClass.add_dynamic(resource_method);

      }
      // unmatched send statements are wasteful, but not incorrect. 
    }
    send_recv_map.clear();
  }
  
  private int getConstant(ASTNode arg) {
    IntegerValue v=(IntegerValue)((ConstantExpression)arg).value;
    return v.value;
  }

  @Override
  public void visit(IfStatement s) {
    IfStatement res=new IfStatement();
    res.setOrigin(s.getOrigin());
    int N=s.getCount();
    for(int i=0;i<N;i++){
      ASTNode guard=s.getGuard(i);
      if (guard!=IfStatement.else_guard) guard=guard.apply(this);
      Debug("pushing guard");
      guard_stack.push(guard);
      ASTNode body=s.getStatement(i);
      body=body.apply(this);
      Debug("popping guard");
      guard_stack.pop();
      res.addClause(guard,body);
    }
    result=res; return ;
  }

}
