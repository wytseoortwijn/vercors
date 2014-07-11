package vct.col.rewrite;

import hre.ast.BranchOrigin;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.concurrent.atomic.AtomicInteger;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.BindingExpression.Binder;
import vct.col.ast.BlockStatement;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.ast.VariableDeclaration;
import vct.col.util.ASTUtils;
import vct.col.util.NameScanner;
import vct.col.util.OriginWrapper;

public class IterationContractEncoder extends AbstractRewriter {

  private AtomicInteger counter=new AtomicInteger();
    
  public IterationContractEncoder(ProgramUnit arg) {
    super(arg);
  }
//
  public void visit(OperatorExpression e)
  { //DRB

	  int N=counter.incrementAndGet();	  
	  ContractBuilder cb = new ContractBuilder();
	  Hashtable<String,Type> vars=new Hashtable<String,Type>();
	  BranchOrigin branch;
	  
	  switch(e.getOperator())
	  {
	  case Send:
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
	      
	      //System.out.printf("\n generated %s at %s%n \n",send_body.name,send_body.getOrigin());

	      currentClass.add_dynamic(send_body);
	      
	      result=create.invokation(null,null,send_name,send_args.toArray(new ASTNode[0]));
	      
		  break;
	  case Recv:
		  // create method contract
		  //and call the method
		  vct.util.Configuration.getDiagSyntax().print(System.out,e.getArg(0));//DRB		        		  		  
		  
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

	      currentClass.add_dynamic(recv_body);
	      
	      result=create.invokation(null,null,recv_name,recv_args.toArray(new ASTNode[0]));
	      		  
		  break;
	  default:
		  super.visit(e);
			  
	  }
  }
  public void visit(LoopStatement s){
	  
    Contract c=s.getContract(); 
    
    if (c!=null && (c.pre_condition != c.default_true || c.post_condition != c.default_true)){
      Warning("processing iteration contract");
      Hashtable<String,Type> vars=new Hashtable<String,Type>();
      s.getBody().accept(new NameScanner(vars));
      c.accept(new NameScanner(vars));
      s.getEntryGuard().accept(new NameScanner(vars));
      Hashtable<String,Type> iters=new Hashtable<String,Type>();
      s.getUpdateBlock().accept(new NameScanner(iters));
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
      ASTNode low=s.getInitBlock(); //get loop low bound
      if (low instanceof BlockStatement){
        low=((BlockStatement)low).getStatement(0);
      }
      String var_name=((DeclarationStatement)low).getName();
      low=((DeclarationStatement)low).getInit();
      // low
      // higher bound of the loop
      ASTNode high=s.getEntryGuard(); //get loop high bound
      StandardOperator op=((OperatorExpression)high).getOperator();
      high=((OperatorExpression)high).getArg(1);
      // high
      ////create loop guard 
      ASTNode guard=create.expression(StandardOperator.And,
          create.expression(StandardOperator.LTE,low,create.unresolved_name(var_name)),
          create.expression(op,create.unresolved_name(var_name),high)
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
    	  // same support of implication for precodition also required     	  
        if (NameScanner.occurCheck(clause,var_name)){
            if (clause.isa(StandardOperator.Implies)){
          	  //Fail("this form of implies is not supported");        	  
          	  if (clause.getType().isBoolean()){  
          		  Fail("this form of implies is not supported -- boolean experssions");
                  } else {                                	                  	         	            	                       
                    if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.EQ)) //==
                    {      
                  	  boolean IsArr = false;
                  	  if(IsArr){                	  
  	                      Hashtable<NameExpression,ASTNode> map=new Hashtable();
  	                      map.put((NameExpression)((OperatorExpression)(
  	                    		  ((OperatorExpression)((OperatorExpression)clause).getArg(1)).getArg(0))).getArg(1)/*i*/,
  	                    		  (((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/*len-1*/);
  	                      
  	                      Substitution sigma=new Substitution(source(),map);
  	                      
  	                      cb.requires(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
  	                      
  	                      cb_main_loop.requires(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
  	                                           
  	                      vct.util.Configuration.getDiagSyntax().print(System.out,sigma.rewrite(((OperatorExpression)clause).getArg(1))); 
  	                	  System.out.printf("\nAssssssssssssssssssssss \n ");                                          
                  	  }
                  	  else {//IsArr == false 
                  		  cb.requires(clause);
                  		  cb_main_loop.requires(((OperatorExpression)clause).getArg(1));
                  	  }
                    }
                    else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.GT)){ // > what about >= (missing case )
                  	  //create new guard because of implication before the resource expression
                  	  ASTNode new_guard=create.expression(StandardOperator.And,
            	                create.expression(StandardOperator.LT,(((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/* new lower bound*/,create.unresolved_name(var_name)),
            	                create.expression(op,create.unresolved_name(var_name),high)
            	            );
                        cb.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication */
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                        
                        cb_main_loop.requires(create.starall(
                                copy_rw.rewrite(new_guard),
                                copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication */
                                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                    }
          	  	else // < and >= (missing case) 
          	  		{        	        
          	  		// should be filled up 
          	  		Fail("this form of implies is not supported -- greater than");
          	  		}
                  }
            }
            else  if (clause.getType().isBoolean()){
            cb.requires(create.forall(
                copy_rw.rewrite(guard),
                copy_rw.rewrite(clause),
                create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.requires(create.forall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
          } else {
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
        if (NameScanner.occurCheck(clause,var_name)){//check whether clause is in the list of free variables or not.
          if (clause.isa(StandardOperator.Implies)){
        	  //Fail("this form of implies is not supported");        	  
        	  if (clause.getType().isBoolean()){  
        		  Fail("this form of implies is not supported -- boolean experssions");
                } else {                                	                  	         	            	                       
                  if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.EQ)) //==
                  {      
                	  boolean IsArr = false;
                	  if(IsArr){                	  
	                      Hashtable<NameExpression,ASTNode> map=new Hashtable();
	                      map.put((NameExpression)((OperatorExpression)(
	                    		  ((OperatorExpression)((OperatorExpression)clause).getArg(1)).getArg(0))).getArg(1)/*i*/,
	                    		  (((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/*len-1*/);
	                      
	                      Substitution sigma=new Substitution(source(),map);
	                      
	                      cb.ensures(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
	                      
	                      cb_main_loop.ensures(sigma.rewrite(((OperatorExpression)clause).getArg(1)));
	                                           
	                      vct.util.Configuration.getDiagSyntax().print(System.out,sigma.rewrite(((OperatorExpression)clause).getArg(1))); 
	                	  System.out.printf("\nAssssssssssssssssssssss \n ");                                          
                	  }
                	  else { //IsArr == false 
                		  cb.ensures(clause);
                		  cb_main_loop.ensures(((OperatorExpression)clause).getArg(1));
                	  }
                  }
                  else if(((OperatorExpression)clause).getArg(0).isa(StandardOperator.GT)){ // > what about >= (missing case )
                	  //create new guard because of implication before the resource expression
                	  ASTNode new_guard=create.expression(StandardOperator.And,
          	                create.expression(StandardOperator.LT,(((OperatorExpression)((OperatorExpression)clause).getArg(0)).getArg(1))/* new lower bound*/,create.unresolved_name(var_name)),
          	                create.expression(op,create.unresolved_name(var_name),high)
          	            );
                      cb.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication */
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));                        
                      
                      cb_main_loop.ensures(create.starall(
                              copy_rw.rewrite(new_guard),
                              copy_rw.rewrite(((OperatorExpression)clause).getArg(1)), /*the other side of implication */
                              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
                  }
        	  	else // < and >= (missing case) 
        	  		{        	        
        	  		// should be filled up 
        	  		Fail("this form of implies is not supported -- greater than");
        	  		}
                }
          } else if (clause.getType().isBoolean()){ //binder method can be used for refactoring of starall and forall 

            cb.ensures(create.forall(
              copy_rw.rewrite(guard),
              copy_rw.rewrite(clause),
              create.field_decl(var_name,create.primitive_type(Sort.Integer))));
            
            cb_main_loop.ensures(create.forall(
                    copy_rw.rewrite(guard),
                    copy_rw.rewrite(clause),
                    create.field_decl(var_name,create.primitive_type(Sort.Integer))));
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
          rewrite(s.getBody()) // loop body
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
      //Error management  --> line numbers, origins , ...
      
    } else {
      super.visit(s);
    }
  }
  
}
