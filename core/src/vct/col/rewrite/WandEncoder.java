package vct.col.rewrite;

import hre.ast.MessageOrigin;
import hre.config.StringSetting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.ASTSpecial;
import vct.col.ast.BlockStatement;
import vct.col.ast.ClassType;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.IfStatement;
import vct.col.ast.Lemma;
import vct.col.ast.LoopStatement;
import vct.col.ast.Method;
import vct.col.ast.MethodInvokation;
import vct.col.ast.NameExpression;
import vct.col.ast.OperatorExpression;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.util.ASTFactory;
import vct.col.util.ASTUtils;
import vct.col.util.NameScanner;
import vct.col.util.WandScanner;
import static vct.col.ast.ASTReserved.*;

public class WandEncoder extends AbstractRewriter {

  public static final String VALID = "valid_wand";

  public static StringSetting apply_name=new StringSetting("_apply");
  
  private class WandDefinition {
    ASTClass cl;
    ASTNode valid_body;
    IfStatement apply_cases;
    int case_count;
  }
  private Hashtable<String,WandDefinition> defined_wand_classes=new Hashtable<String,WandDefinition>();
  
	public WandEncoder(ProgramUnit source) {
		super(source);
	}
	  public void visit(OperatorExpression e){
		  	
		    switch (e.getOperator()){
		    case Witness:{
		      ASTNode arg1=e.getArg(0);
		      if (arg1.labels()!=1){
		        Fail("Witness must have precisely one label.");
		      }
		      String lbl=arg1.getLabel(0).getName();
		      if (arg1.isa(StandardOperator.Wand)){
		        // instantiate magic wand witnesses only
		        Type t=create.class_type(get_wand_type((OperatorExpression)arg1));
            result=create.field_decl(lbl, t);
		      } else {
		        super.visit(e);
		      }
		      break;
		    }
		    case Apply:{
		      ASTNode arg1=e.getArg(0);
		      if (arg1.labels()==1){
		        for(NameExpression lbl:arg1.getLabels()){
		          MethodInvokation res=create.invokation(create.local_name(lbl.getName()), null, apply_name.get());
		          res.set_before(copy_rw.rewrite(e.get_before()));
		          res.set_after(copy_rw.rewrite(e.get_after()));
		          result=res;
		          return;
		        }
		        Warning("weird %s expression",e.getOperator());
		      } else {
		        Abort("bad apply");
		      }
		      break;
		    }
		    case Wand:{
		    	if (e.labels()!=1){
		    		Abort("badly labeled magic wand");
		    	}
		    	String lbl=e.getLabel(0).getName();
		    	String type_name="Wand";
		    	ASTNode res=create.expression(StandardOperator.NEQ,
		    					create.local_name(lbl),create.reserved_name(Null));
		    	ASTNode tmp=create.invokation(create.local_name(lbl), null, VALID);
		    	res=create.expression(StandardOperator.Star,res,tmp);
		    	int count=0;
		    	for(ASTNode n:ASTUtils.conjuncts(e.getArg(0),StandardOperator.Star)){
		    		count++;
		    		if (n instanceof MethodInvokation){
		    			MethodInvokation m=(MethodInvokation)n;
		    			type_name+="_"+m.method;
			    		tmp=create.invokation(create.local_name(lbl), null, "get_in_"+count);
			    		tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.object));
			    		res=create.expression(StandardOperator.Star,res,tmp);
			        Method m_def=m.getDefinition();
			        if (m_def==null){
			          Abort("applied method is is undefined");
			        }
			        int N=m_def.getArity();
			        for (int i=0;i<N;i++){
	              tmp=create.invokation(create.local_name(lbl), null, "get_in_"+count+"_"+i);
	              tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.getArg(i)));
	              res=create.expression(StandardOperator.Star,res,tmp);
		          }
		    		} else {
		    			Abort("unexpected clause in magic wand");
		    		}
		    	}
		    	count=0;
    			type_name+="_for";
		    	for(ASTNode n:ASTUtils.conjuncts(e.getArg(1),StandardOperator.Star)){
		    		count++;
		    		if (n instanceof MethodInvokation){
		    			MethodInvokation m=(MethodInvokation)n;
		    			type_name+="_"+m.method;
			    		tmp=create.invokation(create.local_name(lbl), null, "get_out_"+count);
			    		tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.object));
			    		res=create.expression(StandardOperator.Star,res,tmp);
              Method m_def=m.getDefinition();
              if (m_def==null){
                Abort("applied method is is undefined");
              }
              int N=m_def.getArity();
              for (int i=0;i<N;i++){
                tmp=create.invokation(create.local_name(lbl), null, "get_out_"+count+"_"+i);
                tmp=create.expression(StandardOperator.EQ,tmp,rewrite(m.getArg(i)));
                res=create.expression(StandardOperator.Star,res,tmp);
              }
		    		} else {
		    			Abort("unexpected clause in magic wand");
		    		}
		    	}
		    	if (!defined_wand_classes.containsKey(type_name)){
		    	  define_wand(type_name,e);
		    	}
		    	if (in_requires){
		    		currentContractBuilder.given(create.field_decl(lbl,create.class_type(type_name)));
		    	}
		    	if (in_ensures){
		    		currentContractBuilder.yields(create.field_decl(lbl,create.class_type(type_name)));
		    	}
		    	auto_labels=false;
		    	result=res;
		    	return;
		    }
		    default:
		      super.visit(e);
		    }
    }
	  
	public void define_wand(String name,OperatorExpression e){
	  WandDefinition def=new WandDefinition();
	  defined_wand_classes.put(name,def);
	  create.enter();
	  create.setOrigin(new MessageOrigin("generated class "+name));
	  ASTClass cl=create.ast_class(name,ASTClass.ClassKind.Plain,null,null,null);
	  def.cl=cl;
	      
	  cl.add_dynamic(create.field_decl("lemma",create.primitive_type(Sort.Integer)));
	  ArrayList<ASTNode> valid_list=new ArrayList();
	  valid_list.add(create.expression(StandardOperator.Value,create.field_name("lemma")));
	  valid_list.add(create.expression(StandardOperator.LTE,create.constant(1),create.field_name("lemma")));
	  ContractBuilder cb=new ContractBuilder();
	  cb.requires(create.invokation(create.reserved_name(This), null, VALID));
	  ASTNode get_perms=create.invokation(create.reserved_name(This), null, VALID);
	  Contract get_contract=cb.getContract();
	  cb.ensures(create.expression(StandardOperator.NEQ,
	      create.reserved_name(Result),create.reserved_name(Null)));
	  Contract get_contract_non_null=cb.getContract();
	  
	  // now we build the contract of the apply method.
	  cb=new ContractBuilder();
	  cb.requires(create.invokation(create.reserved_name(This), null, VALID));
	  
    int count=0;
    for(ASTNode n:ASTUtils.conjuncts(e.getArg(0),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        String var="in_"+count;
        Type t=m.object.getType();
        if (t.getOrigin()==null){
          t.setOrigin(cl);
        }
        add_field_and_getter(cl, valid_list, get_contract_non_null, get_perms, var, t,true);
        //cb.requires(create.non_null(create.invokation(null,null,"get_"+var)));
        Method m_def=m.getDefinition();
        if (m_def==null){
          Abort("applied method is is undefined");
        }
        int N=m_def.getArity();
        ASTNode args[]=new ASTNode[N];
        for (int i=0;i<N;i++){
          Type tt=m_def.getArgType(i);
          add_field_and_getter(cl, valid_list, get_contract, get_perms, var+"_"+i, tt,false);
          //if (tt instanceof ClassType) cb.requires(create.non_null(create.invokation(null,null,"get_"+var+"_"+i)));
          args[i]=create.invokation(null,null,"get_"+var+"_"+i);
        }
        ASTNode tmp=create.invokation(create.invokation(null,null,"get_"+var),null,m.method,args);
        for (NameExpression l:m.getLabels()){
          tmp.addLabel(copy_rw.rewrite(l));
        }
        cb.requires(tmp);
      } else {
        Abort("unexpected clause in magic wand");
      }
    }
    count=0;
    for(ASTNode n:ASTUtils.conjuncts(e.getArg(1),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        String var="out_"+count;
        Type t=m.object.getType();
        if (t.getOrigin()==null){
          t.setOrigin(cl);
        }
        add_field_and_getter(cl, valid_list, get_contract_non_null, get_perms, var, t,true);
        //??
        cb.requires(create.non_null(create.invokation(null,null,"get_"+var)));
        Method m_def=m.getDefinition();
        if (m_def==null){
          Abort("applied method is is undefined");
        }
        int N=m_def.getArity();
        ASTNode args[]=new ASTNode[N];
        for (int i=0;i<N;i++){
          Type tt=m_def.getArgType(i);
          add_field_and_getter(cl, valid_list, get_contract, get_perms, var+"_"+i, tt,false);
          //if (tt instanceof ClassType) cb.requires(create.non_null(create.invokation(null,null,"get_"+var+"_"+i)));
          args[i]=create.expression(StandardOperator.Old,create.invokation(null,null,"get_"+var+"_"+i));
        }
        ASTNode tmp=create.invokation(
            create.expression(StandardOperator.Old,create.invokation(null,null,"get_"+var)),
            null,
            m.method,
            args
        );
        for (NameExpression l:m.getLabels()){
          tmp.addLabel(copy_rw.rewrite(l));
        }
        cb.ensures(tmp);
      } else {
        Abort("unexpected clause in magic wand");
      }
    }    
    def.valid_body=create.fold(StandardOperator.Star,valid_list);
    IfStatement cases=new IfStatement();
    cases.setOrigin(create.getOrigin());
    ASTNode apply_body=create.block(
        create.expression(StandardOperator.Unfold,
            create.invokation(create.reserved_name(This), null, VALID)
        ), cases
    );
    Method apply=create.method_decl(create.primitive_type(Sort.Void),
        cb.getContract(),apply_name.get(),new DeclarationStatement[0],apply_body);
    cl.add_dynamic(apply);
    def.apply_cases=cases;
	  target().add(cl);
	  create.leave();
	}
  private void add_field_and_getter(ASTClass cl, ArrayList<ASTNode> valid_list,
      Contract get_contract, ASTNode get_perms, String var, Type t, boolean non_null) {
    ASTNode decl=create.field_decl(var,rewrite(t));
    cl.add_dynamic(decl);
    valid_list.add(create.expression(StandardOperator.Value,create.field_name(var)));
    if (non_null) valid_list.add(create.non_null(create.field_name(var)));
    ASTNode body=create.field_name(var);
    Method getter=create.function_decl(t,get_contract, "get_"+var, new DeclarationStatement[0],
        create.expression(StandardOperator.Unfolding,get_perms,body));
    cl.add_dynamic(getter);
  }
	
	public void visit(Lemma l){
	  Hashtable<String,Type> vars=new Hashtable<String,Type>();
	  l.accept(new NameScanner(vars));
	  int N=l.block.getLength();
	  OperatorExpression wand=(OperatorExpression)((OperatorExpression)l.block.getStatement(N-1)).getArg(0);
	  String wand_type=get_wand_type(wand);
	  String wand_name=wand.getLabel(0).getName();
	  WandDefinition def=defined_wand_classes.get(wand_type);
	  def.case_count++;
	  int lemma_no=def.case_count;
	  
      HashMap<NameExpression,ASTNode> local2proof=new HashMap();
	  ContractBuilder lemma_cb=new ContractBuilder();
	  BlockStatement lemma_body=create.block();
	  BlockStatement proof_body=create.block();
	  ASTNode proof_result=create.constant(true);
	  ArrayList<DeclarationStatement> lemma_args=new ArrayList();
	  ArrayList<ASTNode> create_args=new ArrayList();
	  ArrayList<ASTNode> case_body=new ArrayList();
	  
	  lemma_body.add_statement(create.field_decl("wand",create.class_type(wand_type),
	      create.new_object(create.class_type(wand_type)))
	  );
	  lemma_body.add_statement(create.assignment(
	      create.dereference(create.local_name("wand"),"lemma"),
	      create.constant(lemma_no))
	  );
    lemma_cb.ensures(create.expression(StandardOperator.NEQ,
        create.reserved_name(Result),
        create.reserved_name(Null)
    ));
    lemma_cb.ensures(create.invokation(create.reserved_name(Result), null, VALID));
    
    Type this_type=create.class_type(current_class().getFullName());
    String this_name="this_"+lemma_no;
    def.cl.add_dynamic(create.field_decl(this_name,this_type));
    def.valid_body=create.expression(StandardOperator.Star,
			def.valid_body,
			create.expression(StandardOperator.Value,create.field_name(this_name))
		);
    lemma_args.add(create.field_decl(this_name,this_type));
    lemma_body.add_statement(create.assignment(
            create.dereference(create.local_name("wand"),this_name),
            create.local_name(this_name)
        ));
    create_args.add(create.reserved_name(This));
    case_body.add(create.expression(StandardOperator.NEQ,
            create.field_name(this_name),
            create.reserved_name(Null))
	  );
    lemma_cb.requires(create.expression(StandardOperator.NEQ,
            create.local_name(this_name),
            create.reserved_name(Null)
	));
    local2proof.put(create.reserved_name(This),create.unresolved_name(this_name));
    AbstractRewriter rename_for_proof=new Substitution(source(), local2proof);
    
    for(String name:vars.keySet()){
      Debug("accessing %s : %s",name,vars.get(name));
      DeclarationStatement arg=create.field_decl(name,vars.get(name));
      String var=arg.getName()+"_"+lemma_no;
      add_access(def, local2proof, lemma_body, lemma_args, create_args, arg, var);
    }
    for(int i=0;i<N-1;i++){
    	ASTNode tmp=l.block.getStatement(i);
    	create(tmp);
    	if (tmp instanceof OperatorExpression){
    		OperatorExpression e=(OperatorExpression)tmp;
    		switch(e.getOperator()){
	    		case Apply:{
	    		  String label=e.getArg(0).getLabel(0).getName()+"_"+lemma_no;
	    		  proof_body.add_statement(create.invokation(create.field_name(label), null , apply_name.get()));
	    		  // If a magic wand is applied, it is also used, so we continue with the use body.
	    		}
	    		case Use:{
	    		  ASTNode temp=e.getArg(0);
	    		  if (temp instanceof OperatorExpression){
	    		    OperatorExpression ee=(OperatorExpression)temp;
	    		    if (ee.getOperator()==StandardOperator.Wand){
	    		      String label=ee.getLabel(0).getName();
	    		      DeclarationStatement arg=create.field_decl(label,create.class_type(get_wand_type(ee)));
	    		      String var=arg.getName()+"_"+lemma_no;
	    		      add_access(def, local2proof, lemma_body, lemma_args, create_args, arg, var);
	    		    }
	    		  }
	    		  temp=rewrite(temp);
	    			lemma_cb.requires(rename_for_proof.rewrite(temp));
	    			case_body.add(rename_for_proof.rewrite(temp));	    			
					continue;
	    		}
	    		case Access:{
	    		  Fail("access keyword no longer supported.");
	    			continue;
	    		}
    		}
    	}
    	proof_body.add_statement(rename_for_proof.rewrite(tmp));
    }
    create.enter();
    proof_body.add_statement(create(l.block).return_statement());
    create.leave();
    
	  int count=0;
    for(ASTNode n:ASTUtils.conjuncts(wand.getArg(0),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        String var="in_"+count;
        Type t=m.object.getType();
        if (t.getOrigin()==null){
          t.setOrigin(l);
        }
        define_link(lemma_cb, lemma_body, lemma_args, create_args, case_body,
            rename_for_proof, m.object, var, t);
        Method m_def=m.getDefinition();
        if (m_def==null){
          Abort("applied method is is undefined");
        }
        int N1=m_def.getArity();
        for (int i=0;i<N1;i++){
          Type tt=m_def.getArgType(i);
          define_link(lemma_cb, lemma_body, lemma_args, create_args, case_body,
              rename_for_proof, m.getArg(i) , var+"_"+i, tt);
        }
      } else {
        Abort("unexpected clause in magic wand");
      }
    }
    count=0;
    for(ASTNode n:ASTUtils.conjuncts(wand.getArg(1),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        String var="out_"+count;
        Type t=m.object.getType();
        if (t.getOrigin()==null){
          t.setOrigin(l);
        }
        define_link(lemma_cb, lemma_body, lemma_args, create_args, case_body,
            rename_for_proof, m.object, var, t);
        Method m_def=m.getDefinition();
        if (m_def==null){
          Abort("applied method is is undefined");
        }
        int N1=m_def.getArity();
        ASTNode args[]=new ASTNode[N1];
        for (int i=0;i<N1;i++){
          Type tt=m_def.getArgType(i);
          define_link(lemma_cb, lemma_body, lemma_args, create_args, case_body,
              rename_for_proof, m.getArg(i) , var+"_"+i, tt);
          args[i]=create.field_name(var+"_"+i);
        }
        ASTNode call=create.invokation(create.field_name(var),null,m.method,args);
        for(NameExpression name:n.getLabels()){
          call.addLabel(copy_rw.rewrite(name));
        }
        proof_result=create.expression(StandardOperator.Star,proof_result,call);
      } else {
        Abort("unexpected clause in magic wand");
      }
    }
 
	  lemma_body.add_statement(create.expression(StandardOperator.Fold,
        create.invokation(create.local_name("wand"), null, VALID)));
	  lemma_body.add_statement(create.return_statement(create.local_name("wand")));
	  // The following assert is not needed for correctness.
	  // However, it is essential for providing an error message at the correct lines!
	  create.enter();
	  create.setOrigin(l.block.getStatement(N-1).getOrigin());
	  //FIXME: rewrite assertions properly!
	  //proof_body.add_statement(create.expression(StandardOperator.Assert,proof_result));
	  //proof_body.add_statement(create.special(ASTSpecial.Kind.Assert, proof_result));
	  create.leave();
	  
	  String lemma_name=wand_type+"_lemma_"+lemma_no;
	  Method lemma_method=create.method_decl(
	      create.class_type(wand_type),
	      lemma_cb.getContract(),
	      lemma_name,
	      lemma_args.toArray(new DeclarationStatement[0]),
	      lemma_body);
	  currentTargetClass.add_dynamic(lemma_method);
	  def.valid_body=create.expression(StandardOperator.Star,
				def.valid_body,
				create.expression(StandardOperator.Implies,
						create.expression(StandardOperator.EQ,create.field_name("lemma"),create.constant(lemma_no)),
						create.fold(StandardOperator.Star,case_body)
				)
	  );
	  def.apply_cases.addClause(
	      create.expression(StandardOperator.EQ,create.field_name("lemma"),create.constant(lemma_no)),
	      proof_body);
	  result=create.assignment(create.local_name(wand_name),
	      create.invokation(null,null,lemma_name,create_args.toArray(new ASTNode[0])));
	}
  private void define_link(ContractBuilder lemma_cb, BlockStatement lemma_body,
      ArrayList<DeclarationStatement> lemma_args,
      ArrayList<ASTNode> create_args, ArrayList<ASTNode> case_body,
      AbstractRewriter rename_for_proof, ASTNode object, String var, Type t) {
    DeclarationStatement decl=create.field_decl(var,rewrite(t));
    lemma_args.add(decl);
    lemma_body.add_statement(create.assignment(
        create.dereference(create.local_name("wand"),var),
        create.local_name(var)
    ));
    if (t instanceof ClassType) lemma_cb.requires(create.expression(StandardOperator.NEQ,
        create.local_name(var),
        create.reserved_name(Null)
    ));
    lemma_cb.ensures(create.expression(StandardOperator.EQ,
        create.invokation(create.reserved_name(Result),null, "get_"+var),
        create.local_name(var)
    ));
    create_args.add(rewrite(object));
    case_body.add(
    create.expression(StandardOperator.EQ,create.field_name(var),rename_for_proof.rewrite(object))
    );
    lemma_cb.requires(
    create.expression(StandardOperator.EQ,create.local_name(var),rename_for_proof.rewrite(object))
    );
  }
  private void add_access(WandDefinition def,
      HashMap<NameExpression, ASTNode> local2proof, BlockStatement lemma_body,
      ArrayList<DeclarationStatement> lemma_args,
      ArrayList<ASTNode> create_args, DeclarationStatement arg, String var) {
    DeclarationStatement decl=create.field_decl(var, rewrite(arg.getType()));
    def.cl.add_dynamic(decl);
    lemma_args.add(decl);
    lemma_body.add_statement(create.assignment(
              create.dereference(create.local_name("wand"),var),
              create.local_name(var)	    					
    ));
    create_args.add(create.unresolved_name(arg.getName()));
    local2proof.put(create.unresolved_name(arg.getName()),create.unresolved_name(var));
    def.valid_body=create.expression(StandardOperator.Star,
    	def.valid_body,
    	create.expression(StandardOperator.Value,create.field_name(var))
    );
  }
	
	private String get_wand_type(OperatorExpression e){
    String type_name="Wand";
    int count=0;
    for(ASTNode n:ASTUtils.conjuncts(e.getArg(0),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        type_name+="_"+m.method;
      } else {
        Abort("unexpected clause in magic wand");
      }
    }
    count=0;
    type_name+="_for";
    for(ASTNode n:ASTUtils.conjuncts(e.getArg(1),StandardOperator.Star)){
      count++;
      if (n instanceof MethodInvokation){
        MethodInvokation m=(MethodInvokation)n;
        type_name+="_"+m.method;
      } else {
        Abort("unexpected clause in magic wand");
      }
    }
    return type_name;
	}
	
	
	@Override
	public ProgramUnit rewriteAll(){
	  ProgramUnit res=super.rewriteAll();
	  for(WandDefinition def:defined_wand_classes.values()){
	    create.enter();
	    create. setOrigin(def.cl.getOrigin());
	    def.valid_body=create.expression(StandardOperator.Star,
	        def.valid_body,
	        create.expression(StandardOperator.LTE,create.field_name("lemma"),create.constant(def.case_count))
	    );
      Method valid=create.predicate(VALID,def.valid_body);
      def.cl.add_dynamic(valid);
      create.addZeroConstructor(def.cl);
      create.leave();
	  }
	  return res;
	}
	
	@Override
	public void visit(LoopStatement l){
	  for(ASTNode inv:l.getInvariants()){
	    if (inv instanceof OperatorExpression && ((OperatorExpression)inv).getOperator()==StandardOperator.Wand){
	      String label=inv.getLabel(0).getName();
	      currentBlock.add_statement(create.field_decl(label,create.class_type(get_wand_type((OperatorExpression)inv))));
	    }
	  }
	  super.visit(l);
	}
}
