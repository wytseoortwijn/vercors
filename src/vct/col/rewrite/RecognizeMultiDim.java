package vct.col.rewrite;

import hre.lang.Ref;

import java.util.ArrayList;
import java.util.HashMap;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;

public class RecognizeMultiDim extends AbstractRewriter {

  public RecognizeMultiDim(ProgramUnit source) {
    super(source);
  }

  private static Type get_basetype(Type t){
    while(t.isPrimitive(Sort.Array)){
      PrimitiveType tt=(PrimitiveType)t;
      t=(Type)tt.getArg(0);
    }
    return t;
  }

  private static ASTNode[] get_dimensions(Type t){
    ArrayList<ASTNode> list=new ArrayList();
    while(t.isPrimitive(Sort.Array)){
      PrimitiveType tt=(PrimitiveType)t;
      if (tt.getArgCount()==2){
        list.add(tt.getArg(1));
        t=(Type)tt.getArg(0);
      } else {
        // dimension unknown.
        return null;
      }
    }
    if (list.size()>0){ 
      return list.toArray(new ASTNode[0]);
    } else {
      return null;
    }
  }
  
  private HashMap<String,ASTNode[]> dimension=new HashMap();
  
  @Override
  public void visit(Method m){
    String name=m.getName();
    int N=m.getArity();
    if (currentContractBuilder==null) currentContractBuilder=new ContractBuilder();
    DeclarationStatement args[]=new DeclarationStatement[N];
    for(int i=0;i<N;i++){
      String arg=m.getArgument(i);
      Type t=m.getArgType(i);
      ASTNode dims[]=get_dimensions(t);
      if (dims!=null){
        Debug("Looks like %s is a multi-dimensional array",arg);
        args[i]=create.field_decl(arg,create.primitive_type(
            Sort.Array,
            rewrite(get_basetype(t)),
            create.fold(StandardOperator.Mult,dims)
        ));
        dimension.put(arg,dims);
      } else {
        args[i]=create.field_decl(arg,rewrite(t));
      }
    }
    Contract mc=m.getContract();
    if (mc!=null){
      rewrite(mc,currentContractBuilder);
    }
    Method.Kind kind=m.kind;
    Type rt=rewrite(m.getReturnType());
    Contract c=currentContractBuilder.getContract();
    currentContractBuilder=null;
    ASTNode body=rewrite(m.getBody());
    dimension.clear();
    result=create.method_kind(kind, rt, c, name, args, m.usesVarArgs(), body);
  }

  @Override
  public void visit(OperatorExpression e){
    if (e.isa(StandardOperator.Subscript)){
      ArrayList<ASTNode> args=new ArrayList();
      ASTNode tmp=try_multidim(e,args);
      if(tmp!=null){
        result=tmp;
        return;
      }
    }
    super.visit(e);
  }

  private ASTNode try_multidim(ASTNode node, ArrayList<ASTNode> args) {
    if (node.isa(StandardOperator.Subscript)){
      OperatorExpression e=(OperatorExpression)node;
      args.add(rewrite(e.getArg(1)));
      return try_multidim(e.getArg(0),args);
    }
    if (node instanceof NameExpression){
      NameExpression n=(NameExpression)node;
      String name=n.getName();
      ASTNode dims[]=dimension.get(name);
      if(dims==null) return null;
      if(dims.length!=args.size()) return null;
      int i=dims.length-1;
      ASTNode idx=args.get(i);
      if (idx.isReserved(ASTReserved.Any)){
        while(i>0){
          i--;
          if (!args.get(i).isReserved(ASTReserved.Any)) return null;
        }
      } else {
        while(i>0){
          i--;
          idx=create.expression(StandardOperator.Mult,idx,dims[i]);
          idx=create.expression(StandardOperator.Plus,idx,args.get(i));
        }
      }
      return create.expression(StandardOperator.Subscript,rewrite(node),idx);
    }
    return null;
  }
}
