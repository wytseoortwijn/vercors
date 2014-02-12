package vct.antlr4.parser;

import static hre.System.Debug;
import static hre.System.Fail;
import static hre.System.Warning;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import pv.parser.PVFullLexer;
import pv.parser.PVFullParser;
import pv.parser.PVFullParser.ArgsContext;
import pv.parser.PVFullParser.BlockContext;
import pv.parser.PVFullParser.ClazContext;
import pv.parser.PVFullParser.ContractContext;
import pv.parser.PVFullParser.ExprContext;
import pv.parser.PVFullParser.Fence_listContext;
import pv.parser.PVFullParser.FieldContext;
import pv.parser.PVFullParser.FunctionContext;
import pv.parser.PVFullParser.InvariantContext;
import pv.parser.PVFullParser.KernelContext;
import pv.parser.PVFullParser.Kernel_fieldContext;
import pv.parser.PVFullParser.LexprContext;
import pv.parser.PVFullParser.MethodContext;
import pv.parser.PVFullParser.ProgramContext;
import pv.parser.PVFullParser.StatementContext;
import pv.parser.PVFullParser.TupleContext;
import pv.parser.PVFullParser.TypeContext;
import pv.parser.PVFullVisitor;
import vct.col.ast.ASTClass;
import vct.col.ast.ASTNode;
import vct.col.ast.BlockStatement;
import vct.col.ast.CompilationUnit;
import vct.col.ast.Contract;
import vct.col.ast.ContractBuilder;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Dereference;
import vct.col.ast.NameExpression;
import vct.col.ast.ParallelBarrier;
import vct.col.ast.ProgramUnit;
import vct.col.ast.StandardOperator;
import vct.col.ast.Type;
import vct.col.ast.ASTClass.ClassKind;
import vct.col.ast.Method.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.util.Syntax;
import static vct.col.ast.ASTReserved.*;

/**
 * Convert ANTLR parse trees for PVL to COL.
 * 
 * @author <a href="mailto:s.c.c.blom@utwente.nl">Stefan Blom</a>
*/
public class PVLtoCOL extends ANTLRtoCOL implements PVFullVisitor<ASTNode> {

  public static CompilationUnit convert(ParseTree tree, String file_name,BufferedTokenStream tokens,org.antlr.v4.runtime.Parser parser) {
    CompilationUnit unit=new CompilationUnit(file_name);
    PVLtoCOL visitor=new PVLtoCOL(PVLSyntax.get(),file_name,tokens,parser);
    visitor.scan_to(unit,tree);
    return unit;
  }
  public PVLtoCOL(Syntax syntax, String filename, BufferedTokenStream tokens,org.antlr.v4.runtime.Parser parser) {
    super(syntax, filename, tokens,parser,PVFullLexer.ID,PVFullLexer.class);
  }

  @Override
  public ASTNode visitKernel_field(Kernel_fieldContext ctx) {
    if (ctx.children.size()>4) visit(ctx);
    ASTNode res=create.field_decl(getIdentifier(ctx,2),(Type)convert(ctx.children.get(1)));
    String keyword=ctx.children.get(0).toString();
    switch(keyword){
    case "global":
      res.setStatic(true);
      break;
    case "local":
      res.setStatic(false);
      break;
    default:
      Fail("bad variable class %s",keyword);
    }
    return res;
  }

  @Override
  public ASTNode visitClaz(ClazContext ctx) {
    String name=getIdentifier(ctx,1);
    ASTClass cl=create.ast_class(name,ClassKind.Plain,null,null);
    for(int i=3;i<ctx.children.size()-1;i++){
      cl.add_dynamic(convert(ctx.children.get(i)));
    }
    return cl;
  }

  @Override
  public ASTNode visitContract(ContractContext ctx) {
    ContractBuilder cb=new ContractBuilder();
    Debug("contract %s",ctx.toStringTree());
    if (ctx.children!=null){
      int N=ctx.children.size();
      for(int i=0;i<N;){
        switch(ctx.children.get(i).toString()){
        case "requires":
          cb.requires(convert(ctx.children.get(i+1)));
          i+=3;
          break;
        case "ensures":
          cb.ensures(convert(ctx.children.get(i+1)));
          i+=3;
          break;
        case "given":{
          Type type=(Type)convert(ctx.children.get(i+1));
          String name=getIdentifier(ctx, i+2);
          if (ctx.children.get(i+3).toString().equals(";")){
            i+=4;
            cb.given(create.field_decl(name, type));
            break;
          }
          Fail("missing case in %s",ctx.children.get(i));
        }
        case "yields":{
          Type type=(Type)convert(ctx.children.get(i+1));
          String name=getIdentifier(ctx, i+2);
          if (ctx.children.get(i+3).toString().equals(";")){
            i+=4;
            cb.yields(create.field_decl(name, type));
            break;
          }
          Fail("missing case in %s",ctx.children.get(i));
        }
        default:
          Fail("missing case: %s",ctx.children.get(i));
        }
      }
    }
    return cb.getContract(false);
  }

  @Override
  public ASTNode visitArgs(ArgsContext ctx) {
    throw hre.System.Failure("illegal call to visitArgs");
  }
  
  private DeclarationStatement[] convertArgs(ArgsContext ctx){
    ArrayList<DeclarationStatement> args=new ArrayList<DeclarationStatement>();
    DeclarationStatement empty[]=new DeclarationStatement[0];
    if (ctx.children==null) return empty;
    int N=ctx.children.size();
    for(int i=0;i<N;i+=3){
      Type type=(Type)convert(ctx.children.get(i));
      String name=getIdentifier(ctx, i+1);
      args.add(create.field_decl(name, type));
    }
    return args.toArray(empty);
  }

  @Override
  public ASTNode visitTuple(TupleContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFence_list(Fence_listContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitBlock(BlockContext ctx) {
    BlockStatement block=create.block();
    int N=ctx.children.size()-1;
    for(int i=1;i<N;i++){
      block.add_statement(convert(ctx.children.get(i)));
      ParseTree tmp=ctx.children.get(i);
    }
    return block;
  }

  @Override
  public ASTNode visitExpr(ExprContext ctx) {
    if (ctx.children.size()==1){
      ASTNode res=try_specials(ctx.children.get(0).toString());
      if (res!=null) return res;
      return convert(ctx.children.get(0));
    }
    if (ctx.children.get(0) instanceof TerminalNode){
      switch(ctx.children.get(0).toString()){
      case "old":
        return create.expression(StandardOperator.Old,getTuple((ParserRuleContext)ctx.children.get(1)));
      case "perm":
        return create.expression(StandardOperator.Perm,getTuple((ParserRuleContext)ctx.children.get(1)));
      case "value":
        return create.expression(StandardOperator.Value,getTuple((ParserRuleContext)ctx.children.get(1)));
      case "pointsto":
        return create.expression(StandardOperator.PointsTo,getTuple((ParserRuleContext)ctx.children.get(1)));
      }
    }
    if (ctx.children.size()==3
        && ctx.children.get(0) instanceof PVFullParser.ExprContext
        && ctx.children.get(1) instanceof TerminalNode
        && ctx.children.get(2) instanceof PVFullParser.ExprContext
    ){
      ASTNode e1=convert(ctx.children.get(0));
      ASTNode e2=convert(ctx.children.get(2));
      switch(ctx.children.get(1).toString()){
      case ".": return create.dereference(e1,e2.toString());
//      case "mul": return create.expression(StandardOperator.Mult,e1,e2);
//      case "div": return create.expression(StandardOperator.Div,e1,e2);
//      case "mod": return create.expression(StandardOperator.Mod,e1,e2);
      case ">": return create.expression(StandardOperator.GT,e1,e2);
      case ">=": return create.expression(StandardOperator.GTE,e1,e2);
      case "<": return create.expression(StandardOperator.LT,e1,e2);
      case "<=": return create.expression(StandardOperator.LTE,e1,e2);
      case "*": return create.expression(StandardOperator.Star,e1,e2);
      case "&": return create.expression(StandardOperator.And,e1,e2);
      case "|": return create.expression(StandardOperator.Or,e1,e2);
      case "->": return create.expression(StandardOperator.Implies,e1,e2);
//      case "+": return create.expression(StandardOperator.Plus,e1,e2);
//      case "-": return create.expression(StandardOperator.Minus,e1,e2);
      case "=": return create.expression(StandardOperator.EQ,e1,e2);
      case "!=": return create.expression(StandardOperator.NEQ,e1,e2);
      }
    }
    if (match(ctx,"!",null)){
      return create.expression(StandardOperator.Not,convert(ctx,1));
    }
    if (match(ctx,null,"?",null,":",null)){
      return create.expression(StandardOperator.ITE,convert(ctx,0),convert(ctx,2),convert(ctx,4));
    }
    if (match(ctx,"(",null,")")){
      return convert(ctx,1);
    }
    if (match(ctx,null,tuple)){
      return get_invokation(ctx,0);
    }
    if (match(ctx,"new",null)){
      return create.expression(StandardOperator.New,create.class_type(getIdentifier(ctx,1)));
    }
    if (match(ctx,"(","forall*",null,null,";",null,";",null,")")){
      return create.starall(convert(ctx,5),convert(ctx,7),create.field_decl(getIdentifier(ctx,3),(Type)convert(ctx,2)));
    }
    if (match(ctx,"(","forall",null,null,";",null,";",null,")")){
      return create.forall(convert(ctx,5),convert(ctx,7),create.field_decl(getIdentifier(ctx,3),(Type)convert(ctx,2)));
    }
    if (match(ctx,"(","exists",null,null,";",null,";",null,")")){
      return create.exists(convert(ctx,5),convert(ctx,7),create.field_decl(getIdentifier(ctx,3),(Type)convert(ctx,2)));
    }
    return visit(ctx);
  }

  @Override
  public ASTNode visitType(TypeContext ctx) {
    ASTNode res=null;
    if (match(0,true,ctx,"TerminalNode")){
      Sort sort=Sort.Void;
      switch(ctx.children.get(0).toString()){
      case "boolean": res=create.primitive_type(sort=Sort.Boolean); break;
      case "frac": res=create.primitive_type(Sort.Fraction); break;
      case "int": res=create.primitive_type(Sort.Integer); break;
      case "pred": res=create.primitive_type(Sort.Resource); break;
      case "resource": res=create.primitive_type(Sort.Resource); break;
        case "void": res=create.primitive_type(Sort.Void); break;
        default: res=create.class_type(ctx.children.get(0).toString()); break;
      }
    } else {
      Fail("unknown type %s",ctx.toStringTree());
    }
    int N=ctx.children.size()/3;
    for(int i=0;i<N;i++){
      if (match(3*i+1,true,ctx,"[","ExprContext","]")){
        res=create.primitive_type(Sort.Array,res,convert(ctx.children.get(3*i+2)));
      } else {
        Fail("unknown type %s",ctx.toStringTree());
      }
    }
    return res;
  }

  @Override
  public ASTNode visitKernel(KernelContext ctx) {
    String name=getIdentifier(ctx,1);
    ASTClass cl=create.ast_class(name,ClassKind.Kernel,null,null);
    for(int i=3;i<ctx.children.size()-1;i++){
      ASTNode tmp=convert(ctx.children.get(i));
      if (tmp.isStatic()){
        cl.add_static(tmp);
      } else {
        cl.add_dynamic(tmp);
      }
    }
    return cl;
  }

  @Override
  public ASTNode visitFunction(FunctionContext ctx) {
    Contract c=(Contract) convert(ctx.children.get(0));
    Type returns=(Type)convert(ctx.children.get(1));
    String name=getIdentifier(ctx,2);
    DeclarationStatement args[]=convertArgs((ArgsContext) ctx.children.get(4));
    ASTNode body=convert(ctx.children.get(7));
    Kind kind;
    if (returns.isPrimitive(Sort.Resource)) {
      kind=Kind.Predicate;
    } else {
      kind=Kind.Pure;
    }
    ASTNode res=create.method_kind(kind,returns,c, name, args ,body);
    res.setStatic(false);
    return res;
  }
  
  private String type_expr="TypeContext";
  private String tuple="TupleContext";

  @Override
  public ASTNode visitStatement(StatementContext ctx) {
    if (match(ctx,null,":=",null,";")){
      return create.assignment(convert(ctx,0),convert(ctx,2));
    }
    if (match(ctx,"return",null,";")){
      return create.return_statement(convert(ctx,1));
    }
    if (match(ctx,type_expr,null,";")){
      return create.field_decl(getIdentifier(ctx,1),(Type)convert(ctx,0));
    }
    if (match(ctx,type_expr,null,":=",null,";")){
      return create.field_decl(getIdentifier(ctx,1),(Type)convert(ctx,0),convert(ctx,3));
    }
    if (match(ctx,"if","(",null,")",null)){
      return create.ifthenelse(convert(ctx,2),convert(ctx,4));
    }
    if (match(ctx,"if","(",null,")",null,"else",null)){
      return create.ifthenelse(convert(ctx,2),convert(ctx,4),convert(ctx,6));
    }
    if (match(ctx,null,"while","(",null,")",null)){
      PVFullParser.InvariantContext inv_ctx=(PVFullParser.InvariantContext)ctx.children.get(0);
      int N = (inv_ctx.children==null) ? 0 : inv_ctx.children.size()/3;
      ASTNode invs[]=new ASTNode[N];
      for(int i=0;i<N;i++){
        invs[i]=convert(inv_ctx,3*i+1);
      }
      return create.while_loop(convert(ctx,3),convert(ctx,5),invs);
    }
    if (match(ctx,"assert",null,";")){
      return create.expression(StandardOperator.Assert,convert(ctx,1));
    }
    if (match(ctx,"assume",null,";")){
      return create.expression(StandardOperator.Assume,convert(ctx,1));
    }
    if (match(ctx,"fork",null,";")){
      return create.expression(StandardOperator.Fork,convert(ctx,1));
    }
    if (match(ctx,"join",null,";")){
      return create.expression(StandardOperator.Join,convert(ctx,1));
    }
    if (match(ctx,"fold",null,";")){
      return create.expression(StandardOperator.Fold,convert(ctx,1));
    }
    if (match(ctx,"unfold",null,";")){
      return create.expression(StandardOperator.Unfold,convert(ctx,1));
    }
    if (match(ctx,"call",null,tuple,";")){
      return get_invokation(ctx,1);
    }
    if (match(ctx,"barrier","(",null,")","{",null,"}")){
      ContractBuilder cb=new ContractBuilder();
      EnumSet<ParallelBarrier.Fence> fences=EnumSet.noneOf(ParallelBarrier.Fence.class);
      if (((ParserRuleContext)ctx.children.get(2)).children!=null){
        for (ParseTree item:((ParserRuleContext)ctx.children.get(2)).children){
          String tag=item.toString();
          switch(tag){
          case "local":
            fences.add(ParallelBarrier.Fence.Local);
            continue;
          case "global":
            fences.add(ParallelBarrier.Fence.Global);
            continue;
          default:
            Fail("unknown fence %s",tag);
          }
        }
      }
      Contract c=(Contract)convert(ctx,5);
      return create.barrier(c,fences);
    }
    return visit(ctx);
  }

  @Override
  public ASTNode visitField(FieldContext ctx) {
    if (ctx.children.size()>3) visit(ctx);
    return create.field_decl(getIdentifier(ctx,1),(Type)convert(ctx.children.get(0)));
  }

  @Override
  public ASTNode visitInvariant(InvariantContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLexpr(LexprContext ctx) {
    ASTNode res=convert(ctx,0);
    int N=ctx.children.size();
    for(int i=1;i<N;){
      if (match(i,true,ctx,".",null)){
        res=create.dereference(res,getIdentifier(ctx,i+1));
        i+=2;
      } else if(match(i,true,ctx,"[",null,"]")){
        res=create.expression(StandardOperator.Subscript,res,convert(ctx,i+1));
        i+=3;
      } else {
        Fail("unknown lexpr");
      }
    }
    return res;
  }

  @Override
  public ASTNode visitProgram(ProgramContext ctx) {
    /*
    for(ParseTree item:ctx.children){
      if (item instanceof ClazContext || item instanceof KernelContext){
        ASTClass cl=(ASTClass)convert(item);
        unit.add(cl);
      } else {
        Fail("cannot handle %s at top level",item.getClass());
      }
    }
*/
    return null;
  }

  @Override
  public ASTNode visitMethod(MethodContext ctx) {
    Contract c=(Contract) convert(ctx.children.get(0));
    Type returns=(Type)convert(ctx.children.get(1));
    String name=getIdentifier(ctx,2);
    DeclarationStatement args[]=convertArgs((ArgsContext) ctx.children.get(4));
    ASTNode body=convert(ctx.children.get(6));
    ASTNode res=create.method_decl(returns,c, name, args ,body);
    res.setStatic(false);
    return res;
  }

  private ASTNode get_invokation(ParserRuleContext ctx,int ofs) {
    ASTNode f=convert(ctx.children.get(ofs));
    ASTNode args[]=getTuple((ParserRuleContext)ctx.children.get(ofs+1));
    if (f instanceof Dereference){
      Dereference fd=(Dereference) f;
      return create.invokation(fd.object,null,fd.field,args);
    } else if (f instanceof NameExpression){
      return create.invokation(null,null,((NameExpression)f).getName(),args);
    } else {
      throw hre.System.Failure("unimplemented invokation");
    }
  }
  
  private ASTNode[] getTuple(ParserRuleContext ctx){
    int N=(ctx.children.size()-1)/2;
    ASTNode res[]=new ASTNode[N];
    for(int i=0;i<N;i++){
      res[i]=convert(ctx,2*i+1);
    }
    return res;
  }

  private ASTNode try_specials(String text){
    switch(text){
    case "tcount":
    case "gsize":
    case "tid":
    case "gid":
    case "lid":
      return create.unresolved_name(text);
    case "this":
      return create.reserved_name(This);
    case "result": return create.reserved_name(Result);
    case "null": return create.reserved_name(Null);
    case "true": return create.constant(true);
    case "false": return create.constant(false);
    }
    return null;
  }
  
  @Override
  public ASTNode visitTerminal(TerminalNode node){
    Token tok=node.getSymbol();
    ASTNode res=try_specials(tok.getText());
    if (res!=null) return res;
    switch(tok.getType()){
    case PVFullLexer.ID:
      return create.unresolved_name(tok.getText());
    case PVFullLexer.NUMBER:
      return create.constant(Integer.parseInt(tok.getText()));
    }
    Fail("At %s: unimplemented terminal node",create.getOrigin());
    return visit(node);
  }
 

}
