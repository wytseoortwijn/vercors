package vct.antlr4.parser;

import hre.HREError;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicBoolean;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.Parser;

import com.sun.net.httpserver.Authenticator.Failure;

import vct.col.ast.*;
import vct.col.ast.ASTSpecial.Kind;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.syntax.JavaDialect;
import vct.col.syntax.JavaSyntax;
import vct.col.syntax.Syntax;
import vct.parsers.Java8JMLParser.*;
import vct.parsers.*;
import vct.util.Configuration;

/**
 * Convert JML parse trees to COL.
 *
 * @author <a href="mailto:s.c.c.blom@utwente.nl">Stefan Blom</a>
*/
public class Java8JMLtoCol extends AbstractJava8ToCol implements Java8JMLVisitor<ASTNode> {
  
  private static <E extends ASTSequence<?>> E convert(E unit,ParseTree tree, String file_name,BufferedTokenStream tokens,Parser parser){
    Java8JMLtoCol visitor=new Java8JMLtoCol(unit,JavaSyntax.getJava(JavaDialect.JavaVerCors),file_name,tokens,parser);
    visitor.scan_to(unit,tree);
    return unit;
  }
  
  public static ProgramUnit convert(ParseTree tree, String file_name,BufferedTokenStream tokens,Parser parser) {
    return convert(new ProgramUnit(),tree,file_name,tokens,parser);
  }
  
  public static TempSequence convert_seq(ParseTree tree, String file_name,BufferedTokenStream tokens,Parser parser) {
    return convert(new TempSequence(),tree,file_name,tokens,parser);
  }

  public Java8JMLtoCol(ASTSequence<?> unit,Syntax syntax, String filename, BufferedTokenStream tokens, Parser parser) {
    super(unit,syntax, filename, tokens, parser, Java8JMLLexer.Identifier, Java8JMLLexer.COMMENT,Java8JMLLexer.class);
  }

  

  private void add_proof_script(OperatorExpression res, ParseTree child) {
    ParserRuleContext ctx=(ParserRuleContext)child;
    for(int i=0;i<ctx.getChildCount();i+=2){
      if (match(i,true,ctx,"label",null)){
        res.addLabel(create.label(getIdentifier(ctx,i+1)));
      } else if (match(i,true,ctx,"with",null)){
        scan_body(res.get_before(),(ParserRuleContext)ctx.getChild(i+1));
      } else if (match(i,true,ctx,"then",null)){
        scan_body(res.get_after(),(ParserRuleContext)ctx.getChild(i+1));
      } 
    }
  }

  public ASTNode getResourceExpression(ParserRuleContext ctx) {
    String label=null;
    int offset=0;
    if (match(ctx,null,":",null)){
      label=getIdentifier(ctx,0);
      ASTNode res=convert(ctx,2);
      if (res.isa(StandardOperator.Implies)){
        ((OperatorExpression)res).getArg(1).labeled(label);
      } else {
        res.labeled(label);
      }
      return res;
    }
    if (match(0,true,ctx,null,":")){
      label=getIdentifier(ctx,0);
      offset=2;
    }
    if (match(offset,true,ctx,null,"->",null,"(")){
      ASTNode object=convert(ctx,offset);
      String name=getIdentifier(ctx,offset+2);
      ASTNode args[];
      if (ctx.getChildCount()==offset+5){
        args=new ASTNode[0];
      } else {
        args=convert_list((ParserRuleContext)(ctx.getChild(offset+4)),",");
      }
      ASTNode call=create.invokation(object, null, name, args);
      if (label!=null) call.labeled(label);
      return create.expression(StandardOperator.Implies,
            create.expression(StandardOperator.NEQ,object,create.reserved_name(ASTReserved.Null)),
            call);
    }
    if (match(ctx,null,".",null,"@",null,"(",")")){
      return create.invokation(convert(ctx,0),forceClassType(convert(ctx,4)), getIdentifier(ctx,2));
    }
    if (match(ctx,null,".",null,"@",null,"(",null,")")){
      ASTNode args[]=convert_list((ParserRuleContext)(ctx.getChild(6)),",");
      return create.invokation(convert(ctx,0),forceClassType(convert(ctx,4)), getIdentifier(ctx,2),args);
    }
    if (match(ctx,null,"@",null,"(",")")){
      return create.invokation(null,forceClassType(convert(ctx,2)), getIdentifier(ctx,0));
    }
    if (match(ctx,null,"@",null,"(",null,")")){
      ASTNode args[]=convert_list((ParserRuleContext)(ctx.getChild(4)),",");
      return create.invokation(null,forceClassType(convert(ctx,2)), getIdentifier(ctx,0),args);
    }
    return super.getResourceExpression(ctx);
  }

  private String[] to_name(ASTNode pkg) {
    ArrayList<String> list=new ArrayList();
    while(pkg instanceof Dereference){
      Dereference d=(Dereference)pkg;
      list.add(0,d.field);
      pkg=d.object;
    }
    list.add(0,pkg.toString());
    return list.toArray(new String[0]);
  }

  @Override
  public ASTNode visitAdditionalBound(AdditionalBoundContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAdditiveExpression(AdditiveExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAmbiguousName(AmbiguousNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAndExpression(AndExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotation(AnnotationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationTypeBody(AnnotationTypeBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationTypeDeclaration(
      AnnotationTypeDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationTypeElementDeclaration(
      AnnotationTypeElementDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationTypeElementModifier(
      AnnotationTypeElementModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationTypeMemberDeclaration(
      AnnotationTypeMemberDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArgumentList(ArgumentListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArguments(ArgumentsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayAccess(ArrayAccessContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayAccess_lf_primary(ArrayAccess_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayAccess_lfno_primary(
      ArrayAccess_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayCreationExpression(ArrayCreationExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayInitializer(ArrayInitializerContext ctx) {
    return getArrayInitializer(ctx);
  }

  @Override
  public ASTNode visitArrayType(ArrayTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAssertStatement(AssertStatementContext ctx) {
    return null;
  }

  @Override
  public ASTNode visitAssignment(AssignmentContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAssignmentExpression(AssignmentExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAssignmentOperator(AssignmentOperatorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

 
  @Override
  public ASTNode visitAxiomDeclaration(AxiomDeclarationContext ctx) {
    if (match(ctx,"axiom",null,"{",null,"==",null,"}")){
      return create.axiom(getIdentifier(ctx,1),create.expression(StandardOperator.EQ,convert(ctx,3),convert(ctx,5)));
    }
    return null;
  }

  private ASTNode getBasicFor(ParserRuleContext ctx){
    int ptr=2;
    ASTNode init;
    if (match(ptr,true,ctx,";")){
      ptr+=1;
      init=null;
    } else {
      init=convert(ctx,ptr);
      // It is probably a bug that the following line is needed.
      init=create.block(init.getOrigin(),init);
      ptr+=2;
    }
    ASTNode test;
    if (match(ptr,true,ctx,";")){
      ptr+=1;
      test=null;
    } else {
      test=convert(ctx,ptr);
      ptr+=2;
    }
    ASTNode update;
    if (match(ptr,true,ctx,")")){
      update=null;
      ptr+=1;
    } else {
      update=convert(ctx,ptr);
      ptr+=2;
    }    
    ASTList lst=new ASTList();
    scan_comments_before(lst,ctx.getChild(ptr));
    ASTNode body=convert(ctx,ptr);
    LoopStatement loop=create.for_loop(init, test, update, body);
    for(ASTNode n:lst) loop.get_after().add(n);
    return loop;
  }
  
  @Override
  public ASTNode visitBasicForStatement(BasicForStatementContext ctx) {
    return getBasicFor(ctx);
  }

  
  @Override
  public ASTNode visitBasicForStatementNoShortIf(
      BasicForStatementNoShortIfContext ctx) {
    return getBasicFor(ctx);
  }

  @Override
  public ASTNode visitBlock(BlockContext ctx) {
    return getBlock(ctx);
  }

  @Override
  public ASTNode visitBlockStatement(BlockStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitBlockStatements(BlockStatementsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitBreakStatement(BreakStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCastExpression(CastExpressionContext ctx) {
    ASTNode t=convert(ctx,1);
    ASTNode e=convert(ctx,3);
    return create.expression(StandardOperator.Cast, t ,e);
  }

  @Override
  public ASTNode visitCatchClause(CatchClauseContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCatches(CatchesContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCatchFormalParameter(CatchFormalParameterContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCatchType(CatchTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassBody(ClassBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassBodyDeclaration(ClassBodyDeclarationContext ctx) {
    return getClassBodyDeclaration(ctx);
  }

  @Override
  public ASTNode visitClassDeclaration(ClassDeclarationContext ctx) {
    return null;
  }

  @Override
  public ASTNode visitClassInstanceCreationExpression(
      ClassInstanceCreationExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassInstanceCreationExpression_lf_primary(
      ClassInstanceCreationExpression_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  ASTNode doNew(int ofs,ParserRuleContext ctx){
    if (match(ofs,false,ctx,"new",null,"(",")")){
      MethodInvokation res=create.new_object(create.class_type(getIdentifier(ctx,ofs+1)));
      scan_comments_after(res.get_after(),ctx.getChild(ofs+3));
      return res;
    }
    if (match(ofs,false,ctx,"new",null,"(",null,")")){
      MethodInvokation res=create.new_object(create.class_type(getIdentifier(ctx,ofs+1)),
          convert_list((ParserRuleContext)ctx.getChild(ofs+3),","));
      scan_comments_after(res.get_after(),ctx.getChild(ofs+4));
      return res;
    }    
    return null;
  }
  
  @Override
  public ASTNode visitClassInstanceCreationExpression_lfno_primary(
      ClassInstanceCreationExpression_lfno_primaryContext ctx) {
    if (match(0,true,ctx,"new")) {
      return doNew(0,ctx);
    }
    return null;
  }

  @Override
  public ASTNode visitClassMemberDeclaration(ClassMemberDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassModifier(ClassModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassOrInterfaceType(ClassOrInterfaceTypeContext ctx) {
    return getClassOrInterfaceType(ctx);
  }

  @Override
  public ASTNode visitClassType(ClassTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassType_lf_classOrInterfaceType(
      ClassType_lf_classOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassType_lfno_classOrInterfaceType(
      ClassType_lfno_classOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCompilationUnit(CompilationUnitContext ctx) {
    NameSpace ns;
    int ptr=0;
    if (match(0,true,ctx,"PackageDeclaration")) {
      hre.System.Debug("has package");
      ASTNode pkg=convert((ParserRuleContext)ctx.getChild(0),1);
      System.err.printf("pkg %s (%s)%n",Configuration.getDiagSyntax().print(pkg),pkg.getClass());
      ptr++;
      ns=create.namespace(to_name(pkg));
    } else {
      hre.System.Debug("does not have package");
      ns=create.namespace(NameSpace.NONAME);
    }
    while(match(ptr,true,ctx,"ImportDeclaration")){
      ParserRuleContext imp=(ParserRuleContext)ctx.getChild(ptr);
      if (match(imp,"import",null,";")){
        ASTNode name=convert(imp,1);
        ns.add_import(false,false,to_name(name));
      } else if (match(imp,"import",null,".","*",";")){
        ASTNode name=convert(imp,1);
        ns.add_import(false,true,to_name(name));
      } else if (match(imp,"import","static",null,";")){
        ASTNode name=convert(imp,2);
        ns.add_import(true,false,to_name(name));
      } else if (match(imp,"import","static",null,".","*",";")){
        ASTNode name=convert(imp,2);
        ns.add_import(true,true,to_name(name));
      } else {
        hre.System.Abort("unimplemented import type");
      }
      ptr++;
    }
    scan_to(ns, ctx, ptr, ctx.getChildCount());
    return ns;
  }

  @Override
  public ASTNode visitConditionalAndExpression(
      ConditionalAndExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConditionalExpression(ConditionalExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConditionalOrExpression(ConditionalOrExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantDeclaration(ConstantDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantExpression(ConstantExpressionContext ctx) {
    return getExpression(ctx);
  }

  @Override
  public ASTNode visitConstantModifier(ConstantModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstructorBody(ConstructorBodyContext ctx) {
    return getBlock(ctx);
  }

  @Override
  public ASTNode visitConstructorDeclaration(ConstructorDeclarationContext ctx) {
    int base=0;
    int N=ctx.getChildCount();
    while(!match(base,true,ctx,"ConstructorDeclarator")){
      base++;
    }
    ParserRuleContext cons_ctx=(ParserRuleContext)ctx.getChild(base);
    if (base!=N-2){
      throw new Error("no exceptions yet");
    }
    String name=getIdentifier(cons_ctx,0);
    DeclarationStatement[] args;
    if (match(cons_ctx,null,"(",")")){
      args=new DeclarationStatement[0];
    } else {
      args=getFormalParameters(cons_ctx.getChild(2),new AtomicBoolean());
    }
    ASTNode body=convert(ctx,N-1);
    Type returns=create.primitive_type(Sort.Void);
    Method res=create.method_kind(Method.Kind.Constructor, returns ,null, name, args, body);
    for(int i=0;i<base;i++){
      res.attach(convert(ctx,i));
    }
    return res;
  }

  @Override
  public ASTNode visitConstructorDeclarator(ConstructorDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstructorModifier(ConstructorModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitContinueStatement(ContinueStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDefaultValue(DefaultValueContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDimExpr(DimExprContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDimExprs(DimExprsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDims(DimsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDoStatement(DoStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitElementValue(ElementValueContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitElementValueArrayInitializer(
      ElementValueArrayInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitElementValueList(ElementValueListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitElementValuePair(ElementValuePairContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }
  
  @Override
  public ASTNode visitElementValuePairList(ElementValuePairListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEmptyStatement(EmptyStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnhancedForStatement(EnhancedForStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnhancedForStatementNoShortIf(
      EnhancedForStatementNoShortIfContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumBody(EnumBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumBodyDeclarations(EnumBodyDeclarationsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumConstant(EnumConstantContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumConstantList(EnumConstantListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumConstantModifier(EnumConstantModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumConstantName(EnumConstantNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumDeclaration(EnumDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEqualityExpression(EqualityExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExceptionType(ExceptionTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExceptionTypeList(ExceptionTypeListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExclusiveOrExpression(ExclusiveOrExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExplicitConstructorInvocation(
      ExplicitConstructorInvocationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExpression(ExpressionContext ctx) {
    return getExpression(ctx);
  }

  @Override
  public ASTNode visitExpressionList(ExpressionListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExpressionName(ExpressionNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExpressionStatement(ExpressionStatementContext ctx) {
    return convert(ctx,0);
  }

  @Override
  public ASTNode visitExtendsInterfaces(ExtendsInterfacesContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFieldAccess(FieldAccessContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFieldAccess_lf_primary(FieldAccess_lf_primaryContext ctx) {
    return create.dereference(primarystack.pop(),getIdentifier(ctx,1));
  }

  @Override
  public ASTNode visitFieldAccess_lfno_primary(
      FieldAccess_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFieldDeclaration(FieldDeclarationContext ctx) {
    return getVariableDeclaration(ctx);
  }

  private ASTNode getVariableDeclaration(ParserRuleContext ctx) {
    int base=0;
    int N=ctx.getChildCount();
    while(!match(base,true,ctx,"UnannType")){
      base++;
    }
    Type t=checkType(convert(ctx,base));
    ASTNode vars[]=convert_list((ParserRuleContext)ctx.getChild(base+1),",");
    VariableDeclaration decl=create.variable_decl(t);
    for(int i=0;i<vars.length;i++){
      DeclarationStatement tmp;
      if (vars[i] instanceof NameExpression){
        String name=((NameExpression)vars[i]).getName();
        tmp=create.field_decl(name,create.class_type(name));
      } else if (vars[i] instanceof DeclarationStatement) {
        DeclarationStatement d=(DeclarationStatement)vars[i];
        tmp=create.field_decl(d.getName(),d.getType(),d.getInit());
      } else {
        throw new HREError("unexpected %s in variable list at %s",vars[i].getClass(),create.getOrigin());
      }
      decl.add(tmp);
    }
    for(int i=0;i<base;i++){
      decl.attach(convert(ctx,i));
    }
    return decl;
  }

  @Override
  public ASTNode visitFieldModifier(FieldModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFinally_(Finally_Context ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFloatingPointType(FloatingPointTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitForInit(ForInitContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFormalParameter(FormalParameterContext ctx) {
    return getFormalParameter(ctx);
  }

  @Override
  public ASTNode visitFormalParameterList(FormalParameterListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFormalParameters(FormalParametersContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitForStatement(ForStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitForStatementNoShortIf(ForStatementNoShortIfContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitForUpdate(ForUpdateContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  
  @Override
  public ASTNode visitFunctionDeclaration(FunctionDeclarationContext ctx) {
    int N=ctx.getChildCount();
    Method m=(Method)convert(ctx,N-4);
    m.setBody(convert(ctx,N-2));
    for(int i=0;i<N-4;i++){
      m.attach(convert(ctx,i));
    }
    m.attach(create.reserved_name(ASTReserved.Pure));
    return m;
  }
  
  public ASTNode PreviousvisitFunctionDeclaration(FunctionDeclarationContext ctx) {
    Contract contract=null;
    int i=0;
    if (match(0,true,ctx,"ContractContext")){
      contract=(Contract)convert(ctx,0);
      i=1;
    }
    int i0=i;
    while(match(i,true,ctx,"ModifierContext")){
      // skip now convert later.
      i++;
    }
    Type returns=checkType(convert(ctx,i));
    String name=getIdentifier(ctx,i+1);
    hre.System.Debug("function %s, contract %s",name,contract);
    AtomicBoolean varargs=new AtomicBoolean();
    DeclarationStatement args[]=getFormalParameters(ctx.getChild(i+2),varargs);
    if (varargs.get()){
      hre.System.Fail("functions with varargs not supported yet.");
    }
    ASTNode body=null;
    if (match(i+3,false,ctx,"=",null,";")){
      body=convert(ctx,i+4);
    }
    Method res=create.function_decl(returns, contract, name, args, body);
    hre.System.Debug("function %s, contract %s",res.name,res.getContract());
    while(i0<i){
      //add modifiers as annotations.
      ASTNode mod=convert(ctx,i0);
      //System.err.printf("<modifier! %s = %s%n",ctx.getChild(i0).toStringTree(parser),mod);
      res.attach(mod);
      i0++;
    }
    return res;
  }

  @Override
  public ASTNode visitIfThenElseStatement(IfThenElseStatementContext ctx) {
    return create.ifthenelse(convert(ctx,2),convert(ctx,4),convert(ctx,6));
  }

  @Override
  public ASTNode visitIfThenElseStatementNoShortIf(
      IfThenElseStatementNoShortIfContext ctx) {
    return create.ifthenelse(convert(ctx,2),convert(ctx,4),convert(ctx,6));
  }

  @Override
  public ASTNode visitIfThenStatement(IfThenStatementContext ctx) {
    return create.ifthenelse(convert(ctx,2),convert(ctx,4));
  }

  @Override
  public ASTNode visitImportDeclaration(ImportDeclarationContext ctx) {
    return getImportDeclaration(ctx);
  }

  @Override
  public ASTNode visitInclusiveOrExpression(InclusiveOrExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInferredFormalParameterList(
      InferredFormalParameterListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInstanceInitializer(InstanceInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitIntegralType(IntegralTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceBody(InterfaceBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceDeclaration(InterfaceDeclarationContext ctx) {
    return getClassDeclaration(ctx);
  }

  @Override
  public ASTNode visitInterfaceMemberDeclaration(
      InterfaceMemberDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceMethodDeclaration(InterfaceMethodDeclarationContext ctx) {
    return getMethodDeclaration(ctx);
  }

  @Override
  public ASTNode visitInterfaceMethodModifier(InterfaceMethodModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceModifier(InterfaceModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceType(InterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceType_lf_classOrInterfaceType(
      InterfaceType_lf_classOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceType_lfno_classOrInterfaceType(
      InterfaceType_lfno_classOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceTypeList(InterfaceTypeListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLabeledExpression(LabeledExpressionContext ctx) {
    return getExpression(ctx);
  }

  @Override
  public ASTNode visitLabeledStatement(LabeledStatementContext ctx) {
    ASTNode S=convert(ctx,2);
    S.addLabel(create.label(getIdentifier(ctx, 0)));
    return S;
  }

  @Override
  public ASTNode visitLabeledStatementNoShortIf(
      LabeledStatementNoShortIfContext ctx) {
    ASTNode S=convert(ctx,2);
    S.addLabel(create.label(getIdentifier(ctx, 0)));
    return S;
  }

  @Override
  public ASTNode visitLambdaBody(LambdaBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLambdaExpression(LambdaExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLambdaParameters(LambdaParametersContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLastFormalParameter(LastFormalParameterContext ctx) {
    return getLastFormalParameter(ctx);
  }

  @Override
  public ASTNode visitLeftHandSide(LeftHandSideContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLiteral(LiteralContext ctx) {
    return getLiteral(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclaration(LocalVariableDeclarationContext ctx) {
    return getVariableDeclaration(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclarationStatement(
      LocalVariableDeclarationStatementContext ctx) {
    return convert(ctx,0);
  }

  @Override
  public ASTNode visitMarkerAnnotation(MarkerAnnotationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodBody(MethodBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodDeclaration(MethodDeclarationContext ctx) {
    return getMethodDeclaration(ctx);
  }

  @Override
  public ASTNode visitMethodDeclarator(MethodDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodHeader(MethodHeaderContext ctx) {
    return getMethodHeader(ctx);
  }

  private ASTNode getMethodInvocation(ParserRuleContext ctx) {
    if (match(0,true,ctx,"TypeName",".")||match(0,true,ctx,"Primary",".")){
      if (match(2,true,ctx,"super",".")||match(2,true,ctx,"TypeArguments")){
        throw new Error("missing case");
      }
      ASTNode object=convert(ctx,0);
      String method=getIdentifier(ctx,2);
      ASTNode args[];
      int close;
      if (match(4,true,ctx,"ArgumentList")){
        args=convert_list((ParserRuleContext)ctx.getChild(4),",");
        close=5;
      } else {
        args=new ASTNode[0];
        close=4;
      }
      MethodInvokation res=create.invokation(object,null, method, args);
      scan_comments_before(res.get_before(),ctx.getChild(3));
      scan_comments_after(res.get_after(),ctx.getChild(close));
      return res;
    }
    return getExpression(ctx);
  }
  
  @Override
  public ASTNode visitMethodInvocation(MethodInvocationContext ctx) {
    return getMethodInvocation(ctx);
  }

  @Override
  public ASTNode visitMethodInvocation_lf_primary(
      MethodInvocation_lf_primaryContext ctx) {
    int N=ctx.getChildCount();
    String method=getIdentifier(ctx,1);
    ASTNode args[];
    if (match(3,true,ctx,"ArgumentList")){
      args=convert_list((ParserRuleContext)ctx.getChild(3),",");
    } else {
      args=new ASTNode[0];
    }
    MethodInvokation res=create.invokation(primarystack.pop(), null, method, args);
    scan_comments_before(res.get_before(),ctx.getChild(2));
    scan_comments_after(res.get_after(),ctx.getChild(N-1));
    return res;
  }

  @Override
  public ASTNode visitMethodInvocation_lfno_primary(MethodInvocation_lfno_primaryContext ctx) {
    return getMethodInvocation(ctx);
  }

  @Override
  public ASTNode visitMethodModifier(MethodModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodName(MethodNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodReference(MethodReferenceContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodReference_lf_primary(
      MethodReference_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMethodReference_lfno_primary(
      MethodReference_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMultiplicativeExpression(
      MultiplicativeExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitNormalAnnotation(NormalAnnotationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitNormalClassDeclaration(NormalClassDeclarationContext ctx) {
    return getClassDeclaration(ctx);
  }

  @Override
  public ASTNode visitNormalInterfaceDeclaration(
      NormalInterfaceDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitNumericType(NumericTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageDeclaration(PackageDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageModifier(PackageModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageName(PackageNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageOrTypeName(PackageOrTypeNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostDecrementExpression(PostDecrementExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostDecrementExpression_lf_postfixExpression(
      PostDecrementExpression_lf_postfixExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostfixExpression(PostfixExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostIncrementExpression(PostIncrementExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostIncrementExpression_lf_postfixExpression(
      PostIncrementExpression_lf_postfixExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPreDecrementExpression(PreDecrementExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPreIncrementExpression(PreIncrementExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  
  
  private Stack<ASTNode> primarystack=new Stack();
  
  @Override
  public ASTNode visitPrimary(PrimaryContext ctx) {
    ASTNode res=convert(ctx,0);
    int N=ctx.getChildCount();
    for(int i=1;i<N;i++){
      int chk=primarystack.size();
      primarystack.push(res);
      res=convert(ctx,i);
      if (chk!=primarystack.size()){
        throw new HREError("stack problem %d expected %d found",chk,primarystack.size());
      }
    }
    return res;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray(PrimaryNoNewArrayContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lf_arrayAccess(
      PrimaryNoNewArray_lf_arrayAccessContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lf_primary(
      PrimaryNoNewArray_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lf_primary_lf_arrayAccess_lf_primary(
      PrimaryNoNewArray_lf_primary_lf_arrayAccess_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lf_primary_lfno_arrayAccess_lf_primary(
      PrimaryNoNewArray_lf_primary_lfno_arrayAccess_lf_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lfno_arrayAccess(
      PrimaryNoNewArray_lfno_arrayAccessContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lfno_primary(
      PrimaryNoNewArray_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lfno_primary_lf_arrayAccess_lfno_primary(
      PrimaryNoNewArray_lfno_primary_lf_arrayAccess_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimaryNoNewArray_lfno_primary_lfno_arrayAccess_lfno_primary(
      PrimaryNoNewArray_lfno_primary_lfno_arrayAccess_lfno_primaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimitiveType(PrimitiveTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitProofScript(ProofScriptContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitReceiverParameter(ReceiverParameterContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitReferenceType(ReferenceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitRelationalExpression(RelationalExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResource(ResourceContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResourceExpression(ResourceExpressionContext ctx) {
    return getResourceExpression(ctx);
  }

  @Override
  public ASTNode visitResourceList(ResourceListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResourceSpecification(ResourceSpecificationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResult(ResultContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitReturnStatement(ReturnStatementContext ctx) {
    if (ctx.getChildCount()==3){
      return create.return_statement(convert(ctx,1));
    } else {
      return create.return_statement();
    }
  }

  @Override
  public ASTNode visitShiftExpression(ShiftExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSimpleTypeName(SimpleTypeNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSingleElementAnnotation(SingleElementAnnotationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSingleStaticImportDeclaration(
      SingleStaticImportDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSingleTypeImportDeclaration(
      SingleTypeImportDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationDeclaration(
      SpecificationDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationModifier(SpecificationModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationPrimary(SpecificationPrimaryContext ctx) {
    return getSpecificationPrimary(ctx);
  }

  @Override
  public ASTNode visitSpecificationPrimitiveType(SpecificationPrimitiveTypeContext ctx) {
    if (match(ctx,"cell","<",null,">")){
      return create.primitive_type(Sort.Cell, checkType(convert(ctx,2)));
    }
    if (match(ctx,"seq","<",null,">")){
      return create.primitive_type(Sort.Sequence, checkType(convert(ctx,2)));
    }
    if (match(ctx,"bag","<",null,">")){
      return create.primitive_type(Sort.Bag, checkType(convert(ctx,2)));
    }
    if (match(ctx,"set","<",null,">")){
      return create.primitive_type(Sort.Set, checkType(convert(ctx,2)));
    }
    return null;
  }

  @Override
  public ASTNode visitSpecificationSequence(SpecificationSequenceContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationStatement(SpecificationStatementContext ctx) {
    ASTNode res=null;
    if (match(ctx,"loop_invariant",null,";")){
      res=create.special_decl(ASTSpecial.Kind.Invariant,convert(ctx,1));
    } else if (match(ctx,"set",null,"=",null,";")){
      res=create.assignment(convert(ctx,1),convert(ctx,3));
    } else if (match(ctx,"fold",null,";")){
      res=create.expression(StandardOperator.Fold,convert(ctx,1));
    } else if (match(ctx,"unfold",null,";")){
      res=create.expression(StandardOperator.Unfold,convert(ctx,1));
    } else if (match(ctx,"refute",null,";")){
      res=create.expression(StandardOperator.Refute,convert(ctx,1));    
    } else if (match(ctx,"assert",null,";")){
      res=create.expression(StandardOperator.Assert,convert(ctx,1));
    } else if (match(ctx,"check",null,";")){
      res=create.expression(StandardOperator.Assert,convert(ctx,1));
    } else if (match(ctx,"spec_ignore","{")){
      res=create.special(ASTSpecial.Kind.SpecIgnoreStart);
    } else if (match(ctx,"}","spec_ignore")){
      res=create.special(ASTSpecial.Kind.SpecIgnoreEnd);
    } else if (match(ctx,"inhale",null,";")){
      res=create.special(ASTSpecial.Kind.Inhale,convert(ctx,1));
    } else if (match(ctx,"exhale",null,";")){
      res=create.special(ASTSpecial.Kind.Exhale,convert(ctx,1));
    } else if (match(ctx,"send",null,"to",null,",",null,";")){//DRB       
      res=create.expression(StandardOperator.Send,convert(ctx,1),convert(ctx,3),convert(ctx,5));   
      res.setGhost(true);
    } else if (match(ctx,"recv",null,"from",null,",",null,";")){//DRB
      res=create.expression(StandardOperator.Recv,convert(ctx,1),convert(ctx,3),convert(ctx,5));   
      res.setGhost(true);
    } else if (match(ctx,"assume",null,";")){
      res=create.expression(StandardOperator.Assume,convert(ctx,1));
    }
    if (match(ctx,"create",null,";")){
      return create.special(ASTSpecial.Kind.CreateHistory,convert(ctx,1));
    }
    if (match(ctx,"create", null , "," , null , ";")){
      return create.special(ASTSpecial.Kind.CreateFuture,convert(ctx,1),convert(ctx,3));
    }
    if (match(ctx,"destroy",null,",",null,";")){
      return create.special(ASTSpecial.Kind.DestroyHistory,convert(ctx,1),convert(ctx,3));
    }
    if (match(ctx,"destroy",null,";")){
      return create.special(ASTSpecial.Kind.DestroyFuture,convert(ctx,1));
    }
    if (match(ctx,"split",null,",",null,",",null,",",null,",",null,";")){
      return create.special(ASTSpecial.Kind.SplitHistory,
          convert(ctx,1),convert(ctx,3),convert(ctx,5),convert(ctx,7),convert(ctx,9));
    }
    if (match(ctx,"merge",null,",",null,",",null,",",null,",",null,";")){
      return create.special(ASTSpecial.Kind.MergeHistory,
          convert(ctx,1),convert(ctx,3),convert(ctx,5),convert(ctx,7),convert(ctx,9));
    }
    if (match(ctx,"open",null,";")){
      return create.expression(StandardOperator.Open,convert(ctx,1));
    }
    if (match(ctx,"open",null,null,";")){
      ASTNode block=convert(ctx,2);
      res=create.expression(StandardOperator.Open,convert(ctx,1)).set_after((BlockStatement)block);
    }
    if (match(ctx,"close",null,";")){
      return create.expression(StandardOperator.Close,convert(ctx,1));
    }
    if (match(ctx,"transfer",null,";")){
      return create.special(ASTSpecial.Kind.Transfer,convert(ctx,1));
    }
    if (match(ctx,"csl_subject",null,";")){
      return create.special(ASTSpecial.Kind.CSLSubject,convert(ctx,1));
    }
    if (match(ctx,"with",null)){
        return create.special(ASTSpecial.Kind.With,convert(ctx,1));
      }
    if (match(ctx,"label",null)){
        return create.special(ASTSpecial.Kind.Label,convert(ctx,1));
      }
    if (match(ctx,"then",null)){
      return create.special(ASTSpecial.Kind.Then,convert(ctx,1));
    }
    if (match(ctx,"proof",null)){
      return create.special(ASTSpecial.Kind.Proof,convert(ctx,1));
    }
    if (match(ctx,"create",null,"BlockContext")){
        ASTNode wand=convert(ctx,1);
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(2));
        block.add_statement(create.expression(StandardOperator.QED,wand));
        return create.lemma(block);
      }
    if (match(ctx,"create","BlockContext",null,";")){
        ASTNode wand=convert(ctx,2);
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(1));
        block.add_statement(create.expression(StandardOperator.QED,wand));
        return create.lemma(block);
      }
    if (match(ctx,"create","BlockContext")){
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(1));
        return create.lemma(block);
      }
    if (match(ctx,"qed",null,";")){
        return create.expression(StandardOperator.QED,convert(ctx,1));
      }
    if (match(ctx,"apply",null,null,";")){
      OperatorExpression res2=create.expression(StandardOperator.Apply,convert(ctx,1));
      add_proof_script(res2,ctx.getChild(2));
      return res2;
    }
    if (match(ctx,"use",null,";")){
      return create.expression(StandardOperator.Use,convert(ctx,1));
    }
    if (match(ctx,"witness",null,";")){
      res=create.expression(StandardOperator.Witness,convert(ctx,1));
    }
    if (match(ctx,"atomic","(",null,")",null)){
      ASTNode args[]=convert_list((ParserRuleContext)ctx.getChild(2),",");
      BlockStatement block=(BlockStatement)convert(ctx,4);
      res=create.csl_atomic(block,args);
    }
    if (res!=null){
      res.setGhost(true);
    }
    return res;
  }

  @Override
  public ASTNode visitSpecificResourceExpression(SpecificResourceExpressionContext ctx) {
     return getResourceExpression(ctx);
  }

  @Override
  public ASTNode visitStatement(StatementContext ctx) {
    return getStatement(ctx);
  }

  @Override
  public ASTNode visitStatementExpression(StatementExpressionContext ctx) {
    return getExpression(ctx);
  }

  @Override
  public ASTNode visitStatementExpressionList(StatementExpressionListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStatementNoShortIf(StatementNoShortIfContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStatementWithoutTrailingSubstatement(
      StatementWithoutTrailingSubstatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStaticImportOnDemandDeclaration(
      StaticImportOnDemandDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStaticInitializer(StaticInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSuperclass(SuperclassContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSuperinterfaces(SuperinterfacesContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSwitchBlock(SwitchBlockContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSwitchBlockStatementGroup(
      SwitchBlockStatementGroupContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSwitchLabel(SwitchLabelContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSwitchLabels(SwitchLabelsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSwitchStatement(SwitchStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSynchronizedStatement(SynchronizedStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitThrows_(Throws_Context ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitThrowStatement(ThrowStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTryStatement(TryStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTryWithResourcesStatement(
      TryWithResourcesStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitType(TypeContext ctx) {
    return getType(ctx);
  }

  @Override
  public ASTNode visitTypeArgument(TypeArgumentContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeArgumentList(TypeArgumentListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeArguments(TypeArgumentsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeArgumentsOrDiamond(TypeArgumentsOrDiamondContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeBound(TypeBoundContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeDeclaration(TypeDeclarationContext ctx) {
    return convert_annotated(ctx);
  }

  @Override
  public ASTNode visitTypeImportOnDemandDeclaration(
      TypeImportOnDemandDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeName(TypeNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeParameter(TypeParameterContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeParameterList(TypeParameterListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeParameterModifier(TypeParameterModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeParameters(TypeParametersContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeVariable(TypeVariableContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannArrayType(UnannArrayTypeContext ctx) {
    Type t=checkType(convert(ctx,0));
    ParserRuleContext dims=(ParserRuleContext)ctx.getChild(1);
    int ofs=0;
    int N=dims.getChildCount();
    while(match(ofs,true,dims,"[","]")){
      t=create.primitive_type(Sort.Array,t);
      ofs+=2;
    }
    if (ofs!=N){
      hre.System.Fail("unimplemented array dim variant");
    }
    return t;
  }

  @Override
  public ASTNode visitUnannClassOrInterfaceType(
      UnannClassOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannClassType(UnannClassTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannClassType_lf_unannClassOrInterfaceType(
      UnannClassType_lf_unannClassOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannClassType_lfno_unannClassOrInterfaceType(
      UnannClassType_lfno_unannClassOrInterfaceTypeContext ctx) {
    String name=getIdentifier(ctx,0);
    ASTNode args[];
    if (ctx.getChildCount()==1){
      args=new ASTNode[0];
    } else {
      args=convert_list((ParserRuleContext)ctx.getChild(1),"<",",",">");
    }
    return create.class_type(name, args);
  }

  @Override
  public ASTNode visitUnannInterfaceType(UnannInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannInterfaceType_lf_unannClassOrInterfaceType(
      UnannInterfaceType_lf_unannClassOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannInterfaceType_lfno_unannClassOrInterfaceType(
      UnannInterfaceType_lfno_unannClassOrInterfaceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannPrimitiveType(UnannPrimitiveTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannReferenceType(UnannReferenceTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnannType(UnannTypeContext ctx) {
    return getType(ctx);
  }

  @Override
  public ASTNode visitUnannTypeVariable(UnannTypeVariableContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnaryExpression(UnaryExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnaryExpressionNotPlusMinus(
      UnaryExpressionNotPlusMinusContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableDeclarator(VariableDeclaratorContext ctx) {
    return getVariableDeclarator(ctx);
  }

  @Override
  public ASTNode visitVariableDeclaratorId(VariableDeclaratorIdContext ctx) {
    return getVariableDeclaratorId(ctx);
  }

  @Override
  public ASTNode visitVariableDeclaratorList(VariableDeclaratorListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableInitializer(VariableInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableInitializerList(VariableInitializerListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableModifier(VariableModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitWhileStatement(WhileStatementContext ctx) {
    assert match(ctx,"while","(",null,")",null);
    LoopStatement res=create.while_loop(convert(ctx,2),convert(ctx,4));
    scan_comments_after(res.get_after(), ctx.getChild(3));
    return res;
  }

  @Override
  public ASTNode visitWhileStatementNoShortIf(WhileStatementNoShortIfContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitWildcard(WildcardContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitWildcardBounds(WildcardBoundsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

}
