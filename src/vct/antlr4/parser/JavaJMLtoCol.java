package vct.antlr4.parser;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.Parser;

import vct.col.ast.*;
import vct.java.printer.JavaSyntax;
import vct.parsers.JavaJMLParser.*;
import vct.parsers.*;
import vct.parsers.JavaJMLParser.FunctionDeclarationContext;
import vct.parsers.JavaJMLParser.LabeledExpressionContext;
import vct.parsers.JavaJMLParser.ProofScriptContext;
import vct.parsers.JavaJMLParser.ResourceExpressionContext;
import vct.parsers.JavaJMLParser.SpecificationDeclarationContext;
import vct.parsers.JavaJMLParser.SpecificationModifierContext;
import vct.parsers.JavaJMLParser.SpecificationPrimaryContext;
import vct.parsers.JavaJMLParser.SpecificationPrimitiveTypeContext;
import vct.parsers.JavaJMLParser.SpecificationSequenceContext;
import vct.parsers.JavaJMLParser.SpecificationStatementContext;
import vct.util.Syntax;

public class JavaJMLtoCol extends AbstractJavaToCol implements JavaJMLVisitor<ASTNode> {
  
  public static CompilationUnit convert(ParseTree tree, String file_name,BufferedTokenStream tokens,Parser parser) {
    JavaJMLtoCol visitor=new JavaJMLtoCol(JavaSyntax.getJavaJML(),file_name,tokens,parser);
    visitor.scan_to(visitor.unit,tree);
    return visitor.unit;
  }

  public JavaJMLtoCol(Syntax syntax, String filename, BufferedTokenStream tokens, Parser parser) {
    super(syntax, filename, tokens, parser, JavaJMLLexer.Identifier, JavaJMLLexer.COMMENT,JavaJMLLexer.class);
  }

  @Override
  public ASTNode visitAnnotation(AnnotationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationConstantRest(AnnotationConstantRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationMethodOrConstantRest(
      AnnotationMethodOrConstantRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationMethodRest(AnnotationMethodRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAnnotationName(AnnotationNameContext ctx) {
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
  public ASTNode visitAnnotationTypeElementRest(
      AnnotationTypeElementRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArguments(ArgumentsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayCreatorRest(ArrayCreatorRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArrayInitializer(ArrayInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
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
  public ASTNode visitClassCreatorRest(ClassCreatorRestContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassDeclaration(ClassDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassOrInterfaceModifier(
      ClassOrInterfaceModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitClassOrInterfaceType(ClassOrInterfaceTypeContext ctx) {
    return getClassOrInterfaceType(ctx);
  }

  @Override
  public ASTNode visitCompilationUnit(CompilationUnitContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantDeclarator(ConstantDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantExpression(ConstantExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstDeclaration(ConstDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstructorBody(ConstructorBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstructorDeclaration(ConstructorDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitContract(ContractContext ctx) {
    return getContract(ctx);
  }

  @Override
  public ASTNode visitContractClause(ContractClauseContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCreatedName(CreatedNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCreator(CreatorContext ctx) {
    return getCreator(ctx);
  }

  @Override
  public ASTNode visitDefaultValue(DefaultValueContext ctx) {
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
  public ASTNode visitElementValuePair(ElementValuePairContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitElementValuePairs(ElementValuePairsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnhancedForControl(EnhancedForControlContext ctx) {
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
  public ASTNode visitEnumConstantName(EnumConstantNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumConstants(EnumConstantsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumDeclaration(EnumDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExplicitGenericInvocation(
      ExplicitGenericInvocationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExplicitGenericInvocationSuffix(
      ExplicitGenericInvocationSuffixContext ctx) {
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
  public ASTNode visitFieldDeclaration(FieldDeclarationContext ctx) {
    return getVariableDeclaration((ParserRuleContext)ctx.getChild(1),convert(ctx,0));
  }

  @Override
  public ASTNode visitFinallyBlock(FinallyBlockContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitForControl(ForControlContext ctx) {
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
  public ASTNode visitForUpdate(ForUpdateContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericConstructorDeclaration(
      GenericConstructorDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericInterfaceMethodDeclaration(
      GenericInterfaceMethodDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericMethodDeclaration(
      GenericMethodDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitImportDeclaration(ImportDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInnerCreator(InnerCreatorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceBody(InterfaceBodyContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceBodyDeclaration(
      InterfaceBodyDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceDeclaration(InterfaceDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceMemberDeclaration(
      InterfaceMemberDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInterfaceMethodDeclaration(
      InterfaceMethodDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLastFormalParameter(LastFormalParameterContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLiteral(LiteralContext ctx) {
    return getLiteral(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclaration(
      LocalVariableDeclarationContext ctx) {
    return getLocalVariableDeclaration(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclarationStatement(
      LocalVariableDeclarationStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitMemberDeclaration(MemberDeclarationContext ctx) {
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
  public ASTNode visitModifier(ModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitNonWildcardTypeArguments(
      NonWildcardTypeArgumentsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitNonWildcardTypeArgumentsOrDiamond(
      NonWildcardTypeArgumentsOrDiamondContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageDeclaration(PackageDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPackageOrTypeName(PackageOrTypeNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitParExpression(ParExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimary(PrimaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPrimitiveType(PrimitiveTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitQualifiedName(QualifiedNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitQualifiedNameList(QualifiedNameListContext ctx) {
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
    return null;
  }

  @Override
  public ASTNode visitResources(ResourcesContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResourceSpecification(ResourceSpecificationContext ctx) {
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
    if (match(ctx,TypeContext.class,"{","}")){
      return create.expression(StandardOperator.Build,convert(ctx,0));
    }
    if (match(ctx,TypeContext.class,"{",ExpressionListContext.class,"}")){
      ASTNode tmp[]=convert_list((ParserRuleContext)ctx.getChild(2),",");
      ASTNode args[]=new ASTNode[tmp.length+1];
      args[0]=convert(ctx,0);
      for(int i=0;i<tmp.length;i++){
        args[i+1]=tmp[i];
      }
      return create.expression(StandardOperator.Build,args);
    }
    if (match(ctx,"*")){
      return create.reserved_name(ASTReserved.Any);
    }
    if (match(ctx,"(","\\forall",null,";",null,";",null,")")){
      return create.forall(convert(ctx,4),convert(ctx,6), getFormalParameter((ParserRuleContext) ctx.getChild(2)));
    }
    return null;
  }

  @Override
  public ASTNode visitStatement(StatementContext ctx) {
    return getStatement(ctx);
  }

  @Override
  public ASTNode visitStatementExpression(StatementExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSuperSuffix(SuperSuffixContext ctx) {
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
  public ASTNode visitType(TypeContext ctx) {
    return getType(ctx);
  }

  @Override
  public ASTNode visitTypeArgument(TypeArgumentContext ctx) {
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
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeList(TypeListContext ctx) {
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
  public ASTNode visitTypeParameters(TypeParametersContext ctx) {
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
  public ASTNode visitVariableDeclarators(VariableDeclaratorsContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableInitializer(VariableInitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitVariableModifier(VariableModifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationSequence(SpecificationSequenceContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationStatement(SpecificationStatementContext ctx) {
    if (match(ctx,"loop_invariant",null,";")){
      return create.special(ASTSpecial.Kind.Invariant,convert(ctx,1));
    }
    if (match(ctx,"set",null,"=",null,";")){
      return create.assignment(convert(ctx,1),convert(ctx,3));
    }
    if (match(ctx,"fold",null,";")){
      return create.expression(StandardOperator.Fold,convert(ctx,1));
    }
    if (match(ctx,"unfold",null,";")){
      return create.expression(StandardOperator.Unfold,convert(ctx,1));
    }
    if (match(ctx,"assert",null,";")){
      return create.expression(StandardOperator.Assert,convert(ctx,1));
    }
    if (match(ctx,"assume",null,";")){
      return create.expression(StandardOperator.Assume,convert(ctx,1));
    }
    if (match(ctx,"open",null,";")){
      return create.expression(StandardOperator.Open,convert(ctx,1));
    }
    if (match(ctx,"open",null,null,";")){
      ASTNode block=convert(ctx,2);
      OperatorExpression res=create.expression(StandardOperator.Open,convert(ctx,1));
      res.set_after((BlockStatement)block);
      return res;
    }
    if (match(ctx,"close",null,";")){
      return create.expression(StandardOperator.Close,convert(ctx,1));
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
    if (match(ctx,"create",null,BlockContext.class)){
        ASTNode wand=convert(ctx,1);
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(2));
        block.add_statement(create.expression(StandardOperator.QED,wand));
        return create.lemma(block);
      }
    if (match(ctx,"create",BlockContext.class,null,";")){
        ASTNode wand=convert(ctx,2);
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(1));
        block.add_statement(create.expression(StandardOperator.QED,wand));
        return create.lemma(block);
      }
    if (match(ctx,"create",BlockContext.class)){
        BlockStatement block=getBlock((ParserRuleContext)ctx.getChild(1));
        return create.lemma(block);
      }
    if (match(ctx,"qed",null,";")){
        return create.expression(StandardOperator.QED,convert(ctx,1));
      }
    if (match(ctx,"apply",null,null,";")){
      OperatorExpression res=create.expression(StandardOperator.Apply,convert(ctx,1));
      add_proof_script(res,ctx.getChild(2));
      return res;
    }
    if (match(ctx,"use",null,";")){
      return create.expression(StandardOperator.Use,convert(ctx,1));
    }
    if (match(ctx,"witness",null,";")){
      ASTNode res=create.expression(StandardOperator.Witness,convert(ctx,1));
      return res;
    }
    return null;
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

  @Override
  public ASTNode visitSpecificationDeclaration(
      SpecificationDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFunctionDeclaration(FunctionDeclarationContext ctx) {
    Contract contract=null;
    int i=0;
    if (match(0,true,ctx,ContractContext.class)){
      contract=(Contract)convert(ctx,0);
      i=1;
    }
    while(match(i,true,ctx,ModifierContext.class)){
      // TODO keep context!
      i++;
    }
    Type returns=checkType(convert(ctx,i));
    String name=getIdentifier(ctx,i+1);
    hre.System.Debug("function %s, contract %s",name,contract);
    DeclarationStatement args[]=getFormalParameters(ctx.getChild(i+2));
    ASTNode body=null;
    if (match(i+3,false,ctx,"=",null,";")){
      body=convert(ctx,i+4);
    }
    Method res=create.function_decl(returns, contract, name, args, body);
    hre.System.Debug("function %s, contract %s",res.name,res.getContract());
    return res;
  }

  @Override
  public ASTNode visitSpecificationPrimitiveType(
      SpecificationPrimitiveTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLabeledExpression(LabeledExpressionContext ctx) {
    return getExpression(ctx);
  }

  @Override
  public ASTNode visitProofScript(ProofScriptContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

}
