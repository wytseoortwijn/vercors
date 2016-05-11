package vct.antlr4.parser;

import java.util.ArrayList;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.syntax.JavaSyntax;
import vct.col.syntax.Syntax;
import vct.parsers.JavaParser.*;
import vct.parsers.*;
import vct.parsers.JavaParser.ClassBodyContext;
import vct.parsers.JavaParser.ClassBodyDeclarationContext;
import vct.parsers.JavaParser.SpecificationModifierContext;
import vct.parsers.JavaParser.SpecificationPrimaryContext;
import vct.parsers.JavaParser.SpecificationPrimitiveTypeContext;
import vct.parsers.JavaParser.SpecificationStatementContext;
import vct.util.Configuration;

/**
 * Convert Java parse trees to COL.
 *
 * @author <a href="mailto:s.c.c.blom@utwente.nl">Stefan Blom</a>
*/
public class JavaToCol extends AbstractJavaToCol implements JavaVisitor<ASTNode> {

  public static ProgramUnit convert(ParseTree tree, String file_name,BufferedTokenStream tokens,Parser parser) {
    ProgramUnit unit=new ProgramUnit();
    JavaToCol visitor=new JavaToCol(unit,JavaSyntax.getJava(),file_name,tokens,parser);
    visitor.scan_to(unit,tree);
    return unit;
  }

  public JavaToCol(ASTSequence<?> unit,Syntax syntax, String filename, BufferedTokenStream tokens,
      Parser parser) {
    super(unit,syntax, filename, tokens, parser, JavaLexer.Identifier, JavaLexer.COMMENT,JavaLexer.class);
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
    return getArrayInitializer(ctx);
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
    return getClassDeclaration(ctx);
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
  public ASTNode visitConstantDeclarator(ConstantDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantExpression(ConstantExpressionContext ctx) {
    return getExpression(ctx);
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
    return getConstructorDeclaration(ctx);
  }

  @Override
  public ASTNode visitCreatedName(CreatedNameContext ctx) {
    return getCreatedName(ctx);
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
    return getImportDeclaration(ctx);
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
    return getClassBodyDeclaration(ctx);
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
  public ASTNode visitLastFormalParameter(LastFormalParameterContext ctx) {
    return getLastFormalParameter(ctx);
  }

  @Override
  public ASTNode visitLiteral(LiteralContext ctx) {
    return getLiteral(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclaration(LocalVariableDeclarationContext ctx) {
    return getLocalVariableDeclaration(ctx);
  }

  @Override
  public ASTNode visitLocalVariableDeclarationStatement(
      LocalVariableDeclarationStatementContext ctx) {
    return convert(ctx,0);
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
  public ASTNode visitParExpression(ParExpressionContext ctx) {
    return convert(ctx,1);
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
    return getQualifiedName(ctx);
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
  public ASTNode visitStatement(StatementContext ctx) {
    return getStatement(ctx);
  }

  @Override
  public ASTNode visitStatementExpression(StatementExpressionContext ctx) {
    return getExpression(ctx);
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
    return convert_annotated(ctx);
  }

  @Override
  public ASTNode visitTypeList(TypeListContext ctx) {
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
  public ASTNode visitSpecificationPrimary(SpecificationPrimaryContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationPrimitiveType(
      SpecificationPrimitiveTypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationStatement(SpecificationStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }


}
