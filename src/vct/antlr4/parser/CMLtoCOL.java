package vct.antlr4.parser;

import java.util.ArrayList;

import hre.ast.MessageOrigin;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTree;

import vct.clang.printer.CSyntax;
import vct.col.ast.*;
import vct.parsers.*;
import vct.parsers.CMLParser.AbstractDeclaratorContext;
import vct.parsers.CMLParser.AdditiveExpressionContext;
import vct.parsers.CMLParser.AlignmentSpecifierContext;
import vct.parsers.CMLParser.AndExpressionContext;
import vct.parsers.CMLParser.ArgumentExpressionListContext;
import vct.parsers.CMLParser.AssignmentExpressionContext;
import vct.parsers.CMLParser.AssignmentOperatorContext;
import vct.parsers.CMLParser.AtomicTypeSpecifierContext;
import vct.parsers.CMLParser.BlockItemContext;
import vct.parsers.CMLParser.BlockItemListContext;
import vct.parsers.CMLParser.CastExpressionContext;
import vct.parsers.CMLParser.CompilationUnitContext;
import vct.parsers.CMLParser.CompoundStatementContext;
import vct.parsers.CMLParser.ConditionalExpressionContext;
import vct.parsers.CMLParser.ConstantExpressionContext;
import vct.parsers.CMLParser.ContractClauseContext;
import vct.parsers.CMLParser.ContractContext;
import vct.parsers.CMLParser.DeclarationContext;
import vct.parsers.CMLParser.DeclarationListContext;
import vct.parsers.CMLParser.DeclarationSpecifierContext;
import vct.parsers.CMLParser.DeclarationSpecifiers2Context;
import vct.parsers.CMLParser.DeclarationSpecifiersContext;
import vct.parsers.CMLParser.DeclaratorContext;
import vct.parsers.CMLParser.DesignationContext;
import vct.parsers.CMLParser.DesignatorContext;
import vct.parsers.CMLParser.DesignatorListContext;
import vct.parsers.CMLParser.DirectAbstractDeclaratorContext;
import vct.parsers.CMLParser.DirectDeclaratorContext;
import vct.parsers.CMLParser.EnumSpecifierContext;
import vct.parsers.CMLParser.EnumerationConstantContext;
import vct.parsers.CMLParser.EnumeratorContext;
import vct.parsers.CMLParser.EnumeratorListContext;
import vct.parsers.CMLParser.EqualityExpressionContext;
import vct.parsers.CMLParser.ExclusiveOrExpressionContext;
import vct.parsers.CMLParser.ExpressionContext;
import vct.parsers.CMLParser.ExpressionListContext;
import vct.parsers.CMLParser.ExpressionStatementContext;
import vct.parsers.CMLParser.ExternalDeclarationContext;
import vct.parsers.CMLParser.FunctionDefinitionContext;
import vct.parsers.CMLParser.FunctionSpecifierContext;
import vct.parsers.CMLParser.GccAttributeContext;
import vct.parsers.CMLParser.GccAttributeListContext;
import vct.parsers.CMLParser.GccAttributeSpecifierContext;
import vct.parsers.CMLParser.GccDeclaratorExtensionContext;
import vct.parsers.CMLParser.GenericAssocListContext;
import vct.parsers.CMLParser.GenericAssociationContext;
import vct.parsers.CMLParser.GenericSelectionContext;
import vct.parsers.CMLParser.IdentifierListContext;
import vct.parsers.CMLParser.InclusiveOrExpressionContext;
import vct.parsers.CMLParser.InitDeclaratorContext;
import vct.parsers.CMLParser.InitDeclaratorListContext;
import vct.parsers.CMLParser.InitializerContext;
import vct.parsers.CMLParser.InitializerListContext;
import vct.parsers.CMLParser.IterationStatementContext;
import vct.parsers.CMLParser.JumpStatementContext;
import vct.parsers.CMLParser.LabeledExpressionContext;
import vct.parsers.CMLParser.LabeledStatementContext;
import vct.parsers.CMLParser.LogicalAndExpressionContext;
import vct.parsers.CMLParser.LogicalOrExpressionContext;
import vct.parsers.CMLParser.MultiplicativeExpressionContext;
import vct.parsers.CMLParser.NestedParenthesesBlockContext;
import vct.parsers.CMLParser.ParameterDeclarationContext;
import vct.parsers.CMLParser.ParameterListContext;
import vct.parsers.CMLParser.ParameterTypeListContext;
import vct.parsers.CMLParser.PointerContext;
import vct.parsers.CMLParser.PostfixExpressionContext;
import vct.parsers.CMLParser.PrimaryExpressionContext;
import vct.parsers.CMLParser.PureFunctionDeclarationContext;
import vct.parsers.CMLParser.RelationalExpressionContext;
import vct.parsers.CMLParser.ResourceExpressionContext;
import vct.parsers.CMLParser.SelectionStatementContext;
import vct.parsers.CMLParser.ShiftExpressionContext;
import vct.parsers.CMLParser.SpecificResourceExpressionContext;
import vct.parsers.CMLParser.SpecificationDeclarationContext;
import vct.parsers.CMLParser.SpecificationPrimaryContext;
import vct.parsers.CMLParser.SpecificationPrimitiveTypeContext;
import vct.parsers.CMLParser.SpecifierQualifierListContext;
import vct.parsers.CMLParser.StatementContext;
import vct.parsers.CMLParser.StaticAssertDeclarationContext;
import vct.parsers.CMLParser.StorageClassSpecifierContext;
import vct.parsers.CMLParser.StructDeclarationContext;
import vct.parsers.CMLParser.StructDeclarationListContext;
import vct.parsers.CMLParser.StructDeclaratorContext;
import vct.parsers.CMLParser.StructDeclaratorListContext;
import vct.parsers.CMLParser.StructOrUnionContext;
import vct.parsers.CMLParser.StructOrUnionSpecifierContext;
import vct.parsers.CMLParser.TranslationUnitContext;
import vct.parsers.CMLParser.TypeContext;
import vct.parsers.CMLParser.TypeNameContext;
import vct.parsers.CMLParser.TypeQualifierContext;
import vct.parsers.CMLParser.TypeQualifierListContext;
import vct.parsers.CMLParser.TypeSpecifierContext;
import vct.parsers.CMLParser.TypedefNameContext;
import vct.parsers.CMLParser.UnaryExpressionContext;
import vct.parsers.CMLParser.UnaryOperatorContext;
import vct.parsers.CMLParser.SpecificationStatementContext;
import vct.parsers.CMLParser.SpecificationSequenceContext;
import vct.util.Configuration;
import vct.util.Syntax;   

/**
 * Convert CML (C Modeling Language) parse trees to COL.
 *
 * This class contains the conversions for parse tree nodes,
 * which are unique to CML or have to be handled differently
 * from the same node for C.
 * 
 * @author <a href="mailto:s.c.c.blom@utwente.nl">Stefan Blom</a>
*/
public class CMLtoCOL extends AbstractCtoCOL implements CMLVisitor<ASTNode> {

  public static TempSequence convert(ParseTree tree, String file_name,BufferedTokenStream tokens,org.antlr.v4.runtime.Parser parser) {
    TempSequence unit=new TempSequence();
    CMLtoCOL visitor=new CMLtoCOL(CSyntax.getCML(),file_name,tokens,parser,CMLLexer.Identifier,CMLLexer.COMMENT);
    visitor.scan_to(unit,tree);
    return unit;
  }

  public CMLtoCOL(Syntax syntax, String filename, BufferedTokenStream tokens,
      Parser parser, int identifier, int comment
  ) {
    super(syntax, filename, tokens, parser, identifier, CMLLexer.class);
  }

  @Override
  public ASTNode visitAbstractDeclarator(AbstractDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAdditiveExpression(AdditiveExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAlignmentSpecifier(AlignmentSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitAndExpression(AndExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitArgumentExpressionList(ArgumentExpressionListContext ctx) {
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
  public ASTNode visitAtomicTypeSpecifier(AtomicTypeSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitBlockItem(BlockItemContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitBlockItemList(BlockItemListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCastExpression(CastExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCompilationUnit(CompilationUnitContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitCompoundStatement(CompoundStatementContext ctx) {
    return getCompoundStatement(ctx);
  }

  @Override
  public ASTNode visitConditionalExpression(ConditionalExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitConstantExpression(ConstantExpressionContext ctx) {
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
  public ASTNode visitDeclaration(DeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDeclarationList(DeclarationListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDeclarationSpecifier(DeclarationSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDeclarationSpecifiers(DeclarationSpecifiersContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDeclarationSpecifiers2(DeclarationSpecifiers2Context ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDeclarator(DeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDesignation(DesignationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDesignator(DesignatorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDesignatorList(DesignatorListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDirectAbstractDeclarator(
      DirectAbstractDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitDirectDeclarator(DirectDeclaratorContext ctx) {
    return getDirectDeclarator(ctx);
  }

  @Override
  public ASTNode visitEnumerationConstant(EnumerationConstantContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumerator(EnumeratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumeratorList(EnumeratorListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEnumSpecifier(EnumSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitEqualityExpression(EqualityExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }//

  @Override
  public ASTNode visitExclusiveOrExpression(ExclusiveOrExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExpression(ExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }// //

  @Override
  public ASTNode visitExpressionStatement(ExpressionStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitExternalDeclaration(ExternalDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFunctionDefinition(FunctionDefinitionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitFunctionSpecifier(FunctionSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGccAttribute(GccAttributeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGccAttributeList(GccAttributeListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGccAttributeSpecifier(GccAttributeSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGccDeclaratorExtension(GccDeclaratorExtensionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericAssociation(GenericAssociationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericAssocList(GenericAssocListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitGenericSelection(GenericSelectionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitIdentifierList(IdentifierListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInclusiveOrExpression(InclusiveOrExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInitDeclarator(InitDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInitDeclaratorList(InitDeclaratorListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInitializer(InitializerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitInitializerList(InitializerListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitIterationStatement(IterationStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitJumpStatement(JumpStatementContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLabeledStatement(LabeledStatementContext ctx) {
    return getLabeledStatement(ctx);
  }

  @Override
  public ASTNode visitLogicalAndExpression(LogicalAndExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLogicalOrExpression(LogicalOrExpressionContext ctx) {
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
  public ASTNode visitNestedParenthesesBlock(NestedParenthesesBlockContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitParameterDeclaration(ParameterDeclarationContext ctx) {
    return getParameterDeclaration(ctx);
  }

  @Override
  public ASTNode visitParameterList(ParameterListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitParameterTypeList(ParameterTypeListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPointer(PointerContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitPostfixExpression(PostfixExpressionContext ctx) {
    return visitPrimaryExpression((ParserRuleContext)ctx);
  }

  @Override
  public ASTNode visitPrimaryExpression(PrimaryExpressionContext ctx) {
    return visitPrimaryExpression((ParserRuleContext)ctx);
  }

  @Override
  public ASTNode visitRelationalExpression(RelationalExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSelectionStatement(SelectionStatementContext ctx) {
    return getSelectionStatement(ctx);
  }

  @Override
  public ASTNode visitShiftExpression(ShiftExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override  
  public ASTNode visitSpecificationSequence(SpecificationSequenceContext ctx) {//DRB --Added	  
	return null;
  }
  //
  @Override
  public ASTNode visitSpecificationStatement(SpecificationStatementContext ctx) {//DRB --Added	    

	    ASTNode res=null;	    

	  	if (match(ctx,"loop_invariant",null,";")){	      
	      res= create.special_decl(ASTSpecialDeclaration.Kind.Invariant,convert(ctx,1));
	    }
	    else if (match(ctx,"send",null,"to",null,",",null,";")){//DRB	    	
		    res= create.expression(StandardOperator.Send,convert(ctx,1),convert(ctx,3),convert(ctx,5));		
		    res.setGhost(true);
  		} else if (match(ctx,"recv",null,"from",null,",",null,";")){//DRB
  			
		    res= create.expression(StandardOperator.Recv,convert(ctx,1),convert(ctx,3),convert(ctx,5));		
		    res.setGhost(true);
  		}
	    else if (match(ctx,"assert",null,";")){ // DRB
  			res=create.expression(StandardOperator.Assert,convert(ctx,1));
  			res.setGhost(true);
  		} else if (match(ctx,"fold",null,";")){//DRB
  			res=create.expression(StandardOperator.Fold,convert(ctx,1));
  			res.setGhost(true);
  		} else if (match(ctx,"unfold",null,";")){//DRB
  			res=create.expression(StandardOperator.Unfold,convert(ctx,1));
  			res.setGhost(true);
  		}
	    return res;
  }
  
  @Override
  public ASTNode visitSpecifierQualifierList(SpecifierQualifierListContext ctx) {
    // TODO Auto-generated method stub	  
    return null;
  }

  @Override
  public ASTNode visitStatement(StatementContext ctx) {
    // TODO Auto-generated method stub
	  return null;
  }

  @Override
  public ASTNode visitStaticAssertDeclaration(StaticAssertDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStorageClassSpecifier(StorageClassSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructDeclaration(StructDeclarationContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructDeclarationList(StructDeclarationListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructDeclarator(StructDeclaratorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructDeclaratorList(StructDeclaratorListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructOrUnion(StructOrUnionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitStructOrUnionSpecifier(StructOrUnionSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTranslationUnit(TranslationUnitContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypedefName(TypedefNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeName(TypeNameContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeQualifier(TypeQualifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeQualifierList(TypeQualifierListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitTypeSpecifier(TypeSpecifierContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnaryExpression(UnaryExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitUnaryOperator(UnaryOperatorContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificResourceExpression(
      SpecificResourceExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitResourceExpression(ResourceExpressionContext ctx) {
    // TODO Auto-generated method stub	  
    return getResourceExpression(ctx); //DRB
  }
  public ASTNode getResourceExpression(ParserRuleContext ctx) {//DRB
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

  @Override
  public ASTNode visitExpressionList(ExpressionListContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitType(TypeContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitLabeledExpression(LabeledExpressionContext ctx) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ASTNode visitSpecificationPrimary(SpecificationPrimaryContext ctx) {
    return getSpecificationPrimary(ctx);
  }

  @Override
  public ASTNode visitSpecificationPrimitiveType(
      SpecificationPrimitiveTypeContext ctx) {
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
  public ASTNode visitPureFunctionDeclaration(PureFunctionDeclarationContext ctx) {
    hre.System.Warning("pure function");
    Type t=checkType(convert(ctx,0));
    ASTNode expr=convert(ctx,3);
    int ofs=1;
    String name=null;
    ArrayList<DeclarationStatement> args=new ArrayList<DeclarationStatement>();
    if (match((DeclaratorContext)ctx.getChild(ofs),"DirectDeclaratorContext")){
      DirectDeclaratorContext decl_ctx=(DirectDeclaratorContext)((DeclaratorContext)ctx.getChild(ofs)).getChild(0);
      if (match(decl_ctx,null,"(","ParameterTypeListContext",")")){
        enter(decl_ctx);
        name=getIdentifier(decl_ctx, 0);
        ParserRuleContext arg_ctx=(ParserRuleContext)decl_ctx.getChild(2);
        convert_parameters(args, arg_ctx);
        leave(decl_ctx,null);
      } else {
        return null;
      }
    } else {
      throw hre.System.Failure("unknown declarator%ntree: %s",ctx.getChild(ofs).toStringTree(parser));
    }
    hre.System.Warning("? %s (?) = %s",name,Configuration.getDiagSyntax().print(expr));
    return create.function_decl(t, null, name, args.toArray(new DeclarationStatement[0]), expr);
  }


}
