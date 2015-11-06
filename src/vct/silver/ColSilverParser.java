package vct.silver;

import hre.HREError;
import hre.ast.MessageOrigin;
import hre.ast.Origin;

import java.io.File;
import java.util.List;
import java.util.Properties;

import vct.col.ast.ASTClass;
import vct.col.ast.ASTDeclaration;
import vct.col.ast.ASTNode;
import vct.col.ast.AxiomaticDataType;
import vct.col.ast.DeclarationStatement;
import vct.col.ast.Method;
import vct.col.ast.ProgramUnit;
import vct.col.ast.Type;
import vct.error.VerificationError;
import viper.api.SilverVerifier;
import viper.api.ViperError;

public class ColSilverParser implements vct.col.util.Parser {

  @Override
  public ProgramUnit parse(File file) {
    return run_test(file);
  }
  
  public static <T,E,S,Decl,DFunc,DAxiom,Program>
  ProgramUnit run_test(File f){
    SilverVerifier<Origin,VerificationError,T,E,S,Decl,DFunc,DAxiom,Program> verifier=
        SilverBackend.getVerifier("silicon");
    Program program=verifier.parse_program(f.toString());
    if (program==null){
      throw new HREError("parsing %s failed",f);
    }
    SilverVerifier<Origin, VerificationError, Type, ASTNode, ASTNode, DeclarationStatement, Method, AxiomaticDataType, ProgramUnit> verifier2=
        new VerCorsVerifier();
    ProgramUnit tmp=verifier.convert(verifier2, program);
    ProgramUnit res=new ProgramUnit();
    ASTClass ref=new ASTClass("Ref",ASTClass.ClassKind.Record);
    ref.setOrigin(new MessageOrigin("implicit Ref for %s",f));
    res.add(ref);
    for(ASTNode d:tmp){
      if (d instanceof DeclarationStatement){
        ref.add_dynamic(d);
      } else {
        res.add(d);
      }
    }
    return res;
  }
  
}
