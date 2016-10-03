package vct.logging;

import java.util.ArrayList;

import hre.HREError;
import hre.ast.Origin;
import viper.api.ViperError;
import static vct.logging.VerCorsError.ErrorCode.*;
import static vct.logging.VerCorsError.SubCode.*;

public class VerCorsError extends AbstractMessage {

  public static enum ErrorCode {
    AssertFailed,
    ExhaleFailed,
    InvariantNotEstablished,
    InvariantBroken,
    PostConditionFailed,
    UnspecifiedError,
    MagicWandUnproven,
    MagicWandPreCondition,
    NotWellFormed,
    ApplicationPreCondition,
    CallPreCondition,
    AssignmentFailed
  }
  
  public static enum SubCode {
    AssertionFalse,
    DivisionByZero,
    InsufficientPermission,
    UnspecifiedCause
  }
  
  
  
  public final ErrorCode code;
  
  public final SubCode sub;
  
  public final Origin main;
  
  public final ArrayList<Origin> aux=new ArrayList<Origin>();
  
  public VerCorsError(ViperError<Origin> e){
    fatal=true;
    String err[]=e.getError(0).split(":");
    switch(err[0]){
    case "postcondition.violated":
      code=PostConditionFailed;
      break;
    case "exhale.failed":
      code=ExhaleFailed;
      break;
    case "assert.failed":
      code=AssertFailed;
      break;
    case "assignment.failed":
      code=AssignmentFailed;
      break;
    case "predicate.not.wellformed":
    case "not.wellformed":
      code=NotWellFormed;
      break;
    case "application.precondition":
      code=ApplicationPreCondition;
      break;
    case "call.precondition":
      code=CallPreCondition;
      break;
    default:
      throw new HREError("unspecified error %s%n",err[0]);
      //code=UnspecifiedError;
      //break;
    }
    switch(err[1]){
    case "assertion.false":
      sub=AssertionFalse;
      break;
    case "division.by.zero":
      sub=DivisionByZero;
      break;
    case "insufficient.permission":
      sub=InsufficientPermission;
      break;
    case "receiver.not.injective":
      sub=InsufficientPermission;
      break;
    default:
      throw new HREError("unspecified cause %s%n",err[1]);
      //sub=UnspecifiedCause;
      //break;    
    }
    main=e.getOrigin(0);
    for(int i=1;i<e.getExtraCount();i++){
      aux.add(e.getOrigin(i));
    }
  }
  
  public VerCorsError(ErrorCode code, SubCode sub,Origin origin, ArrayList<Origin> aux) {
    this.code=code;
    this.sub=sub;
    this.main=origin;
    this.aux.addAll(aux);
  }

  @Override
  public void accept(MessageVisitor visitor){
    visitor.visit(this);
  }

}
