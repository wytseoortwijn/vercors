package vct.col.rewrite;

import vct.col.ast.*;

/**
 * Rewrite pass that rewrites null values to none where they should be converted. This happens when e.g. null is
 * assigned to an array in Java.
 */
public class ArrayNullValues extends AbstractRewriter {
    /**
     * Marker label that is added to any AST Node which must be cast to an option via conversion:
     * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html
     * Applicable are assignment, method invocation and casting conversion.
     */


    public ArrayNullValues(ProgramUnit source) {
        super(source);
    }

    @Override
    public void visit(NameExpression exp) {
        if(exp.isReserved(ASTReserved.Null) && exp.getType().isPrimitive(PrimitiveSort.Option)) {
            result = new NameExpression(ASTReserved.OptionNone);
        } else {
            super.visit(exp);
        }
    }

    @Override
    public void visit(OperatorExpression exp) {
        switch(exp.operator()) {
            case Get:
                break;
            case Set:
                // TODO?
                break;

            case UPlus:
            case UMinus:
            case Exp:
            case Plus:
            case Minus:
            case Mult:
            case Div:
            case Mod:
            case BitAnd:
            case BitOr:
            case BitXor:
            case BitNot:
            case And:
            case Or:
            case Not:
            case Implies:
            case IFF:
            case LeftShift:
            case RightShift:
            case UnsignedRightShift:
                break;

            case EQ:
            case NEQ:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(0).setType(exp.getType());
                    exp.arg(1).setType(exp.getType());
                }
                break;

            case GT:
            case GTE:
            case LT:
            case LTE:
                break;

            case ITE:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(1).setType(exp.getType());
                    exp.arg(2).setType(exp.getType());
                }
                break;

            case TypeOf:
                // TODO?
                break;
            case Instance:
                // TODO?
                break;
            case Cast:
                // TODO?
                break;
            case SubType:
            case SuperType:
                // TODO?
                break;
            case InterSect:
                // TODO?
                break;

            case Assign:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(1).setType(exp.getType());
                }
                break;

            case MulAssign:
            case DivAssign:
            case RemAssign:
            case AddAssign:
            case SubAssign:
            case ShlAssign:
            case ShrAssign:
            case SShrAssign:
            case AndAssign:
            case XorAssign:
            case OrAssign:
            case PreIncr:
            case PreDecr:
            case PostIncr:
            case PostDecr:
                break;

            case Star:
            case Wand:
                break;

            case Perm:
            case Value:
            case HistoryPerm:
            case ActionPerm:
            case ArrayPerm:
                break;

            case PointsTo:
                // TODO
                break;

            case StructSelect:
                break;
            case StructDeref:
                break;
            case AddsTo:
                break;
            case Subscript:
                break;

            case Old:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(0).setType(exp.getType());
                }
                break;

            case New:
                break;
            case NewSilver:
                break;
            case NewArray:
                break;

            case Length:
                break;
            case Size:
                break;

            case Cons:
            case Drop:
            case Take:
            case Append:
            case Head:
            case Tail:
                break;

            case Member:
                // TODO?
                break;
            case AddrOf:
                break;
            case SizeOf:
                break;

            case BindOutput:
                break;
            case Wrap:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(0).setType(exp.getType());
                }
                break;
            case CurrentPerm:
                break;
            case Scale:
                break;
            case RangeSeq:
                break;
            case Unfolding:
                break;
            case LeftMerge:
                break;
            case History:
                break;
            case Future:
                break;
            case AbstractState:
                break;
            case IndependentOf:
                break;
            case Contribution:
                break;
            case ReducibleSum:
                break;
            case ReducibleMax:
                break;
            case ReducibleMin:
                break;
            case Held:
                break;
            case Identity:
                if(exp.getType().isPrimitive(PrimitiveSort.Option)) {
                    exp.arg(0).setType(exp.getType());
                }
                break;
            case Indirection:
                break;
            case IterationOwner:
                break;
            case PVLidleToken:
                break;
            case PVLjoinToken:
                break;
            case OptionSome:
                break;
            case OptionGet:
                break;
            case ValidArray:
            case ValidMatrix:
                // this should probably be type-checked to be a proper array, not an option.
                break;
            case Values:
                // this is type-checked to be a proper array
                break;
            case FoldPlus:
                break;
            case VectorRepeat:
                break;
            case VectorCompare:
                break;
            case MatrixSum:
                break;
            case MatrixRepeat:
                break;
            case MatrixCompare:
                break;
        }

        super.visit(exp);
    }
}
