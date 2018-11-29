package vct.learn;

import vct.col.ast.ClassType;
import vct.col.ast.FunctionType;
import vct.col.ast.PrimitiveType;
import vct.col.ast.ProgramUnit;
import vct.col.ast.RecordType;
import vct.col.ast.TupleType;
import vct.col.ast.TypeExpression;

public class TypesCountVisitor extends SpecialCountVisitor {
  
  public TypesCountVisitor(ProgramUnit pu) {
    super(pu);
  }
  
  @Override
  public void visit(ClassType ct) {
    specialCounter.count(ct.getClass().getName());
    super.visit(ct);
  }
  
  @Override
  public void visit(FunctionType ft) {
    specialCounter.count(ft.getClass().getName());
    super.visit(ft);
  }
  
  @Override
  public void visit(PrimitiveType pt) {
    specialCounter.count(pt.getClass().getName(), pt.sort.toString());
    super.visit(pt);
  }
  
  @Override
  public void visit(RecordType rt) {
    specialCounter.count(rt.getClass().getName());
    super.visit(rt);
  }
  
  @Override
  public void visit(TupleType tt) {
    specialCounter.count(tt.getClass().getName());
    super.visit(tt);
  }
  
  @Override
  public void visit(TypeExpression te) {
    specialCounter.count(te.getClass().getName());
    super.visit(te);
  }
}
