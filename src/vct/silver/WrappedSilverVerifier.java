package vct.silver;
import java.lang.reflect.*;

/** Wrapper for SilverVerifier implementations using reflection.  
 *  Thus it can wrap both older and newer versions without linker errors.
 *  This class is generated code! Do not modify!
 */
class WrappedSilverVerifier<O extends java.lang.Object,Err extends java.lang.Object,T extends java.lang.Object,E extends java.lang.Object,S extends java.lang.Object,Decl extends java.lang.Object,DFunc extends java.lang.Object,DAxiom extends java.lang.Object,P extends java.lang.Object> implements SilverVerifier<O,Err,T,E,S,Decl,DFunc,DAxiom,P> {
private Method m0;
private Method m1;
private Method m2;
private Method m3;
private Method m4;
private Method m5;
private Method m6;
private Method m7;
private Method m8;
private Method m9;
private Method m10;
private Method m11;
private Method m12;
private Method m13;
private Method m14;
private Method m15;
private Method m16;
private Method m17;
private Method m18;
private Method m19;
private Method m20;
private Method m21;
private Method m22;
private Method m23;
private Method m24;
private Method m25;
private Method m26;
private Method m27;
private Method m28;
private Method m29;
private Method m30;
private Method m31;
private Method m32;
private Method m33;
private Method m34;
private Method m35;
private Method m36;
private Method m37;
private Method m38;
private Method m39;
private Method m40;
private Method m41;
private Method m42;
private Method m43;
private Method m44;
private Method m45;
private Method m46;
private Method m47;
private Method m48;
private Method m49;
private Method m50;
private Method m51;
private Method m52;
private Method m53;
private Method m54;
private Method m55;
private Method m56;
private Method m57;
private Method m58;
private Method m59;
private Method m60;
private Method m61;
private Method m62;
private Method m63;
private Method m64;
private Method m65;
private Method m66;
private Method m67;
private Method m68;
private Method m69;
private Method m70;
private Method m71;
private Method m72;
private Method m73;
private Method m74;
private Method m75;
private Method m76;
private Method m77;
private Method m78;
private Method m79;
private Method m80;
private Method m81;
private Method m82;
private Method m83;
private final Object obj;
public WrappedSilverVerifier(Object obj){
  this.obj=obj;
  Class cl=obj.getClass();
  try {
    m0=cl.getMethod("Bag",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m1=cl.getMethod("Bool");
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m2=cl.getMethod("Constant",java.lang.Object.class,int.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m3=cl.getMethod("Constant",java.lang.Object.class,boolean.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m4=cl.getMethod("FieldAccess",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m5=cl.getMethod("Int");
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m6=cl.getMethod("List",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m7=cl.getMethod("Perm");
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m8=cl.getMethod("Ref");
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m9=cl.getMethod("Set",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m10=cl.getMethod("add",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m11=cl.getMethod("add_adt",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.util.List.class,java.util.List.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m12=cl.getMethod("add_field",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m13=cl.getMethod("add_function",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.util.List.class,java.lang.Object.class,java.util.List.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m14=cl.getMethod("add_method",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.util.List.class,java.util.List.class,java.util.List.class,java.util.List.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m15=cl.getMethod("add_predicate",java.lang.Object.class,java.lang.Object.class,java.lang.String.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m16=cl.getMethod("and",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m17=cl.getMethod("any_set_contains",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m18=cl.getMethod("append",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m19=cl.getMethod("assert_",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m20=cl.getMethod("assignment",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m21=cl.getMethod("block",java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m22=cl.getMethod("cond",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m23=cl.getMethod("daxiom",java.lang.Object.class,java.lang.String.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m24=cl.getMethod("decl",java.lang.Object.class,java.lang.String.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m25=cl.getMethod("dfunc",java.lang.Object.class,java.lang.String.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m26=cl.getMethod("div",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m27=cl.getMethod("domain_call",java.lang.Object.class,java.lang.String.class,java.util.List.class,java.util.Map.class,java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m28=cl.getMethod("domain_type",java.lang.String.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m29=cl.getMethod("drop",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m30=cl.getMethod("empty_bag",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m31=cl.getMethod("empty_seq",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m32=cl.getMethod("empty_set",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m33=cl.getMethod("eq",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m34=cl.getMethod("exhale",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m35=cl.getMethod("exists",java.lang.Object.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m36=cl.getMethod("explicit_bag",java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m37=cl.getMethod("explicit_seq",java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m38=cl.getMethod("explicit_set",java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m39=cl.getMethod("field_access",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m40=cl.getMethod("fold",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m41=cl.getMethod("forall",java.lang.Object.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m42=cl.getMethod("frac",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m43=cl.getMethod("function_call",java.lang.Object.class,java.lang.String.class,java.util.List.class,java.lang.Object.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m44=cl.getMethod("getOrigin",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m45=cl.getMethod("goto_",java.lang.Object.class,java.lang.String.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m46=cl.getMethod("gt",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m47=cl.getMethod("gte",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m48=cl.getMethod("if_then_else",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m49=cl.getMethod("implies",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m50=cl.getMethod("index",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m51=cl.getMethod("inhale",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m52=cl.getMethod("label",java.lang.Object.class,java.lang.String.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m53=cl.getMethod("local_name",java.lang.Object.class,java.lang.String.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m54=cl.getMethod("lt",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m55=cl.getMethod("lte",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m56=cl.getMethod("method_call",java.lang.Object.class,java.lang.String.class,java.util.List.class,java.util.List.class,java.util.List.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m57=cl.getMethod("mod",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m58=cl.getMethod("mult",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m59=cl.getMethod("neg",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m60=cl.getMethod("neq",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m61=cl.getMethod("new_object",java.lang.Object.class,java.lang.Object.class,java.util.List.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m62=cl.getMethod("no_perm",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m63=cl.getMethod("not",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m64=cl.getMethod("null_",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m65=cl.getMethod("old",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m66=cl.getMethod("or",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m67=cl.getMethod("predicate_call",java.lang.Object.class,java.lang.String.class,java.util.List.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m68=cl.getMethod("program");
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m69=cl.getMethod("range",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m70=cl.getMethod("read_perm",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m71=cl.getMethod("result",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m72=cl.getMethod("scale_access",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m73=cl.getMethod("seq_contains",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m74=cl.getMethod("size",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m75=cl.getMethod("sub",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m76=cl.getMethod("take",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m77=cl.getMethod("unfold",java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m78=cl.getMethod("unfolding_in",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m79=cl.getMethod("union",java.lang.Object.class,java.lang.Object.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m80=cl.getMethod("verify",java.lang.Object.class,java.nio.file.Path.class,java.util.Properties.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m81=cl.getMethod("while_loop",java.lang.Object.class,java.lang.Object.class,java.util.List.class,java.util.List.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m82=cl.getMethod("write_perm",java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
  try {
    m83=cl.getMethod("write_program",java.io.PrintWriter.class,java.lang.Object.class);
  } catch (NoSuchMethodException e) {
    throw new Error("NoSuchMethodException: "+e.getMessage());
  } catch (SecurityException e) {
    throw new Error("SecurityException: "+e.getMessage());
  }
}
public T Bag(T arg0){
  try {
    return (T)m0.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T Bool(){
  try {
    return (T)m1.invoke(obj);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E Constant(O arg0,int arg1){
  try {
    return (E)m2.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E Constant(O arg0,boolean arg1){
  try {
    return (E)m3.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E FieldAccess(O arg0,E arg1,java.lang.String arg2,T arg3){
  try {
    return (E)m4.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T Int(){
  try {
    return (T)m5.invoke(obj);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T List(T arg0){
  try {
    return (T)m6.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T Perm(){
  try {
    return (T)m7.invoke(obj);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T Ref(){
  try {
    return (T)m8.invoke(obj);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T Set(T arg0){
  try {
    return (T)m9.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E add(O arg0,E arg1,E arg2){
  try {
    return (E)m10.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void add_adt(P arg0,O arg1,java.lang.String arg2,java.util.List<DFunc> arg3,java.util.List<DAxiom> arg4,java.util.List<java.lang.String> arg5){
  try {
    m11.invoke(obj,arg0,arg1,arg2,arg3,arg4,arg5);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void add_field(P arg0,O arg1,java.lang.String arg2,T arg3){
  try {
    m12.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void add_function(P arg0,O arg1,java.lang.String arg2,java.util.List<Decl> arg3,T arg4,java.util.List<E> arg5,java.util.List<E> arg6,E arg7){
  try {
    m13.invoke(obj,arg0,arg1,arg2,arg3,arg4,arg5,arg6,arg7);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void add_method(P arg0,O arg1,java.lang.String arg2,java.util.List<E> arg3,java.util.List<E> arg4,java.util.List<Decl> arg5,java.util.List<Decl> arg6,java.util.List<Decl> arg7,S arg8){
  try {
    m14.invoke(obj,arg0,arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void add_predicate(P arg0,O arg1,java.lang.String arg2,java.util.List<Decl> arg3,E arg4){
  try {
    m15.invoke(obj,arg0,arg1,arg2,arg3,arg4);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E and(O arg0,E arg1,E arg2){
  try {
    return (E)m16.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E any_set_contains(O arg0,E arg1,E arg2){
  try {
    return (E)m17.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E append(O arg0,E arg1,E arg2){
  try {
    return (E)m18.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S assert_(O arg0,E arg1){
  try {
    return (S)m19.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S assignment(O arg0,E arg1,E arg2){
  try {
    return (S)m20.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S block(O arg0,java.util.List<S> arg1){
  try {
    return (S)m21.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E cond(O arg0,E arg1,E arg2,E arg3){
  try {
    return (E)m22.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public DAxiom daxiom(O arg0,java.lang.String arg1,E arg2){
  try {
    return (DAxiom)m23.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public Decl decl(O arg0,java.lang.String arg1,T arg2){
  try {
    return (Decl)m24.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public DFunc dfunc(O arg0,java.lang.String arg1,java.util.List<Decl> arg2,T arg3){
  try {
    return (DFunc)m25.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E div(O arg0,E arg1,E arg2){
  try {
    return (E)m26.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E domain_call(O arg0,java.lang.String arg1,java.util.List<E> arg2,java.util.Map<java.lang.String, T> arg3,T arg4,java.util.List<Decl> arg5){
  try {
    return (E)m27.invoke(obj,arg0,arg1,arg2,arg3,arg4,arg5);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public T domain_type(java.lang.String arg0){
  try {
    return (T)m28.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E drop(O arg0,E arg1,E arg2){
  try {
    return (E)m29.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E empty_bag(O arg0,T arg1){
  try {
    return (E)m30.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E empty_seq(O arg0,T arg1){
  try {
    return (E)m31.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E empty_set(O arg0,T arg1){
  try {
    return (E)m32.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E eq(O arg0,E arg1,E arg2){
  try {
    return (E)m33.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S exhale(O arg0,E arg1){
  try {
    return (S)m34.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E exists(O arg0,java.util.List<Decl> arg1,E arg2){
  try {
    return (E)m35.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E explicit_bag(O arg0,java.util.List<E> arg1){
  try {
    return (E)m36.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E explicit_seq(O arg0,java.util.List<E> arg1){
  try {
    return (E)m37.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E explicit_set(O arg0,java.util.List<E> arg1){
  try {
    return (E)m38.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E field_access(O arg0,E arg1,E arg2){
  try {
    return (E)m39.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S fold(O arg0,E arg1){
  try {
    return (S)m40.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E forall(O arg0,java.util.List<Decl> arg1,E arg2){
  try {
    return (E)m41.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E frac(O arg0,E arg1,E arg2){
  try {
    return (E)m42.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E function_call(O arg0,java.lang.String arg1,java.util.List<E> arg2,T arg3,java.util.List<Decl> arg4){
  try {
    return (E)m43.invoke(obj,arg0,arg1,arg2,arg3,arg4);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public O getOrigin(java.lang.Object arg0){
  try {
    return (O)m44.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S goto_(O arg0,java.lang.String arg1){
  try {
    return (S)m45.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E gt(O arg0,E arg1,E arg2){
  try {
    return (E)m46.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E gte(O arg0,E arg1,E arg2){
  try {
    return (E)m47.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S if_then_else(O arg0,E arg1,S arg2,S arg3){
  try {
    return (S)m48.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E implies(O arg0,E arg1,E arg2){
  try {
    return (E)m49.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E index(O arg0,E arg1,E arg2){
  try {
    return (E)m50.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S inhale(O arg0,E arg1){
  try {
    return (S)m51.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S label(O arg0,java.lang.String arg1){
  try {
    return (S)m52.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E local_name(O arg0,java.lang.String arg1,T arg2){
  try {
    return (E)m53.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E lt(O arg0,E arg1,E arg2){
  try {
    return (E)m54.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E lte(O arg0,E arg1,E arg2){
  try {
    return (E)m55.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S method_call(O arg0,java.lang.String arg1,java.util.List<E> arg2,java.util.List<E> arg3,java.util.List<Decl> arg4,java.util.List<Decl> arg5){
  try {
    return (S)m56.invoke(obj,arg0,arg1,arg2,arg3,arg4,arg5);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E mod(O arg0,E arg1,E arg2){
  try {
    return (E)m57.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E mult(O arg0,E arg1,E arg2){
  try {
    return (E)m58.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E neg(O arg0,E arg1){
  try {
    return (E)m59.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E neq(O arg0,E arg1,E arg2){
  try {
    return (E)m60.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S new_object(O arg0,E arg1,java.util.List<java.lang.String> arg2,java.util.List<T> arg3){
  try {
    return (S)m61.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E no_perm(O arg0){
  try {
    return (E)m62.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E not(O arg0,E arg1){
  try {
    return (E)m63.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E null_(O arg0){
  try {
    return (E)m64.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E old(O arg0,E arg1){
  try {
    return (E)m65.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E or(O arg0,E arg1,E arg2){
  try {
    return (E)m66.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E predicate_call(O arg0,java.lang.String arg1,java.util.List<E> arg2){
  try {
    return (E)m67.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public P program(){
  try {
    return (P)m68.invoke(obj);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E range(O arg0,E arg1,E arg2){
  try {
    return (E)m69.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E read_perm(O arg0){
  try {
    return (E)m70.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E result(O arg0,T arg1){
  try {
    return (E)m71.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E scale_access(O arg0,E arg1,E arg2){
  try {
    return (E)m72.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E seq_contains(O arg0,E arg1,E arg2){
  try {
    return (E)m73.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E size(O arg0,E arg1){
  try {
    return (E)m74.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E sub(O arg0,E arg1,E arg2){
  try {
    return (E)m75.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E take(O arg0,E arg1,E arg2){
  try {
    return (E)m76.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S unfold(O arg0,E arg1){
  try {
    return (S)m77.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E unfolding_in(O arg0,E arg1,E arg2){
  try {
    return (E)m78.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E union(O arg0,E arg1,E arg2){
  try {
    return (E)m79.invoke(obj,arg0,arg1,arg2);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public java.util.List<Err> verify(java.lang.Object arg0,java.nio.file.Path arg1,java.util.Properties arg2,P arg3){
  try {
    return (java.util.List<Err>)m80.invoke(obj,arg0,arg1,arg2,arg3);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public S while_loop(O arg0,E arg1,java.util.List<E> arg2,java.util.List<Decl> arg3,S arg4){
  try {
    return (S)m81.invoke(obj,arg0,arg1,arg2,arg3,arg4);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public E write_perm(O arg0){
  try {
    return (E)m82.invoke(obj,arg0);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
public void write_program(java.io.PrintWriter arg0,P arg1){
  try {
    m83.invoke(obj,arg0,arg1);
  } catch (IllegalAccessException | IllegalArgumentException e) {
    throw new Error(e.getClass()+" "+e.getMessage());
  } catch (InvocationTargetException e) {
    e.getCause().printStackTrace();
    throw new Error("in reflected call: "+e.getCause().getClass()+": "+e.getCause().getMessage());
  }
}
}
