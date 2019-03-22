package vct.col.rewrite;

import java.util.*;

import hre.ast.MessageOrigin;
import vct.col.ast.*;

class RewriteArrayRefJava extends AbstractRewriter {
  private final static String ARRAY_CONSTRUCTOR = "new_array_";
  private final static String ARRAY_VALUES = "array_values_";

  private HashMap<Integer, HashSet<Type>> new_array;
  private HashSet<Type> array_values;
  
  public RewriteArrayRefJava(ProgramUnit source) {
    super(source);
  }
  
  @Override
  public ProgramUnit rewriteAll() {
    new_array = new HashMap<>();
    array_values = new HashSet<>();

    ProgramUnit res = super.rewriteAll();

    create.enter();
    create.setOrigin(new MessageOrigin("Array constructors"));
    for(Map.Entry<Integer, HashSet<Type>> entry : new_array.entrySet()) {
      for(Type t : entry.getValue()) {
        res.add(arrayConstructorFor(entry.getKey(), t));
      }
    }
    create.leave();

    create.enter();
    create.setOrigin(new MessageOrigin("Array values"));
    for (Type t : array_values) {
      res.add(arrayValuesFor(t));
    }
    create.leave();
    new_array = null;
    array_values = null;
    return res;
  }
  
  @Override
  public void visit(OperatorExpression e) {
    switch (e.operator()) {
    case ValidArray: {
      ASTNode M = rewrite(e.arg(0));
      ASTNode sz = rewrite(e.arg(1));
      // Determine type in order to generate appropiate conditions for ValidArray.
      Type t = e.first().getType();
      t = rewrite(t);
      M.setType(t);
      result = validArrayFor(M, sz);
      break;
    }
    case ValidMatrix: {
      ASTNode M = rewrite(e.arg(0));
      ASTNode sz1 = rewrite(e.arg(1));
      ASTNode sz2 = rewrite(e.arg(2));
      // Determine type in order to generate appropiate conditions for ValidMatrix.
      Type t = e.first().getType();
      t = rewrite(t);
      M.setType(t);
      result = validMatrixFor(M, sz1, sz2);
      break;
    }
    case EQ:
    case NEQ: {
      ASTNode e0 = e.arg(0);
      ASTNode e1 = e.arg(1);
      ASTNode array = null;
      if (e0.isReserved(ASTReserved.Null) && e1.getType().isPrimitive(PrimitiveSort.Array)) {
        array = e1;
      }
      if (e1.isReserved(ASTReserved.Null) && e0.getType().isPrimitive(PrimitiveSort.Array)) {
        array = e0;
      }
      if (array != null && rewrite(array.getType()).isPrimitive(PrimitiveSort.Option)) {
        result = create.expression(e.operator(), create.reserved_name(ASTReserved.OptionNone), rewrite(array));
      } else {
        super.visit(e);
      }
      break;
    }
    case Subscript:
      Type baseType = e.first().getType();

      if (baseType.isPrimitive(PrimitiveSort.Array) || baseType.isPrimitive(PrimitiveSort.Option)) {
        // Determine the (new) type to determine how to address elements in the array.
        baseType = rewrite(baseType);
        ASTNode base = rewrite(e.first());
        if (baseType.isPrimitive(PrimitiveSort.Option)) {
          base = create.expression(StandardOperator.OptionGet, base);
          baseType = (Type) baseType.firstarg();
        }
        ASTNode index = rewrite(e.second());
        result = create.expression(StandardOperator.Subscript, base, index);
        baseType = (Type) baseType.firstarg();
        if (baseType.isPrimitive(PrimitiveSort.Cell)) {
          result = create.dereference(result, "item");
        }
      } else {
        super.visit(e);
      }
      break;
    case Values: {
      Type t = (Type) ((PrimitiveType) e.getType()).firstarg();
      array_values.add(t);
      result = create.invokation(null, null, ARRAY_VALUES + t, rewrite(e.argsJava()));
      break;
    }
    case NewArray: {
      Type t = (Type) e.arg(0);
      new_array.computeIfAbsent(e.argslength() - 1, k -> new HashSet<>()).add(t);
      ArrayList<ASTNode> methodArgList = new ArrayList<>();

      for(int i = 1; i < e.argslength(); i++) {
        methodArgList.add(e.arg(i));
      }

      result = create.expression(StandardOperator.OptionSome,
              create.invokation(null, null, getArrayConstructor(t, e.argslength() - 1), rewrite(methodArgList)));
      break;
    }
    case PointsTo: {
      // If an Array field should have a Null value, change it to OptionNone.
      if (e.first().getType().isPrimitive(PrimitiveSort.Array) && e.third().isReserved(ASTReserved.Null)
          && rewrite(e.first().getType()).isPrimitive(PrimitiveSort.Option)) {
        ASTNode res = rewrite(e.first());
        result = star(create.expression(StandardOperator.Perm, res, rewrite(e.second())),
            create.expression(StandardOperator.EQ, res, create.reserved_name(ASTReserved.OptionNone)));
      } else {
        super.visit(e);
      }
      break;
    }
    default:
      super.visit(e);
    }
  }
  
  @Override
  public void visit(Dereference e) {
    if (e.field().equals("length")) {
      ASTNode res = rewrite(e.obj());
      if (rewrite(e.obj().getType()).isPrimitive(PrimitiveSort.Option)) {
        res = create.expression(StandardOperator.OptionGet, res);
      }
      result = create.expression(StandardOperator.Length, res);
    } else {
      super.visit(e);
    }
  }

  @Override
  public void visit(StructValue value) {
    Type t = value.getType();

    while(t.isPrimitive(PrimitiveSort.Option) || t.isPrimitive(PrimitiveSort.Cell) || t.isPrimitive(PrimitiveSort.Array)) {
      if(t.isPrimitive(PrimitiveSort.Cell)) {
        new_array.computeIfAbsent(1, k -> new HashSet<>()).add((Type) t.firstarg());
      }

      t = (Type) t.firstarg();
    }

    super.visit(value);
  }

  public static String getArrayConstructor(Type t, int depth) {
    String baseName = ARRAY_CONSTRUCTOR + depth + "_" + t.toString();
    return baseName.replace('<', '_').replace('>', '_');
  }

  private DeclarationStatement[] arrayConstructorAssertion_guardVariables(int depth) {
    DeclarationStatement[] declarations = new DeclarationStatement[depth];

    for(int i = 0; i < depth; i++) {
      declarations[i] = create.field_decl("i" + i, create.primitive_type(PrimitiveSort.Integer));
    }

    return declarations;
  }

  private ASTNode arrayConstructorAssertion_guard(int depth) {
    ASTNode guard = null;

    for(int i = 0; i < depth; i++) {
      // 0 <= i_n < size_n
      ASTNode variableGuard = create.expression(StandardOperator.And,
              create.expression(StandardOperator.LTE, create.constant(0), /*<=*/ create.local_name("i" + i)),
              create.expression(StandardOperator.LT, create.local_name("i" + i), /*<*/ create.local_name("size" + i)));

      if(guard == null) {
        guard = variableGuard;
      } else {
        guard = create.expression(StandardOperator.And, guard, variableGuard);
      }
    }

    return guard;
  }

  private ASTNode arrayConstructorAssertion_Perm(int depth, ASTNode result) {
    DeclarationStatement[] guardVariables = arrayConstructorAssertion_guardVariables(depth);
    ASTNode guard = arrayConstructorAssertion_guard(depth);

    ASTNode item = result;

    for(int i = 0; i < depth; i++) {
      // The outermost array is not of type option, so do not OptionGet it.
      ASTNode properArray = item == result ? item : create.expression(StandardOperator.OptionGet, item);

      item = create.dereference(create.expression(StandardOperator.Subscript,
              properArray,
              create.local_name("i" + i)), "item");
    }

    return create.starall(guard, create.expression(StandardOperator.Perm, item, create.reserved_name(ASTReserved.FullPerm)), guardVariables);
  }

  private ASTNode arrayConstructorAssertion_Length(int depth, ASTNode result) {
    DeclarationStatement[] guardVariables = arrayConstructorAssertion_guardVariables(depth);
    ASTNode guard = arrayConstructorAssertion_guard(depth);

    ASTNode lengthArray = result;

    for(int i = 0; i < depth; i++) {
      // OptionGet((...[i]).item)
      lengthArray = create.expression(StandardOperator.OptionGet,
              create.dereference(create.expression(StandardOperator.Subscript,
                      lengthArray,
                      create.local_name("i" + i)), "item"));
    }

    ASTNode claim = create.expression(StandardOperator.EQ, create.expression(StandardOperator.Length, lengthArray), create.local_name("size" + depth));

    if(guard == null) {
      return claim;
    } else {
      return create.starall(guard, claim, guardVariables);
    }
  }

  private ASTNode arrayConstructAssertion_None(int depth, ASTNode result) {
    DeclarationStatement[] guardVariables = arrayConstructorAssertion_guardVariables(depth);
    ASTNode guard = arrayConstructorAssertion_guard(depth);

    ASTNode notNone = result;

    for(int i = 0; i < depth; i++) {
      // The outermost array is not of type option, so do not OptionGet it.
      ASTNode properArray = (notNone == result) ? notNone : create.expression(StandardOperator.OptionGet, notNone);

      // OptionGet(...)[i_(depth - n)].item
      notNone = create.dereference(create.expression(StandardOperator.Subscript,
              properArray,
              create.local_name("i" + i)), "item");
    }

    notNone = create.expression(StandardOperator.NEQ, notNone, create.reserved_name(ASTReserved.OptionNone));

    if(guard == null) {
      return notNone;
    } else {
      return create.starall(guard, notNone, guardVariables);
    }
  }
  
  private Method arrayConstructorFor(int maxDepth, Type baseType) {
    ASTNode result = create.reserved_name(ASTReserved.Result);
    ContractBuilder resultContract = new ContractBuilder();

    // For every known depth, assert:
    //  - write permission to the elements [1..depth]
    //  - the array is not equal to none [1..depth)
    //  - the array length is the given size [0..depth)
    // The assertions must be in the correct order, so e.g. the preconditions of OptionGet are satisfied.

    for(int depth = 0; depth <= maxDepth; depth++) {
      if(depth > 0) resultContract.ensures(arrayConstructorAssertion_Perm(depth, result));
      if(depth > 0 && depth < maxDepth) resultContract.ensures(arrayConstructAssertion_None(depth, result));
      if(depth < maxDepth) resultContract.ensures(arrayConstructorAssertion_Length(depth, result));
    }

    // Finally, assert that at the last depth the item is zero
    DeclarationStatement[] guardVariables = arrayConstructorAssertion_guardVariables(maxDepth);
    ASTNode guard = arrayConstructorAssertion_guard(maxDepth);
    ASTNode item = result;

    for(int i = 0; i < maxDepth; i++) {
      // The outermost array is not of type option, so do not OptionGet it.
      ASTNode properArray = item == result ? item : create.expression(StandardOperator.OptionGet, item);

      item = create.dereference(create.expression(StandardOperator.Subscript,
              properArray,
              create.local_name("i" + i)), "item");
    }

    resultContract.ensures(create.starall(guard, create.expression(StandardOperator.EQ, item, baseType.zero()), guardVariables));

    // Now, construct the method declaration
    // create_array_type(int size0, int size1, ...) -> result_type: Array[Cell[Option[Array[Cell[...baseType]]]]]
    //    ensures contract
    Type resultType = baseType;

    for(int i = 0; i < maxDepth - 1; i++) {
      resultType = create.primitive_type(PrimitiveSort.Option, create.primitive_type(PrimitiveSort.Array, create.primitive_type(PrimitiveSort.Cell, resultType)));
    }

    resultType = create.primitive_type(PrimitiveSort.Array, create.primitive_type(PrimitiveSort.Cell, resultType));

    DeclarationStatement[] functionArguments = new DeclarationStatement[maxDepth];

    for(int i = 0; i < maxDepth; i++) {
      functionArguments[i] = create.field_decl("size" + i, create.primitive_type(PrimitiveSort.Integer));
    }

    Method methodDeclaration = create.method_decl(resultType,
            resultContract.getContract(),
            getArrayConstructor(baseType, maxDepth),
            functionArguments,
            null);

    methodDeclaration.setStatic(true);

    return methodDeclaration;
  }
  
  private Method arrayValuesFor(Type t) {
    PrimitiveType result_type = create.primitive_type(PrimitiveSort.Sequence, rewrite(t));
    Type type0 = create.primitive_type(PrimitiveSort.Array, t);
    type0 = rewrite(type0);
    ContractBuilder cb = new ContractBuilder();
    ArrayList<DeclarationStatement> args = new ArrayList<DeclarationStatement>();
    args.add(create.field_decl("ar", type0));
    args.add(create.field_decl("from", create.primitive_type(PrimitiveSort.Integer)));
    args.add(create.field_decl("upto", create.primitive_type(PrimitiveSort.Integer)));
    
    ASTNode deref = create.local_name("ar");
    if (type0.isPrimitive(PrimitiveSort.Option)) {
      cb.requires(neq(create.local_name("ar"), create.reserved_name(ASTReserved.OptionNone)));
      deref = create.expression(StandardOperator.OptionGet, deref);
    }
    
    cb.requires(create.expression(StandardOperator.LTE, create.constant(0), create.local_name("from")));
    cb.requires(create.expression(StandardOperator.LTE, create.local_name("from"), create.local_name("upto")));
    cb.requires(create.expression(StandardOperator.LTE, create.local_name("upto"),
        create.expression(StandardOperator.Length, deref)));
    ASTNode range = create.expression(StandardOperator.And,
        create.expression(StandardOperator.LTE, create.local_name("from"), create.local_name("i")),
        create.expression(StandardOperator.LT, create.local_name("i"), create.local_name("upto")));
    DeclarationStatement decl = create.field_decl("i", create.primitive_type(PrimitiveSort.Integer));
    ASTNode ari = create.dereference(create.expression(StandardOperator.Subscript, deref, create.local_name("i")),
        "item");
    ASTNode perm = create.expression(StandardOperator.Perm, ari, create.reserved_name(ASTReserved.ReadPerm));
    cb.requires(create.starall(range, perm, decl));
    ASTNode Resi = create.expression(StandardOperator.Subscript, create.reserved_name(ASTReserved.Result),
        create.expression(StandardOperator.Minus, create.local_name("i"), create.local_name("from")));
    cb.ensures(create.expression(StandardOperator.EQ,
        create.expression(StandardOperator.Size, create.reserved_name(ASTReserved.Result)),
        create.expression(StandardOperator.Minus, create.local_name("upto"), create.local_name("from"))));
    cb.ensures(create.forall(range, create.expression(StandardOperator.EQ, ari, Resi), decl));
    
    ASTNode len = create.expression(StandardOperator.Minus, create.local_name("upto"), create.local_name("from"));
    range = create.expression(StandardOperator.And,
        create.expression(StandardOperator.LTE, create.constant(0), create.local_name("i")),
        create.expression(StandardOperator.LT, create.local_name("i"), len));
    ari = create.dereference(create.expression(StandardOperator.Subscript, deref,
        create.expression(StandardOperator.Plus, create.local_name("i"), create.local_name("from"))), "item");
    Resi = create.expression(StandardOperator.Subscript, create.reserved_name(ASTReserved.Result),
        create.local_name("i"));
    cb.ensures(create.forall(range, create.expression(StandardOperator.EQ, ari, Resi), decl));
    
    Method m = create.function_decl(result_type, cb.getContract(), ARRAY_VALUES + t, args, null);
    m.setStatic(true);
    return m;
  }
  
  /**
   * Generate conditions for a "valid array" based on its type.
   * 
   * @param array
   *          The array to generate conditions for (needs to have a type set).
   * @param size
   *          The size that the given array is supposed to have.
   * @return Conditions that define a "valid array" for the given node (with its
   *         type). Since the VCTArray domain in Viper already defines
   *         injectivity, it is only needed to optionally define that it is not
   *         equal to None, and that the array has the given size.
   */
  private ASTNode validArrayFor(ASTNode array, ASTNode size) {
    Type type = array.getType();
    ASTNode base = array;
    ASTNode res = create.constant(true);
    if (type.isPrimitive(PrimitiveSort.Option)) {
      res = neq(array, create.reserved_name(ASTReserved.OptionNone));
      base = create.expression(StandardOperator.OptionGet, base);
      type = (Type) type.firstarg();
    }
    return and(res, eq(create.expression(StandardOperator.Length, base), size));
  }
  
  /**
   * Generate conditions for a "valid matrix" based on its type. Note that a valid
   * matrix must be injective for all its cells. Thus if rows are heap locations
   * (Cell-type) we must also show injectivity for the cells within the rows.
   * 
   * @param matrix
   *          The object to generate the conditions for.
   * @param sz1,sz2
   *          The dimensions that the matrix is supposed to have.
   * @return Conditions to define a "valid matrix" with the given demensions.
   */
  private ASTNode validMatrixFor(ASTNode matrix, ASTNode sz1, ASTNode sz2) {
    Type type = matrix.getType();
    ASTNode res = create.constant(true);
    ASTNode base = matrix;
    if (type.isPrimitive(PrimitiveSort.Option)) {
      res = neq(matrix, create.reserved_name(ASTReserved.OptionNone));
      base = create.expression(StandardOperator.OptionGet, base);
      type = (Type) type.firstarg();
    }
    if (!type.isPrimitive(PrimitiveSort.Array)) {
      Abort("Unexpected type for ValidMatrix");
    }
    type = (Type) type.firstarg();
    ASTNode nul = create.constant(0);
    ASTNode i = create.local_name("vm_i");
    ASTNode k = create.local_name("vm_k");
    ASTNode rowi = create.expression(StandardOperator.Subscript, base, i);
    ASTNode rowk = create.expression(StandardOperator.Subscript, base, k);
    DeclarationStatement decli = create.field_decl("vm_i", create.primitive_type(PrimitiveSort.Integer));
    ASTNode guardi = and(lte(nul, i), less(i, sz1));
    ASTNode mInjectivity = null;
    if (type.isPrimitive(PrimitiveSort.Cell)) {
      type = (Type) type.firstarg();
      // add read permissions for every row
      rowi = create.dereference(rowi, "item");
      rowk = create.dereference(rowk, "item");
      ASTNode claim = create.expression(StandardOperator.Perm, rowi, create.reserved_name(ASTReserved.ReadPerm));
      res = star(res, create.starall(guardi, claim, decli));
      // Show injectivity for heap locations.
      ASTNode j = create.local_name("vm_j");
      ASTNode l = create.local_name("vm_l");
      ArrayList<ASTNode> cons = new ArrayList<ASTNode>();
      cons.add(guardi);
      cons.add(lte(nul, j));
      cons.add(less(j, sz2));
      cons.add(lte(nul, k));
      cons.add(less(k, sz1));
      cons.add(lte(nul, l));
      cons.add(less(l, sz2));
      ASTNode ij = rowi;
      ASTNode kl = rowk;
      if (type.isPrimitive(PrimitiveSort.Option)) {
        ij = create.expression(StandardOperator.OptionGet, ij);
        kl = create.expression(StandardOperator.OptionGet, kl);
      }
      ij = create.expression(StandardOperator.Subscript, ij, j);
      kl = create.expression(StandardOperator.Subscript, kl, l);
      cons.add(eq(ij, kl));
      ASTNode guard = create.fold(StandardOperator.And, cons);
      claim = and(eq(i, k), eq(j, l));
      ASTNode[] trigger = new ASTNode[] { ij, kl };
      ASTNode triggers[][] = new ASTNode[][] { trigger };
      mInjectivity = create.forall(triggers, guard, claim, decli,
          create.field_decl("vm_j", create.primitive_type(PrimitiveSort.Integer)),
          create.field_decl("vm_k", create.primitive_type(PrimitiveSort.Integer)),
          create.field_decl("vm_l", create.primitive_type(PrimitiveSort.Integer)));
    }
    if (type.isPrimitive(PrimitiveSort.Option)) {
      // show that rows are not none
      type = (Type) type.firstarg();
      res = star(res, create.forall(guardi, neq(rowi, create.reserved_name(ASTReserved.OptionNone)), decli));
      rowi = create.expression(StandardOperator.OptionGet, rowi);
    }
    // show that rows have specified length.
    if (!type.isPrimitive(PrimitiveSort.Array)) {
      Warning("Row of ValidMatrix is not an array");
    }
    res = star(res, create.forall(guardi, eq(create.expression(StandardOperator.Length, rowi), sz2), decli));
    if (mInjectivity != null) {
      res = star(res, mInjectivity);
    }
    return res;
  }
  
}
