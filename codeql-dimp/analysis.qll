import library

/**
 * The poset the analysis is using
 */
newtype TTag =
  TUnknown() or
  TClean() or
  TTracked()

abstract class Tag extends TTag {
  abstract string toString();
}

class Unknown extends Tag, TUnknown {
  override string toString() { result = "TUnknown" }
}

class Clean extends Tag, TClean {
  override string toString() { result = "TClean" }
}

class Tracked extends Tag, TTracked {
  override string toString() { result = "TTracked" }
}

/**
 * A type context has two forms:
 * - either it is empty
 * - or it contains information about a variable, i.e. a variable and a tag
 */
newtype TTypeContent =
  TEmptyContext() or
  TVarContext(Variable var, TTag t)

abstract class TypeContext extends TTypeContent {
  abstract string toString();
}

class EmptyContext extends TypeContext, TEmptyContext {
  override string toString() { result = "TEmptyContext" }
}

class VarContext extends TypeContext, TVarContext {
  Variable var;
  Tag tag;

  VarContext() { this = TVarContext(var, tag) }

  Variable getVariable() { result = var }

  Tag getTag() { result = tag }

  override string toString() {
    result = "VarContext(" + getVariable().getName() + "," + getTag() + ")"
  }
}

/**
 * Computes the join operator on the `Tag` poset.
 */
Tag joinTags(Tag tag1, Tag tag2) {
  tag1 = tag2 and
  result = tag1
  or
  tag1 != tag2 and
  result instanceof Unknown
}

/**
 * Computes the join on the poset of the two contexts containing information about
 * variables.
 */
Tag joinTypeContexts(VarContext ctx1, VarContext ctx2) {
  result = joinTags(ctx1.getTag(), ctx2.getTag())
}

/**
 * Computes the union of the type contexts `ctx1` and `ctx2`.
 */
TypeContext typeContextUnion(TypeContext ctx1, TypeContext ctx2) {
  result = ctx1 and
  ctx2 instanceof EmptyContext
  or
  result = ctx2 and
  ctx1 instanceof EmptyContext
  or
  ctx1 = ctx2 and
  result = ctx1
  or
  ctx1.(VarContext).getVariable() != ctx2.(VarContext).getVariable() and
  (
    result = ctx1 or
    result = ctx2
  )
  or
  ctx1.(VarContext).getVariable() = ctx2.(VarContext).getVariable() and
  ctx1.(VarContext).getTag() != ctx2.(VarContext).getTag() and
  result.(VarContext).getVariable() = ctx1.(VarContext).getVariable() and
  result.(VarContext).getTag() = joinTypeContexts(ctx1, ctx2)
}

predicate expressionGammaCand(TypeContext gamma, DExpr e) {
  e instanceof IntLiteral and
  gamma instanceof EmptyContext
  or
  e.(VarAccess).getVariable() = gamma.(VarContext).getVariable()
  or
  e instanceof BinaryExpr and
  exists(TypeContext gamma0, TypeContext gamma1 |
    expressionGammaCand(gamma0, e.(BinaryExpr).getLeftOperand()) and
    expressionGammaCand(gamma1, e.(BinaryExpr).getRightOperand()) and
    gamma = typeContextUnion(gamma0, gamma1)
  )
  or
  e instanceof SourceExpr and
  expressionGammaCand(gamma, e.(SourceExpr).getRhs())
}

predicate booleanGammaCand(TypeContext gamma, BExpr e) {
  e instanceof BoolLiteral and
  gamma instanceof EmptyContext
  or
  e instanceof BEqual and
  exists(TypeContext gamma1, TypeContext gamma2 |
    expressionGammaCand(gamma1, e.(BEqual).getFirstOperand()) and
    expressionGammaCand(gamma2, e.(BEqual).getSecondOperand()) and
    gamma = typeContextUnion(gamma1, gamma2)
  )
  or
  e instanceof BLeq and
  exists(TypeContext gamma1, TypeContext gamma2 |
    expressionGammaCand(gamma1, e.(BLeq).getFirstOperand()) and
    expressionGammaCand(gamma2, e.(BLeq).getSecondOperand()) and
    gamma = typeContextUnion(gamma1, gamma2)
  )
  or
  e instanceof BNeg and
  booleanGammaCand(gamma, e.(BNeg).getOperand())
  or
  e instanceof BAnd and
  exists(TypeContext gamma1, TypeContext gamma2 |
    booleanGammaCand(gamma1, e.(BAnd).getFirstOperand()) and
    booleanGammaCand(gamma2, e.(BAnd).getSecondOperand()) and
    gamma = typeContextUnion(gamma1, gamma2)
  )
}

predicate phiNodeGammaCand(TypeContext gamma, TypeContext delta0, TypeContext delta1, PhiNode phi) {
  (
    gamma instanceof EmptyContext
    or
    phi.getAssignedVar() != gamma.(VarContext).getVariable()
  ) and
  exists(VarContext leftContext, VarContext rightContext |
    leftContext = typeContextUnion(gamma, delta0) and
    rightContext = typeContextUnion(gamma, delta1) and
    leftContext.getVariable() = phi.getFirstVar() and
    rightContext.getVariable() = phi.getSecondVar()
  )
}

// Computes a (potentially too large) set of applicable type contexts gamma for each statement
query predicate gammaCand(TypeContext gamma, DStmt stmt) {
  stmt instanceof Skip and
  gamma instanceof EmptyContext
  or
  stmt instanceof Sink and
  expressionGammaCand(gamma, stmt.(Sink).getOperand())
  or
  stmt instanceof Assign and
  expressionGammaCand(gamma, stmt.(Assign).getRhs())
  or
  stmt instanceof Seq and
  gammaCand(gamma, stmt.(Seq).getFirstStatement())
  or
  stmt instanceof IfStmt and
  exists(TypeContext gamma0, TypeContext gamma1, TypeContext gamma2 |
    booleanGammaCand(gamma0, stmt.(IfStmt).getCond()) and
    gammaCand(gamma1, stmt.(IfStmt).getThenBranch()) and
    gammaCand(gamma2, stmt.(IfStmt).getElseBranch()) and
    gamma = typeContextUnion(gamma0, typeContextUnion(gamma1, gamma2))
  )
  or
  stmt instanceof WhileStmt and
  exists(TypeContext gamma0, TypeContext gamma1 |
    booleanGammaCand(gamma0, stmt.(WhileStmt).getCond()) and
    gammaCand(gamma1, stmt.(WhileStmt).getBody()) and
    gamma = typeContextUnion(gamma0, gamma1)
  )
  /*
   * or
   *  stmt instanceof WhileStmt and
   *  exists(TypeContext delta0, TypeContext delta, EmptyContext emptyCtx |
   *    tagPhiNode(gamma, emptyCtx, delta0, stmt.(WhileStmt).getAPhiNode(), delta) or
   *    tagBoolExpr(gamma, stmt.(WhileStmt).getCond()) or
   *    gammaCand(gamma, stmt.(WhileStmt).getBody())
   *  )
   */

  }

/**
 * Computes the judgment for arithmetic expressions.
 */
query predicate tagExpression(TypeContext gamma, DExpr e, Tag tag) {
  //expressionGammaCand(gamma, e) and
  (
    e instanceof IntLiteral and
    tag instanceof Clean
    or
    e instanceof BinaryExpr and
    exists(TypeContext gamma0, TypeContext gamma1 |
      tagExpression(gamma0, e.(BinaryExpr).getLeftOperand(), _) and
      tagExpression(gamma1, e.(BinaryExpr).getRightOperand(), _) and
      gamma = typeContextUnion(gamma0, gamma1)
    ) and
    tag instanceof Clean
    or
    e instanceof SourceExpr and
    tagExpression(gamma, e.(SourceExpr).getRhs(), _) and
    tag instanceof Tracked
    or
    e.(VarAccess).getVariable() = gamma.(VarContext).getVariable() and
    tag = gamma.(VarContext).getTag()
  )
}

/**
 * Computes the judgment for boolean expressions.
 */
query predicate tagBoolExpr(TypeContext gamma, BExpr e) {
  //booleanGammaCand(gamma, e) and
  (
    e instanceof BoolLiteral
    or
    e instanceof BEqual and
    exists(TypeContext gamma1, TypeContext gamma2 |
      tagExpression(gamma1, e.(BEqual).getFirstOperand(), _) and
      tagExpression(gamma2, e.(BEqual).getSecondOperand(), _) and
      gamma = typeContextUnion(gamma1, gamma2)
    )
    or
    e instanceof BLeq and
    exists(TypeContext gamma1, TypeContext gamma2 |
      tagExpression(gamma1, e.(BLeq).getFirstOperand(), _) and
      tagExpression(gamma2, e.(BLeq).getSecondOperand(), _) and
      gamma = typeContextUnion(gamma1, gamma2)
    )
    or
    e instanceof BNeg and
    tagBoolExpr(gamma, e.(BNeg).getOperand())
    or
    e instanceof BAnd and
    exists(TypeContext gamma1, TypeContext gamma2 |
      tagBoolExpr(gamma1, e.(BAnd).getFirstOperand()) and
      tagBoolExpr(gamma2, e.(BAnd).getSecondOperand()) and
      gamma = typeContextUnion(gamma1, gamma2)
    )
  )
}

/**
 * Computes the judgment for Phi nodes
 */
query predicate tagPhiNode(
  TypeContext gamma, TypeContext delta0, TypeContext delta1, PhiNode phi, VarContext delta
) {
  phiNodeGammaCand(gamma, delta0, delta1, phi) and
  delta.getVariable() = phi.getAssignedVar() and
  (
    gamma instanceof EmptyContext
    or
    phi.getAssignedVar() != gamma.(VarContext).getVariable()
  ) and
  exists(VarContext leftContext, VarContext rightContext |
    leftContext = typeContextUnion(gamma, delta0) and
    rightContext = typeContextUnion(gamma, delta1) and
    leftContext.getVariable() = phi.getFirstVar() and
    rightContext.getVariable() = phi.getSecondVar()
  |
    delta.getTag() = joinTypeContexts(leftContext, rightContext)
  )
}

/**
 * Computes the judgment for statements.
 */
predicate tagStmt2(TypeContext gamma, DStmt stmt, TypeContext delta) {
  gammaCand(gamma, stmt) and
  (
    stmt instanceof Skip and
    delta instanceof EmptyContext
    or
    stmt instanceof Sink and
    tagExpression(gamma, stmt.(Sink).getOperand(), _) and
    delta instanceof EmptyContext
    or
    stmt instanceof Assign and
    exists(Tag exprTag, Variable var |
      var = stmt.(Assign).getDest() and
      tagExpression(gamma, stmt.(Assign).getRhs(), exprTag)
    |
      delta instanceof VarContext and
      delta.(VarContext).getTag() = exprTag and
      delta.(VarContext).getVariable() = var and
      (
        gamma.(VarContext).getVariable() != var or
        gamma instanceof EmptyContext
      )
    )
    or
    stmt instanceof Seq and
    exists(TypeContext delta0, TypeContext delta1 |
      tagStmt2(gamma, stmt.(Seq).getFirstStatement(), delta0) and
      tagStmt2(typeContextUnion(gamma, delta0), stmt.(Seq).getSecondStatement(), delta1) and
      delta = typeContextUnion(delta0, delta1)
    )
    or
    stmt instanceof IfStmt and
    exists(
      TypeContext gamma0, TypeContext gamma1, TypeContext gamma2, TypeContext gamma3,
      TypeContext delta0, TypeContext delta1
    |
      tagBoolExpr(gamma0, stmt.(IfStmt).getCond()) and
      tagStmt2(gamma1, stmt.(IfStmt).getThenBranch(), delta0) and
      tagStmt2(gamma2, stmt.(IfStmt).getElseBranch(), delta1) and
      forall(PhiNode phiNode | phiNode = stmt.(IfStmt).getAPhiNode() |
        tagPhiNode(gamma3, delta0, delta1, stmt.(IfStmt).getAPhiNode(), delta)
      ) and
      gamma = typeContextUnion(typeContextUnion(gamma0, gamma1), typeContextUnion(gamma2, gamma3))
    )
    or
    stmt instanceof WhileStmt and
    exists(TypeContext delta0, EmptyContext emptyCtx |
      tagPhiNode(gamma, emptyCtx, delta0, stmt.(WhileStmt).getAPhiNode(), delta) and
      tagStmt2(typeContextUnion(gamma, delta), stmt.(WhileStmt).getBody(), delta0) and
      tagBoolExpr(typeContextUnion(gamma, delta), stmt.(WhileStmt).getCond())
    )
  )
}

/**
 * Computes the judgment for statements.
 */
query predicate tagStmt(TypeContext gamma, DStmt stmt, TypeContext delta) {
  stmt instanceof Skip and
  delta instanceof EmptyContext
  or
  tagExpression(gamma, stmt.(Sink).getOperand(), _) and
  delta instanceof EmptyContext
  or
  stmt instanceof Assign and
  exists(Tag exprTag, Variable var |
    var = stmt.(Assign).getDest() and
    tagExpression(gamma, stmt.(Assign).getRhs(), exprTag)
  |
    delta instanceof VarContext and
    delta.(VarContext).getTag() = exprTag and
    delta.(VarContext).getVariable() = var and
    (
      gamma.(VarContext).getVariable() != var or
      gamma instanceof EmptyContext
    )
  )
  or
  stmt instanceof Seq and
  exists(TypeContext delta0, TypeContext delta1, TypeContext gamma0, TypeContext gamma1 |
    tagStmt(gamma0, stmt.(Seq).getFirstStatement(), delta0) and
    tagStmt(typeContextUnion(gamma1, delta0), stmt.(Seq).getSecondStatement(), delta1) and
    delta = typeContextUnion(delta0, delta1) and
    gamma = typeContextUnion(gamma0, gamma1)
  )
  or
  stmt instanceof IfStmt and
  exists(
    TypeContext gamma0, TypeContext gamma1, TypeContext gamma2, TypeContext delta0,
    TypeContext delta1
  |
    forall(PhiNode phiNode | phiNode = stmt.(IfStmt).getAPhiNode() |
      exists(TypeContext gamma3 |
        tagPhiNode(gamma3, delta0, delta1, phiNode, delta) and
        gamma = typeContextUnion(typeContextUnion(gamma0, gamma1), typeContextUnion(gamma2, gamma3))
      )
    ) and
    tagBoolExpr(gamma0, stmt.(IfStmt).getCond()) and
    tagStmt(gamma1, stmt.(IfStmt).getThenBranch(), delta0) and
    tagStmt(gamma2, stmt.(IfStmt).getElseBranch(), delta1) and
    (
      exists(stmt.(IfStmt).getAPhiNode())
      or
      gamma = typeContextUnion(typeContextUnion(gamma0, gamma1), gamma2)
    )
  )
  or
  stmt instanceof WhileStmt and
  exists(TypeContext delta0, EmptyContext emptyCtx, TypeContext gamma1, TypeContext gamma2 |
    forall(PhiNode phiNode | phiNode = stmt.(WhileStmt).getAPhiNode() |
      exists(TypeContext gamma0 |
        tagPhiNode(gamma0, emptyCtx, delta0, stmt.(WhileStmt).getAPhiNode(), delta) and
        gamma = typeContextUnion(gamma0, typeContextUnion(gamma1, gamma2))
      )
    ) and
    tagStmt(typeContextUnion(gamma1, delta), stmt.(WhileStmt).getBody(), delta0) and
    tagBoolExpr(typeContextUnion(gamma2, delta), stmt.(WhileStmt).getCond()) and
    (
      exists(stmt.(WhileStmt).getAPhiNode())
      or
      gamma = typeContextUnion(gamma1, gamma2)
    )
  )
}

/**
 * This predicate propagates the type context `initialContext` from the entry
 *  point of the program to all sub-expressions in the program, so their
 * initial context Gamma in the program when run in `initialContext` can be
 * determined.
 * If `fromStmt` is tagged with the context `fromGamma`, then `toStmt` is a child
 * statement of `fromStmt`, and it is tagged with the type context `toGamma`.
 */
predicate propagateContext(
  TypeContext initialContext, TypeContext fromGamma, DStmt fromStmt, TypeContext toGamma,
  DStmt toStmt
) {
  (
    exists(fromStmt.getParent()) and
    propagateContext(initialContext, _, fromStmt.getParent(), fromGamma, fromStmt)
    or
    fromGamma = initialContext
  ) and
  tagStmt(fromGamma, fromStmt, _) and
  tagStmt(toGamma, toStmt, _) and
  (
    fromStmt instanceof Seq and
    toStmt = fromStmt.(Seq).getFirstStatement() and
    toGamma = fromGamma
    or
    fromStmt instanceof Seq and
    toStmt = fromStmt.(Seq).getSecondStatement() and
    exists(TypeContext delta0 |
      tagStmt(fromGamma, fromStmt.(Seq).getFirstStatement(), delta0) and
      toGamma = typeContextUnion(fromGamma, delta0)
    )
    or
    fromStmt instanceof IfStmt and
    fromGamma = toGamma
    or
    fromStmt instanceof WhileStmt and
    toStmt = fromStmt.(WhileStmt).getBody() and
    exists(TypeContext delta, TypeContext delta0, EmptyContext emptyCtx |
      tagStmt(fromGamma, fromStmt, delta) and
      toGamma = typeContextUnion(fromGamma, delta) and
      tagStmt(toGamma, toStmt, delta0) and
      tagPhiNode(fromGamma, emptyCtx, delta0, fromStmt.(WhileStmt).getAPhiNode(), delta)
    )
  )
}
