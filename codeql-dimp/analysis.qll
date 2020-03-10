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
  ctx1 = ctx2 and
  result = ctx1
  or
  ctx1 != ctx2 and
  (
    result = ctx1
    or
    result = ctx2
  )
}

/**
 * Computes the judgment for arithmetic expressions.
 */
predicate tagExpression(TypeContext gamma, DExpr e, Tag tag) {
  e instanceof IntLiteral and
  tag instanceof Clean and
  gamma instanceof EmptyContext
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
}

/**
 * Computes the judgment for boolean expressions.
 */
predicate tagBoolExpr(TypeContext gamma, BExpr e) {
  e instanceof BoolLiteral and
  gamma instanceof EmptyContext
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
}

/**
 * Computes the judgment for Phi nodes
 */
predicate tagPhiNode(
  TypeContext gamma, TypeContext delta0, TypeContext delta1, PhiNode phi, VarContext delta
) {
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
predicate tagStmt(TypeContext gamma, DStmt stmt, TypeContext delta) {
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
      gamma = typeContextUnion(typeContextUnion(gamma0, gamma1), gamma2) and
      delta instanceof EmptyContext // else delta isn't bound
    )
  )
  or
  stmt instanceof WhileStmt and
  exists(TypeContext delta0, TypeContext gamma1, TypeContext gamma2 |
    forall(PhiNode phiNode | phiNode = stmt.(WhileStmt).getAPhiNode() |
      exists(TypeContext gamma0 |
        tagPhiNode(gamma0, any(EmptyContext emptyCtx), delta0, phiNode, delta) and
        gamma = typeContextUnion(gamma0, typeContextUnion(gamma1, gamma2))
      )
    ) and
    tagStmt(typeContextUnion(gamma1, delta), stmt.(WhileStmt).getBody(), delta0) and
    tagBoolExpr(typeContextUnion(gamma2, delta), stmt.(WhileStmt).getCond()) and
    (
      exists(stmt.(WhileStmt).getAPhiNode())
      or
      gamma = typeContextUnion(gamma1, gamma2) and
      delta instanceof EmptyContext // else delta isn't bound
    )
  )
}

predicate isCompatibleContext(TypeContext fromCtx, TypeContext toCtx) {
  fromCtx = toCtx
  or
  fromCtx instanceof VarContext and
  toCtx instanceof EmptyContext
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
    isCompatibleContext(initialContext, fromGamma)
  ) and
  tagStmt(fromGamma, fromStmt, _) and
  tagStmt(toGamma, toStmt, _) and
  (
    fromStmt instanceof Seq and
    toStmt = fromStmt.(Seq).getFirstStatement() and
    isCompatibleContext(fromGamma, toGamma)
    or
    //toGamma = fromGamma
    fromStmt instanceof Seq and
    toStmt = fromStmt.(Seq).getSecondStatement() and
    exists(TypeContext delta0 |
      tagStmt(fromGamma, fromStmt.(Seq).getFirstStatement(), delta0) and
      isCompatibleContext(typeContextUnion(fromGamma, delta0), toGamma)
    )
    or
    fromStmt instanceof IfStmt and
    isCompatibleContext(fromGamma, toGamma)
    or
    fromStmt instanceof WhileStmt and
    toStmt = fromStmt.(WhileStmt).getBody() and
    exists(TypeContext delta, TypeContext delta0, EmptyContext emptyCtx |
      tagStmt(fromGamma, fromStmt, delta) and
      isCompatibleContext(typeContextUnion(fromGamma, delta), toGamma) and
      tagStmt(toGamma, toStmt, delta0) and
      tagPhiNode(fromGamma, emptyCtx, delta0, fromStmt.(WhileStmt).getAPhiNode(), delta)
    )
  )
}
