import library

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
    result = "TVarContext(" + getVariable().getName() + "," + getTag() + ")"
  }
}

// this implements the join operator on the poset
Tag joinTags(Tag tag1, Tag tag2) {
  tag1 = tag2 and
  result = tag1
  or
  tag1 != tag2 and
  result instanceof Unknown
}

Tag joinTypeContexts(VarContext ctx1, VarContext ctx2) {
  result = joinTags(ctx1.getTag(), ctx2.getTag())
}

TypeContext typeContextUnion(TypeContext ctx1, TypeContext ctx2) {
  result = ctx1 and
  ctx2 instanceof EmptyContext
  or
  result = ctx2 and
  ctx1 instanceof EmptyContext
  or
  not ctx1 instanceof EmptyContext and
  not ctx2 instanceof EmptyContext and
  (
    result = ctx1 or
    result = ctx2
  )
}

cached
predicate tagExpression(TypeContext gamma, DExpr e, Tag tag) {
  e instanceof IntLiteral and
  tag instanceof Clean
  or
  e instanceof BinaryExpr and
  tag instanceof Clean
  or
  e instanceof SourceExpr and
  tag instanceof Tracked
  or
  e.(VarAccess).getVariable() = gamma.(VarContext).getVariable() and
  tag = gamma.(VarContext).getTag()
}

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

cached
predicate tagStmt(TypeContext gamma, DStmt stmt, TypeContext delta) {
  (
    exists(DStmt parent | stmt.getParent() = parent) or
    gamma instanceof EmptyContext
  ) and
  (
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
    exists(TypeContext delta0, TypeContext delta1 |
      tagStmt(gamma, stmt.(Seq).getFirstStatement(), delta0) and
      (
        tagStmt(gamma, stmt.(Seq).getSecondStatement(), delta1)
        or
        tagStmt(delta0, stmt.(Seq).getSecondStatement(), delta1)
      ) and
      delta = typeContextUnion(delta0, delta1)
    )
    or
    stmt instanceof IfStmt and
    exists(TypeContext delta0, TypeContext delta1 |
      tagStmt(gamma, stmt.(IfStmt).getThenBranch(), delta0) and
      tagStmt(gamma, stmt.(IfStmt).getElseBranch(), delta1) and
      tagPhiNode(gamma, delta0, delta1, stmt.(IfStmt).getPhiNode(), delta)
    )
    or
    stmt instanceof WhileStmt and
    exists(TypeContext delta0, EmptyContext emptyCtx |
      tagPhiNode(gamma, emptyCtx, delta0, stmt.(WhileStmt).getPhiNode(), delta) and
      (
        tagStmt(gamma, stmt.(WhileStmt).getBody(), delta0)
        or
        tagStmt(delta, stmt.(WhileStmt).getBody(), delta0)
      )
    )
  )
}

predicate tagStmtStep(
  TypeContext gamma0, DStmt stmt0, TypeContext gamma, DStmt stmt, TypeContext delta
) {
  tagStmt(gamma0, stmt0, _) and
  (
    stmt.getParent() = stmt0 or
    stmt = stmt0
  ) and
  (
    exists(DStmt parent | stmt.getParent() = parent)
    or
    gamma instanceof EmptyContext
  ) and
  (
    stmt instanceof Skip and
    delta instanceof EmptyContext and
    gamma0 = gamma
    or
    tagExpression(gamma, stmt.(Sink).getOperand(), _) and
    delta instanceof EmptyContext and
    gamma0 = gamma
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
      ) and
      gamma0 = gamma
    )
    or
    stmt instanceof Seq and
    exists(TypeContext delta0, TypeContext delta1 |
      tagStmtStep(gamma, stmt, gamma, stmt.(Seq).getFirstStatement(), delta0) and
      (
        tagStmtStep(gamma, stmt, gamma, stmt.(Seq).getSecondStatement(), delta1) and
        gamma0 = gamma
        or
        tagStmtStep(gamma, stmt, delta0, stmt.(Seq).getSecondStatement(), delta1) and
        gamma0 = delta0
      ) and
      delta = typeContextUnion(delta0, delta1) and
      forall(DStmt parent | parent = stmt.getParent() | parent = stmt0)
    )
    or
    stmt instanceof IfStmt and
    exists(TypeContext delta0, TypeContext delta1 |
      tagStmtStep(gamma, stmt, gamma, stmt.(IfStmt).getThenBranch(), delta0) and
      tagStmtStep(gamma, stmt, gamma, stmt.(IfStmt).getElseBranch(), delta1) and
      tagPhiNode(gamma, delta0, delta1, stmt.(IfStmt).getPhiNode(), delta) and
      gamma0 = gamma
    ) and
    stmt.getParent() = stmt0
    or
    stmt instanceof WhileStmt and
    exists(TypeContext delta0, EmptyContext emptyCtx |
      tagPhiNode(gamma, emptyCtx, delta0, stmt.(WhileStmt).getPhiNode(), delta) and
      (
        tagStmtStep(gamma, stmt, gamma, stmt.(WhileStmt).getBody(), delta0) and
        gamma0 = gamma
        or
        tagStmtStep(gamma, stmt, delta, stmt.(WhileStmt).getBody(), delta0) and
        gamma0 = delta
      )
    ) and
    stmt.getParent() = stmt0
  )
}

query predicate step(TypeContext fromGamma, DStmt fromStmt, TypeContext toGamma, DStmt toStmt) {
  (
    exists(fromStmt.getParent()) and
    step(_, fromStmt.getParent(), fromGamma, fromStmt)
    or
    fromGamma instanceof EmptyContext
  ) and
  toStmt.getParent() = fromStmt and
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
    exists(TypeContext delta, TypeContext delta0, EmptyContext emptyCtx |
      tagStmt(fromGamma, fromStmt, delta) and
      toGamma = typeContextUnion(fromGamma, delta) and
      tagStmt(toGamma, toStmt, delta0) and
      tagPhiNode(fromGamma, emptyCtx, delta0, fromStmt.(WhileStmt).getPhiNode(), delta)
    )
  )
}

/*
 * predicate tagStmtStep2(
 *  TypeContext fromCtx, DStmt fromStmt, TypeContext gamma, DStmt stmt, TypeContext delta
 * ) {
 *  (
 *    if not exists(fromStmt.getParent())
 *    then fromCtx instanceof EmptyContext
 *    else tagStmtStep2(_, fromStmt.getParent(), fromCtx, fromStmt, _)
 *  ) and
 *  stmt.getParent() = fromStmt and
 *  tagStmt(fromCtx, fromStmt, _) and
 *  tagStmt(gamma, stmt, delta) and
 *  (
 *    fromStmt instanceof Seq and
 *    (
 *      stmt = fromStmt.(Seq).getFirstStatement() and
 *      tagStmtStep2(gamma, stmt, gamma, stmt.(Seq).getFirstStatement(), delta) and
 *      //tagStmt(gamma, stmt, delta) and
 *      gamma = fromCtx
 *      or
 *      stmt = fromStmt.(Seq).getSecondStatement() and
 *      exists(TypeContext delta0, TypeContext delta1 |
 *        tagStmtStep2(fromCtx, stmt, gamma, stmt.(Seq).getFirstStatement(), delta0) and
 *        gamma = typeContextUnion(fromCtx, delta0) and
 *        tagStmt(gamma, stmt, delta1) and
 *        delta = typeContextUnion(delta0, delta1)
 *      )
 *    )
 *    or
 *    // TODO test!
 *    fromStmt instanceof IfStmt and
 *    gamma = fromCtx and
 *    (
 *      stmt = fromStmt.(IfStmt).getThenBranch()
 *      or
 *      stmt = fromStmt.(IfStmt).getElseBranch()
 *    )
 *  )
 * }
 */

predicate tagStmtStep3(
  TypeContext fromCtx, DStmt fromStmt, TypeContext fromDelta, TypeContext gamma, DStmt stmt,
  TypeContext delta
) {
  // base case
  not exists(stmt.getParent()) and
  fromStmt = stmt and
  gamma = fromCtx and
  delta = fromDelta and
  gamma instanceof EmptyContext and
  tagStmt(gamma, stmt, delta)
  or
  fromStmt instanceof Seq and
  gamma = fromCtx and
  tagStmtStep3(_, _, _, fromCtx, fromStmt, fromDelta) and
  stmt = fromStmt.(Seq).getFirstStatement() and
  exists(TypeContext delta0, TypeContext delta1 |
    tagStmt(gamma, stmt, delta0) and
    tagStmt(gamma, fromStmt.(Seq).getSecondStatement(), delta1) and
    fromDelta = typeContextUnion(delta0, delta1)
  )
}

predicate tagStmtStep4(TypeContext fromCtx, TypeContext gamma, DStmt stmt, TypeContext delta) {
  stmt instanceof Skip and
  delta instanceof EmptyContext and
  tagStmtStep4(_, fromCtx, stmt.getParent(), _)
  or
  tagExpression(gamma, stmt.(Sink).getOperand(), _) and
  delta instanceof EmptyContext and
  tagStmtStep4(_, fromCtx, stmt.getParent(), _)
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
  ) and
  tagStmtStep4(_, fromCtx, stmt.getParent(), _)
  or
  stmt instanceof Seq and
  //tagStmtStep4(_, fromCtx, stmt.getParent(), _) and
  exists(TypeContext delta0, TypeContext delta1 |
    tagStmt(gamma, stmt.(Seq).getFirstStatement(), delta0) and
    (
      tagStmt(gamma, stmt.(Seq).getSecondStatement(), delta1)
      or
      tagStmt(delta0, stmt.(Seq).getSecondStatement(), delta1)
    ) and
    delta = typeContextUnion(delta0, delta1)
  )
}
