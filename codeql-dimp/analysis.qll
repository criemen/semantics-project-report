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
