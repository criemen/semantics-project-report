class PhiNode extends @phinode {
  string toString() { result = "phinode" }

  Stmt getParent() { phinodes(this, result, _, _, _) }

  Variable getAssignedVar() { phinodes(this, _, result, _, _) }

  Variable getFirstVar() { phinodes(this, _, _, result, _) }

  Variable getSecondVar() { phinodes(this, _, _, _, result) }
}

class ExprParent extends @exprparent {
  string toString() { result = "ExprParent" }
}

abstract class Expr extends @expr {
  abstract string toString();

  /** Gets the parent of this expression. */
  ExprParent getParent() { exprs(this, _, _, result, _) }

  /** Holds if this expression is the child of the specified parent at the specified (zero-based) position. */
  predicate isNthChildOf(ExprParent parent, int index) { exprs(this, _, _, parent, index) }
}

class IntLiteral extends Expr, @intliteral {
  int getValue() { literals(this, result) }

  override string toString() { result = "IntLiteral " + getValue().toString() }
}

class VarAccess extends Expr, @varaccess {
  /** Gets the variable accessed by this variable access. */
  Variable getVariable() { variableread(this, result) }

  override string toString() { result = this.getVariable().getName() }
}

abstract class BinaryExpr extends Expr, @binaryexpr {
  Expr getLeftOperand() { result.isNthChildOf(this, 0) }

  Expr getRightOperand() { result.isNthChildOf(this, 1) }
}

class AddExpr extends BinaryExpr, @addexpr {
  override string toString() { result = "... + ..." }
}

class SubExpr extends BinaryExpr, @subexpr {
  override string toString() { result = "... - ..." }
}

class MulExpr extends BinaryExpr, @mulexpr {
  override string toString() { result = "... * ..." }
}

class SourceExpr extends Expr, @sourceexpr {
  Expr getRhs() { result.isNthChildOf(this, 0) }

  override string toString() { result = "source" }
}

abstract class Stmt extends @stmt {
  abstract string toString();

  Stmt getParent() { stmts(this, _, result, _) }

  /** Gets the index of this statement as a child of its parent. */
  int getIndex() { stmts(this, _, _, result) }

  /** Holds if this statement is the child of the specified parent at the specified (zero-based) position. */
  predicate isNthChildOf(Stmt parent, int index) {
    this.getParent() = parent and this.getIndex() = index
  }
}

class Skip extends Stmt, @skip {
  override string toString() { result = "skip" }
}

class Sink extends Stmt, @sink {
  override string toString() { result = "sink" }

  Expr getOperand() { result.getParent() = this }
}

class Assign extends Stmt, @assign {
  Variable getDest() { variableassign(this, result) }

  Expr getRhs() { result.isNthChildOf(this, 0) }

  override string toString() { result = "assign(" + getDest().getName() + ", " + ")" }
}

class Seq extends Stmt, @seq {
  Stmt getFirstStatement() { result.isNthChildOf(this, 0) }

  Stmt getSecondStatement() { result.isNthChildOf(this, 1) }

  override string toString() { result = "seq" }
}

class IfStmt extends Stmt, @ifstmt {
  override string toString() { result = "if" }

  // TODO condition
  PhiNode getPhiNode() { result.getParent() = this }

  Stmt getThenBranch() { result.isNthChildOf(this, 0) }

  Stmt getElseBranch() { result.isNthChildOf(this, 1) }
}

class Variable extends @variable {
  /** Gets an access to this variable. */
  VarAccess getAnAccess() { variableread(result, this) }

  Assign getAnAssignStmt() { result.getDest() = this }

  string getName() { vars(this, result, _) }

  /** Gets an expression on the right-hand side of an assignment to this variable. */
  //Expr getAnAssignedValue() {
  //  exists(LocalVariableDeclExpr e | e.getVariable() = this and result = e.getInit())
  //  or
  //  exists(AssignExpr e | e.getDest() = this.getAnAccess() and result = e.getSource())
  //}
  string toString() { result = this.getName() }
}
