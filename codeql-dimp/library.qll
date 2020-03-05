class PhiNode extends @phinode {
  string toString() { result = getAssignedVar().getName() + ":=phi(" + getFirstVar().getName() + "," + getSecondVar().getName() + ")" }

  DStmt getParent() { phinodes(this, result, _, _, _) }

  Variable getAssignedVar() { phinodes(this, _, result, _, _) }

  Variable getFirstVar() { phinodes(this, _, _, result, _) }

  Variable getSecondVar() { phinodes(this, _, _, _, result) }
}

class DExprParent extends @exprparent {
  string toString() { result = "DExprParent" }
}

abstract class DExpr extends @expr {
  abstract string toString();

  DExprParent getParent() { exprparents(result, this, _) }

  /** Gets the index of this statement as a child of its parent. */
  int getIndex() {exprparents(_, this, result) }

  /** Holds if this statement is the child of the specified parent at the specified (zero-based) position. */
  predicate isNthChildOf(DExprParent parent, int index) {
    this.getParent() = parent and this.getIndex() = index
  }
}

class IntLiteral extends DExpr, @intliteral {
  int getValue() { literals(this, result) }

  override string toString() { result = "IntLiteral " + getValue().toString() }
}

class VarAccess extends DExpr, @varaccess {
  /** Gets the variable accessed by this variable access. */
  Variable getVariable() { variableread(this, result) }

  override string toString() { result = "VarAccess " + this.getVariable().getName() }
}

abstract class BinaryExpr extends DExpr, @binaryexpr {
  DExpr getLeftOperand() { result.isNthChildOf(this, 0) }

  DExpr getRightOperand() { result.isNthChildOf(this, 1) }
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

class SourceExpr extends DExpr, @sourceexpr {
  DExpr getRhs() { result.isNthChildOf(this, 0) }

  override string toString() { result = "source " + getRhs().toString() }
}

abstract class DStmt extends @stmt {
  abstract string toString();

  DStmt getParent() { stmtparents(result, this, _) }

  /** Gets the index of this statement as a child of its parent. */
  int getIndex() {stmtparents(_, this, result) }

  /** Holds if this statement is the child of the specified parent at the specified (zero-based) position. */
  predicate isNthChildOf(DStmt parent, int index) {
    this.getParent() = parent and this.getIndex() = index
  }
}

class Skip extends DStmt, @skip {
  override string toString() { result = "skip" }
}

class Sink extends DStmt, @sink {
  override string toString() { result = "sink" }

  DExpr getOperand() { result.getParent() = this }
}

class Assign extends DStmt, @assign {
  Variable getDest() { variableassign(this, result) }

  DExpr getRhs() { result.isNthChildOf(this, 0) }

  override string toString() { result = "assign(" + getDest().getName() + ", " + getRhs().toString() + ")" }
}

class Seq extends DStmt, @seq {
  DStmt getFirstStatement() { result.isNthChildOf(this, 0) }

  DStmt getSecondStatement() { result.isNthChildOf(this, 1) }

  override string toString() { result = "seq" }
}

class IfStmt extends DStmt, @ifstmt {
  override string toString() { result = "if" }

  // TODO condition
  PhiNode getPhiNode() { result.getParent() = this }

  DStmt getThenBranch() { result.isNthChildOf(this, 0) }

  DStmt getElseBranch() { result.isNthChildOf(this, 1) }
}

class WhileStmt extends DStmt, @whilestmt {
  override string toString() { result = "while" }

  // TODO condition
  PhiNode getPhiNode() { result.getParent() = this }

  DStmt getBody() { result.isNthChildOf(this, 0) }
}


class Variable extends @variable {
  /** Gets an access to this variable. */
  VarAccess getAnAccess() { variableread(result, this) }

  Assign getAnAssignStmt() { result.getDest() = this }

  string getName() { vars(this, result, _) }

  string toString() { result = "Var " + this.getName() }
}
