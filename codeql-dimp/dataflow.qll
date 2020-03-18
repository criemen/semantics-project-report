import library

newtype TNode =
  TExprNode(DExpr e) {e instanceof VarAccess or e instanceof SourceExpr} or
  TStmtNode(DStmt stmt) or
  TPhiNode(PhiNode phinode)

abstract class DataFlowNode extends TNode {
  abstract string toString();
}

class DFExprNode extends DataFlowNode, TExprNode {
  DExpr e;

  DFExprNode() { this = TExprNode(e) }

  DExpr getExpr() { result = e }

  override string toString() { result = "DFExprNode: " + e.toString() }
}

class DFStmtNode extends DataFlowNode, TStmtNode {
  DStmt stmt;

  DFStmtNode() { this = TStmtNode(stmt) }

  DStmt getStmt() { result = stmt }

  override string toString() { result = "DFStmtNode: " + stmt.toString() }
}

class DFPhiNode extends DataFlowNode, TPhiNode {
  PhiNode phinode;

  DFPhiNode() { this = TPhiNode(phinode) }

  PhiNode getPhiNode() { result = phinode }

  override string toString() { result = "DFPhiNode: " + phinode.toString() }
}

predicate flowStep(DataFlowNode node1, DataFlowNode node2) {
  // node1 is an expression that is assigned to, then we flow to the assign statement
  node1.(DFExprNode).getExpr() = node2.(DFStmtNode).getStmt().(Assign).getRhs()
  or
  // node1 is an expression used in a sink, then we flow to the sink statement
  node1.(DFExprNode).getExpr() = node2.(DFStmtNode).getStmt().(Sink).getOperand()
  or
  // flow from a variable defined in a phi node to a read of the variable
  // in either another phi node or a variable access
  node1 instanceof DFPhiNode and
  exists(PhiNode phiNode | node1.(DFPhiNode).getPhiNode() = phiNode |
    phiNode.getAssignedVar().getAnAccess() = node2.(DFExprNode).getExpr()
    or
    phiNode.getAssignedVar().getAPhiNode() = node2.(DFPhiNode).getPhiNode()
  )
  or
  // node1 is an assign statement to a variable, then we flow to a read of the 
  // assigned-to variable (either a phi node read or a VarAccess expression)
  node1 instanceof DFStmtNode and
  exists(Assign assign | node1.(DFStmtNode).getStmt() = assign |
    assign.getDest().getAnAccess() = node2.(DFExprNode).getExpr()
    or
    assign.getDest().getAPhiNode() = node2.(DFPhiNode).getPhiNode()
  )
}

predicate sourceNode(DataFlowNode node) {
   node.(DFExprNode).getExpr() instanceof SourceExpr
}

predicate sinkNode(DataFlowNode node) { 
  node.(DFStmtNode).getStmt() instanceof Sink
}

predicate reaches(DataFlowNode source, DataFlowNode node) {
  sourceNode(source) and
  flowStep*(source, node)
}
