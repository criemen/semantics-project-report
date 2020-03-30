import library

newtype TNode =
  TExprNode(DExpr e) { e instanceof VarAccess or e instanceof SourceExpr } or
  TStmtNode(DStmt stmt) { stmt instanceof Sink or stmt instanceof Assign } or
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
  // node1 is an expression that is assigned to a variable, then we flow to the
  // assign statement
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

predicate sourceNode(DataFlowNode node) { node.(DFExprNode).getExpr() instanceof SourceExpr }

predicate sinkNode(DataFlowNode node) { node.(DFStmtNode).getStmt() instanceof Sink }

newtype TNodeLabel =
  LUnknown() or
  LTracked() or
  LClean()

/**
 * Computes all applicable node label candidates.
 * Only computes labels on the subset of nodes that are reachable by `flowStep`
 * from sources in the dataflow graph.
 */
predicate nodeLabelCand(DataFlowNode node, TNodeLabel label) {
  // Regardless where in the tree we are, a source node results in a tracked
  // marking
  sourceNode(node) and
  label = LTracked()
  or
  not sourceNode(node) and
  (
    // base case - all nodes without incoming edges in the DF graph
    // (that are not source nodes)
    not exists(DataFlowNode prev | flowStep(prev, node)) and
    label = LClean()
    or
    // node is not a phi node, so we propagate the label(s) from the previous node
    not node instanceof DFPhiNode and
    exists(DataFlowNode prev | flowStep(prev, node) and nodeLabelCand(prev, label))
    or
    // node is a phi node, so we either propagate the previous unknown state if all
    // input nodes have a matching state, or unknown
    node instanceof DFPhiNode and
    (
      forex(DataFlowNode prev | flowStep(prev, node) | nodeLabelCand(prev, label))
      or
      exists(DataFlowNode prev | flowStep(prev, node) and nodeLabelCand(prev, _)) and
      label = LUnknown()
    )
  )
}

/**
 * Marks each dataflow node according to the lattice.
 * For expression nodes, the tracking directly corresponds to the type assigned
 * by the DF typing system.
 *
 * This predicate computes the best label that a node can have, i.e. the most
 * specific one of the candidate labels computed by `nodeLabelCand`.
 */
predicate nodeLabel(DataFlowNode node, TNodeLabel label) {
  nodeLabelCand(node, LUnknown()) and
  nodeLabelCand(node, LTracked()) and
  label = LTracked()
  or
  nodeLabelCand(node, LUnknown()) and
  nodeLabelCand(node, LClean()) and
  label = LClean()
  or
  nodeLabelCand(node, label) and
  not nodeLabelCand(node, any(TNodeLabel l | l != label))
}

/*
 * Computes possible dataflow on a reduced lattice with only clean and unknown.
 * A node not in this predicate is marked with clean.
 */

predicate reaches(DataFlowNode source, DataFlowNode node) {
  sourceNode(source) and
  flowStep*(source, node)
}
