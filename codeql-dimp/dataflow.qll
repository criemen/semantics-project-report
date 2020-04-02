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

abstract class NodeLabel extends TNodeLabel {
  abstract string toString();
}

class UnknownNodeLabel extends NodeLabel, LUnknown {
  override string toString() { result = "LUnknown" }
}

class TrackedNodeLabel extends NodeLabel, LTracked {
  override string toString() { result = "LTracked" }
}

class CleanNodeLabel extends NodeLabel, LClean {
  override string toString() { result = "LClean" }
}

/**
 * Propagates node labels through the dataflow graph.
 * A node can have multiple (even conflicting) labels, this is addressed
 * in `nodeLabel`.
 */
predicate nodeLabelCand(DataFlowNode node, NodeLabel label) {
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
    // propagate the label(s) from the previous node
    exists(DataFlowNode prev | flowStep(prev, node) and nodeLabelCand(prev, label))
  )
}

/**
 * Marks each dataflow node according to the lattice.
 * For expression nodes, the tracking directly corresponds to the type assigned
 * by the DF typing system.
 *
 * This predicate uses `nodeLabelCand` - if there is only one candidate label,
 * it is taken, otherwise the lattice join of the labels is taken.
 */
predicate nodeLabel(DataFlowNode node, NodeLabel label) {
  nodeLabelCand(node, LClean()) and
  nodeLabelCand(node, LTracked()) and
  label = LUnknown()
  or
  nodeLabelCand(node, label) and
  not nodeLabelCand(node, any(NodeLabel l | l != label))
}

/*
 * Computes possible dataflow on a reduced lattice with only clean and unknown.
 * A node not in this predicate is marked with clean.
 */
predicate reaches(DataFlowNode node) {
  exists(DataFlowNode source | sourceNode(source) | flowStep*(source, node))
}
