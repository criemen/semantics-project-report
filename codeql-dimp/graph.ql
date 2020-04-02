/**
 * @kind graph
 */

import dataflow

query predicate nodes(DataFlowNode node, string key, string val) {
  key = "semmle.label" and val = node.toString()
}

query predicate edges(DataFlowNode node1, DataFlowNode node2) { flowStep(node1, node2) }

query predicate parents(DataFlowNode child, DataFlowNode parent) {
    flowStep(parent, child)
//  child.(DFExprNode).getExpr().getParent() = parent.(DFExprNode).getExpr() or
//  child.(DFExprNode).getExpr().getParent() = parent.(DFStmtNode).getStmt()
  //or
  //child.(DFPhiNode).getPhiNode() = parent.(DFStmtNode).getStmt().(WhileStmt).getAPhiNode()
}
