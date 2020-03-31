import dataflow

from DataFlowNode sink, TNodeLabel label
where
  nodeLabel(sink, label) and
  sinkNode(sink) and
  (label = LUnknown() or label = LTracked())
select sink
