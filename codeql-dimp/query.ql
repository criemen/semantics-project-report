import dataflow

from DataFlowNode sink, TNodeLabel label
where
nodeLabel(sink, label) //and
//sinkNode(sink)
select sink, label.toString()
