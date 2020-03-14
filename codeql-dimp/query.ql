import dataflow

from DataFlowNode source, DataFlowNode sink
where
reaches(source, sink) and
sinkNode(sink)
select source, sink
