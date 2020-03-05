import analysis

from Sink sink, TypeContext gamma, Tag tag
where step(_, _, gamma, sink)
and
tagExpression(gamma, sink.getOperand(), tag)
select sink, tag
