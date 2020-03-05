import analysis

query predicate program(DStmt toplevel, TypeContext delta) {
  not exists(toplevel.getParent()) and
  tagStmt(any(EmptyContext c), toplevel, delta)
}

from Sink sink, TypeContext gamma, Tag tag
where
  step(_, _, gamma, sink) and
  tagExpression(gamma, sink.getOperand(), tag)
select sink, tag
