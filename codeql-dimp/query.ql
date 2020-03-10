import analysis

query predicate program(TypeContext gamma, DStmt toplevel, TypeContext delta) {
  not exists(toplevel.getParent()) and
  tagStmt(gamma, toplevel, delta)
}

//query predicate programCand(TypeContext gamma, DStmt toplevel) {
//  not exists(toplevel.getParent()) and
//  gammaCand(gamma, toplevel)
//}

//query predicate program2(DStmt toplevel, TypeContext gamma) {
  //not exists(toplevel.getParent()) and
//  propagateContext(any(EmptyContext c), _, _, gamma, toplevel)
//}


from Sink sink, TypeContext gamma, Tag tag
where
  propagateContext(any(EmptyContext c), _, _, gamma, sink) and
  tagExpression(gamma, sink.getOperand(), tag)
select sink, tag
