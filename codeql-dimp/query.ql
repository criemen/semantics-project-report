import analysis

query predicate taggedExpressions(TypeContext gamma, DExpr e, Tag tag) {
    tagExpression(gamma, e, tag)
}

query predicate taggedStmts(TypeContext gamma, DStmt stmt, TypeContext delta) {
    tagStmt(gamma, stmt, delta)
}

query predicate statements(DStmt stmt) {
    any()
}