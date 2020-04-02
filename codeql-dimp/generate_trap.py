#!/usr/bin/python
# main.py
import sys

if __name__ == "__main__":
    with open('args.txt', 'w') as f:
        f.write(f"Arguments count: {len(sys.argv)}")
        for i, arg in enumerate(sys.argv):
            f.write(f"Argument {i:>6}: {arg}")


trap = ""

def app(s):
    global trap
    trap = trap + s + "\n"


def gen():
    id = 1
    while True:
        yield id 
        id = id + 1

idGen = gen()

def nextId():
    i =  next(idGen)
    app(f"#{i}=*")
    return i

vars = {}
intType = nextId()


def inttype():
    app(f"types(#{intType}, \"int\")")

def newVar(name):
    global vars
    app(f"//var {name}")
    vars[name] = nextId()
    app(f"vars(#{vars[name]}, \"{name}\", #{intType})")
    return vars[name]

def newExpr(kind, s):
    exprId = nextId()
    app(f"//expr {s}")
    app(f"exprs(#{exprId}, {kind}, #{intType})")
    return exprId

def intLiteral(val):
    exprId = newExpr(1, "int literal")
    app(f"literals(#{exprId}, {val})")
    return exprId

def addition(e1, e2):
    exprId = newExpr(2, "addition")
    app(f"exprparents(#{exprId}, #{e1}, 0)")
    app(f"exprparents(#{exprId}, #{e2}, 1)")
    return exprId


def subtraction(e1, e2):
    exprId = newExpr(3, "subtraction")
    app(f"exprparents(#{exprId}, #{e1}, 0)")
    app(f"exprparents(#{exprId}, #{e2}, 1)")
    return exprId


def mul(e1, e2):
    exprId = newExpr(4, "mul")
    app(f"exprparents(#{exprId}, #{e1}, 0)")
    app(f"exprparents(#{exprId}, #{e2}, 1)")
    return exprId

def varAccess(var):
    exprId = newExpr(5, "read var")
    app(f"variableread(#{exprId}, #{var})")
    return exprId

def source(readExpr):
    exprId = newExpr(6, "source")
    app(f"exprparents(#{exprId}, #{readExpr}, 0)")
    return exprId

def phinode(stmt, assignedvar, firstvar, secondvar):
    pid = nextId()
    app(f"//phinode")
    app(f"phinodes(#{pid}, #{stmt}, #{assignedvar}, #{firstvar}, #{secondvar})")
    return pid

def newStmt(kind, s):
    stmtId = nextId()
    app(f"//stmt {s}")
    app(f"stmts(#{stmtId}, {kind})")
    return stmtId


def skip():
    sid = newStmt(0, "skip")
    return sid

def assign(var, expr):
    sid = newStmt(1, "assign")
    app(f"variableassign(#{sid}, #{var})")
    app(f"exprparents(#{sid}, #{expr}, 0)")
    return sid

def seq(s1, s2):
    sid = newStmt(2, "seq")
    app(f"stmtparents(#{sid}, #{s1}, 0)")
    app(f"stmtparents(#{sid}, #{s2}, 1)")
    return sid

def ifstmt(cond, thenBranch, elseBranch):
    sid = newStmt(3, "if")
    app(f"stmtparents(#{sid}, #{thenBranch}, 0)")
    app(f"stmtparents(#{sid}, #{elseBranch}, 1)")
    app(f"bexprparents(#{sid}, #{cond}, 0)")
    return sid

def whilestmt(cond, body):
    sid = newStmt(4, "while")
    app(f"stmtparents(#{sid}, #{body}, 0)")
    app(f"bexprparents(#{sid}, #{cond}, 0)")
    return sid

def sink(expr):
    sid = newStmt(5, "sink")
    app(f"exprparents(#{sid}, #{expr}, 0)")
    return sid

def newBexpr(kind, s):
    bexprId = nextId()
    app(f"//bexpr {s}")
    app(f"boolexprs(#{bexprId}, {kind})")
    return bexprId

def boolliteral(val):
    bexprId = newBexpr(1, "boolliteral")
    app(f"boolliterals(#{bexprId}, {val})")
    return bexprId

def boolequality(a1, a2):
    bexprId = newBexpr(2, "booleq")
    app(f"exprparents(#{bexprId}, #{a1}, 0)")
    app(f"exprparents(#{bexprId}, #{a2}, 1)")
    return bexprId

def boolleq(a1, a2):
    bexprId = newBexpr(3, "boolleq")
    app(f"exprparents(#{bexprId}, #{a1}, 0)")
    app(f"exprparents(#{bexprId}, #{a2}, 1)")
    return bexprId

def bneg(b1):
    bexprId = newBexpr(4, "boolneg")
    app(f"bexprparents(#{bexprId}, #{b1}, 0)")
    return bexprId

def band(b1, b2):
    bexprId = newBexpr(5, "booland")
    app(f"bexprparents(#{bexprId}, #{b1}, 0)")
    app(f"bexprparents(#{bexprId}, #{b2}, 1)")
    return bexprId


inttype()
varX = newVar("X")
varI0 = newVar("I0")
varI1 = newVar("I1")
varI2 = newVar("I2")
varZ0 = newVar("Z0")
varZ1 = newVar("Z1")
varZ2 = newVar("Z2")
varZ3 = newVar("Z3")




ifB = ifstmt(boolleq(varAccess(varZ3), intLiteral(99)), assign(varZ1, source(mul(varAccess(varZ3), varAccess(varX)))),
assign(varZ1, varAccess(varZ3)))
phinode(ifB, varZ2, varZ1, varZ1)
whileBody = seq(assign(varI1, subtraction(varAccess(varI2), intLiteral(1))), ifB)

seq1 = seq(assign(varI0, varAccess(varX)), assign(varZ0, intLiteral(1)))
whileL = whilestmt(boolleq(varAccess(varI2), intLiteral(0)), whileBody)
phinode(whileL, varZ3, varZ0, varZ2)
phinode(whileL, varI2, varI0, varI1)
seq2 = seq(seq1, whileL)
seq3 = seq(seq2, sink(varAccess(varZ3)))


#whileL = whilestmt(boolliteral(0), seq(assign(varZ, source(varAccess(varY))), sink(varY)))
#phinode(whileL, varY, varX, varZ)
#seqfirst = seq(assign(varX, (intLiteral(4))), whileL)

# old program

#whileL = whilestmt(boolliteral(0), assign(varZ, source(varAccess(varX))))
#phinode(whileL, varY, varX, varZ)
#seqfirst = seq(assign(varX, source(intLiteral(4))), whileL)
#seq(seqfirst, sink(varAccess(varY)))

#seqsecond = seq(seqfirst, sink(varAccess(varY)))
#ifS = ifstmt(bneg(boolleq(varAccess(varX), varAccess(varY))), assign(varA1, addition(source(intLiteral(3)), varAccess(varX))), assign(varA2, intLiteral(5)))
#phinode(ifS, varA, varA1, varA2)
#seqthird = seq(seqsecond, ifS)
#seq4 = seq(seqthird, sink(varAccess(varA)))


#assignseq =  seq(assign(varX, source(intLiteral(3))), sink(varAccess(varX)))#seq(assign(varX, intLiteral(3)), assign(varY, varAccess(varX)))#, sink(varAccess(varY)))

#bneg(boolleq(varAccess(varX), varAccess(varX))
#sink(varAccess(varY))
#ifS = seq(seq(assign(varX, source(intLiteral(3))), assign(varY, intLiteral(4))), ifstmt(boolliteral(1), sink(varAccess(varY)), sink(varAccess(varX))))
#phinode(ifS, varX, varY, varZ)

#ifstmt(boolliteral(1), skip(), skip())
#toplevel = seq(assignseq, ifS)

with open("test.trap","w") as f:
    f.write(trap)
