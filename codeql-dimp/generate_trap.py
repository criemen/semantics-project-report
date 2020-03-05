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

def ifstmt(thenBranch, elseBranch):
    sid = newStmt(3, "if")
    app(f"stmtparents(#{sid}, #{thenBranch}, 0)")
    app(f"stmtparents(#{sid}, #{elseBranch}, 1)")
    return sid

def whilestmt(body):
    sid = newStmt(4, "while")
    app(f"stmtparents(#{sid}, #{body}, 0)")
    return sid

def sink(expr):
    sid = newStmt(5, "sink")
    app(f"exprparents(#{sid}, #{expr}, 0)")
    return sid


inttype()
int3 = intLiteral(3)
varX = newVar("X")
varY = newVar("Y")
varZ = newVar("Z")
varA1 = newVar("A1")
varA2 = newVar("A2")
varA = newVar("A")

whileL = whilestmt(seq(skip(), assign(varZ, source(varAccess(varY)))))
phinode(whileL, varY, varX, varZ)
seqfirst = seq(assign(varX, (intLiteral(4))), whileL)
seqsecond = seq(seqfirst, sink(varAccess(varY)))
ifS = ifstmt(assign(varA1, source(intLiteral(3))), assign(varA2, intLiteral(5)))
phinode(ifS, varA, varA1, varA2)
seqthird = seq(seqsecond, ifS)
seq4 = seq(seqthird, sink(varAccess(varA)))

#assignseq = seq(assign(varX, int3), assign(varY, varAccess(varX)))



with open("test.trap","w") as f:
    f.write(trap)
