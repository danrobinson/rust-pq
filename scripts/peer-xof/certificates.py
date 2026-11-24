"""Render the original, unsimplified LLVM path conditions as Lean proof obligations."""
import z3

UNARY = {z3.Z3_OP_NOT:"¬", z3.Z3_OP_UMINUS:"-"}
OPS = {z3.Z3_OP_EQ:"=",z3.Z3_OP_LE:"≤",z3.Z3_OP_LT:"<",z3.Z3_OP_GE:"≥",z3.Z3_OP_GT:">",
       z3.Z3_OP_AND:"∧",z3.Z3_OP_OR:"∨",z3.Z3_OP_IMPLIES:"→",z3.Z3_OP_ADD:"+",z3.Z3_OP_MUL:"*",
       z3.Z3_OP_SUB:"-",z3.Z3_OP_IDIV:"/",z3.Z3_OP_MOD:"%"}


def term(expr):
    if z3.is_int_value(expr):
        n=expr.as_long()
        return str(n) if n>=0 else f"({n})"
    if z3.is_true(expr):return "True"
    if z3.is_false(expr):return "False"
    op=expr.decl().kind()
    args=[term(c) for c in expr.children()]
    if op in UNARY:return "("+UNARY[op]+args[0]+")"
    if op in OPS:return "("+(" "+OPS[op]+" ").join(args)+")"
    if op==z3.Z3_OP_ITE:return "(if "+args[0]+" then "+args[1]+" else "+args[2]+")"
    if op==z3.Z3_OP_UNINTERPRETED:
        name=str(expr.decl().name())
        if name not in ("state","message","pos","n","byte_index","output_len","completed_blocks","index","blocks","iteration"):
            raise ValueError(name)
        return "("+name+" "+" ".join(args)+")" if args else name
    raise ValueError(f"unsupported solver term {expr}")


class Certificates:
    def __init__(self):
        self.cases = {}

    def record(self, env, goal, label):
        if isinstance(goal, bool):
            goal = z3.BoolVal(goal)
        # Avoid trusting solver simplification or sharing across unequal paths.
        key = tuple(term(h) for h in env["guard"]), term(goal)
        self.cases.setdefault(key,label)

    def program(self):
        source = """import Mathlib.Tactic
namespace PeerShake.Memory
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

"""
        names=[]
        for i, ((assumptions, claim), _) in enumerate(self.cases.items()):
            name = "checked"+str(i)
            names.append("PeerShake.Memory."+name)
            source += ("theorem "+name+" (n pos byte_index output_len completed_blocks index blocks iteration : Int) "
                       "(state message : Int → Int)\n    "+" ".join(f"(h{k} : {h})" for k,h in enumerate(assumptions))
                       +" :\n    "+claim+" := by\n  classical\n  first\n  | omega\n  | grind\n"
                       "  | (repeat' split <;> first | omega | grind)\n\n")
        return source+"end PeerShake.Memory\n",names
