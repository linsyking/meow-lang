"""Verify the two main structural bounds on random once-r expressions:

(1) Occurrence Bound: for any nonempty u, #u(output) <= L*max_i #u(S_i) + C
    with L = #variable leaves, C = sum_const #u(W) + 2|u|*#Subst + |u|*#Cat.
(2) Linear Length Bound: |output| <= N*max|S_i| + C' with N = #variable
    leaves, C' = total constant length (same recursion without the +2|u|).

Both stated for the WITH-CONCAT calculus (core is a subcase).
"""
import random
from core import Var, Const, Subst, Cat, evalE, var_leaves
from core import subst_once_r

random.seed(42)
SIG = "ab"

def rand_expr(depth, nvars, consts):
    if depth == 0 or random.random() < 0.3:
        if random.random() < 0.5:
            return Var(random.randrange(nvars))
        return Const(random.choice(consts))
    if random.random() < 0.15:
        return Cat(rand_expr(depth - 1, nvars, consts),
                   rand_expr(depth - 1, nvars, consts))
    R = rand_expr(depth - 1, nvars, consts)
    P = rand_expr(depth - 1, nvars, consts)
    E = rand_expr(depth - 1, nvars, consts)
    return Subst(R, P, E)

def count_const_leaves(E, f):
    if isinstance(E, Var): return 0
    if isinstance(E, Const): return f(E.w)
    if isinstance(E, Cat): return count_const_leaves(E.a, f) + count_const_leaves(E.b, f)
    return count_const_leaves(E.R, f) + count_const_leaves(E.P, f) + count_const_leaves(E.E, f)

def count_nodes(E, cls):
    if isinstance(E, (Var, Const)): return 0
    if isinstance(E, Cat):
        return (1 if cls is Cat else 0) + count_nodes(E.a, cls) + count_nodes(E.b, cls)
    return (1 if cls is Subst else 0) + count_nodes(E.R, cls) + count_nodes(E.P, cls) + count_nodes(E.E, cls)

def nsub(E): return count_nodes(E, Subst)
def ncat(E): return count_nodes(E, Cat)

CONSTS = ["", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb"]
NVARS = 2

bad_occ, bad_len, tested = 0, 0, 0
for trial in range(4000):
    E = rand_expr(3, NVARS, CONSTS)
    inputs = ["".join(random.choice(SIG) for _ in range(random.randint(0, 6)))
              for _ in range(NVARS)]
    v = evalE(E, subst_once_r, inputs)
    if v is None:
        continue
    tested += 1
    M = max(1, max(len(s) for s in inputs))
    L = var_leaves(E)
    # (1) occurrence bound for u = 'aa'
    u = "aa"
    Cout = sum(inputs[i].count(u) for i in range(NVARS))
    lhs = v.count(u)
    rhs = L * Cout + count_const_leaves(E, lambda w: w.count(u)) \
          + 2 * len(u) * nsub(E) + len(u) * ncat(E)
    if lhs > rhs:
        bad_occ += 1
        if bad_occ < 5:
            print(f"OCC BOUND FAIL: E={E!r} inputs={inputs} v={v!r} {lhs}>{rhs}")
    # (2) linear length bound
    lhs2 = len(v)
    rhs2 = L * M + count_const_leaves(E, len)
    if lhs2 > rhs2:
        bad_len += 1
        if bad_len < 5:
            print(f"LEN BOUND FAIL: E={E!r} inputs={inputs} v={v!r} {lhs2}>{rhs2}")

print(f"tested {tested} defined evaluations")
print(f"occurrence bound violations: {bad_occ}")
print(f"linear length bound violations: {bad_len}")

# Spot-check growth: max |output| / M over expressions with L leaves, on inputs
# of length up to 12 -- should never exceed L (+ const slack).
worst = 0.0; worstE = None
for trial in range(2000):
    E = rand_expr(3, 1, CONSTS)
    s = "".join(random.choice("ab") for _ in range(random.randint(1, 12)))
    v = evalE(E, subst_once_r, [s])
    if v is None: continue
    L = var_leaves(E)
    ratio = len(v) / len(s)
    if ratio > L + 1e-9 and ratio > worst:
        worst = ratio; worstE = (E, s, v)
print(f"max observed |output|/|input| vs leaf count: {worst:.3f} (worst case kept: {worstE is not None})")
print(f"any ratio exceeding L exactly: {worstE}")
