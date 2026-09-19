"""Origin-annotated evaluator: verifies the Block/Track Decomposition.

Every character of the final output carries the identity of the LEAF
OCCURRENCE (a variable or constant leaf at a specific position in the
expression tree) and the position within that leaf's value it came from.
Claims verified on random expressions:
  (T1) for each leaf occurrence, the output positions it contributes
       appear in source order (positions within the leaf value increasing);
  (T2) the leaf's contributed positions form d disjoint ordered intervals,
       and  sum_over_leaves(d) <= #leaves + 2*#SubstNodes;
  (T3) as a consequence the output is a shuffle of at most
       #leaves + 2*#Subst "interval-subsequence reads" of leaf values.
"""
import random
from core import Var, Const, Subst, Cat

random.seed(7)
SIG = "ab"

def rand_expr(depth, nvars, consts):
    if depth == 0 or random.random() < 0.35:
        if random.random() < 0.5:
            return Var(random.randrange(nvars))
        return Const(random.choice(consts))
    if random.random() < 0.2:
        return Cat(rand_expr(depth - 1, nvars, consts),
                   rand_expr(depth - 1, nvars, consts))
    return Subst(rand_expr(depth - 1, nvars, consts),
                 rand_expr(depth - 1, nvars, consts),
                 rand_expr(depth - 1, nvars, consts))

# assign a unique id to every leaf occurrence
def tag_leaves(E, counter, D):
    if isinstance(E, (Var, Const)):
        D[id(E)] = counter[0]; counter[0] += 1
    elif isinstance(E, Cat):
        tag_leaves(E.a, counter, D); tag_leaves(E.b, counter, D)
    else:
        tag_leaves(E.R, counter, D); tag_leaves(E.P, counter, D); tag_leaves(E.E, counter, D)

def nleaves(E):
    if isinstance(E, (Var, Const)): return 1
    if isinstance(E, Cat): return nleaves(E.a) + nleaves(E.b)
    return nleaves(E.R) + nleaves(E.P) + nleaves(E.E)

def nsub(E):
    if isinstance(E, (Var, Const)): return 0
    if isinstance(E, Cat): return nsub(E.a) + nsub(E.b)
    return 1 + nsub(E.R) + nsub(E.P) + nsub(E.E)

def evalA(E, inputs, D):
    """Returns list of (char, leaf_tag, pos_in_leaf_value) or None."""
    if isinstance(E, Var):
        s = inputs[E.i]
        return [(c, D[id(E)], i) for i, c in enumerate(s)]
    if isinstance(E, Const):
        return [(c, D[id(E)], i) for i, c in enumerate(E.w)]
    if isinstance(E, Cat):
        a = evalA(E.a, inputs, D); b = evalA(E.b, inputs, D)
        if a is None or b is None: return None
        return a + b
    # Subst
    v = evalA(E.E, inputs, D)
    p = evalA(E.P, inputs, D)
    r = evalA(E.R, inputs, D)
    if v is None or p is None or r is None: return None
    ps = "".join(t[0] for t in p)
    if ps == "": return None
    rs = "".join(t[0] for t in r)
    vs = "".join(t[0] for t in v)
    i = vs.rfind(ps)
    if i < 0:
        return v
    return v[:i] + r + v[i + len(ps):]

CONSTS = ["", "a", "b", "ab", "ba", "aab", "bba"]
bad_order = bad_intervals = tested = 0
max_ratio = 0.0
for trial in range(4000):
    E = rand_expr(3, 2, CONSTS)
    D = {}
    tag_leaves(E, [0], D)
    inputs = ["".join(random.choice(SIG) for _ in range(random.randint(0, 6)))
              for _ in range(2)]
    out = evalA(E, inputs, D)
    if out is None:
        continue
    tested += 1
    # (T1) order per leaf tag
    last = {}
    for ch, tag, pos in out:
        if tag in last and pos <= last[tag]:
            bad_order += 1
            print(f"ORDER FAIL: E={E!r} inputs={inputs}")
            break
        last[tag] = pos
    # (T2) interval count
    per_tag = {}
    for ch, tag, pos in out:
        per_tag.setdefault(tag, []).append(pos)
    total_intervals = 0
    for tag, poss in per_tag.items():
        d = 1 + sum(1 for a, b in zip(poss, poss[1:]) if b != a + 1)
        total_intervals += d
    bound = nleaves(E) + 2 * nsub(E)
    if total_intervals > bound:
        bad_intervals += 1
        if bad_intervals < 4:
            print(f"INTERVAL FAIL: E={E!r} inputs={inputs} "
                  f"total={total_intervals} bound={bound}")
    max_ratio = max(max_ratio, total_intervals / max(1, bound))

print(f"tested {tested} defined evaluations")
print(f"(T1) order violations: {bad_order}")
print(f"(T2) interval-count violations: {bad_intervals} "
      f"(max achieved ratio total/bound = {max_ratio:.2f})")
