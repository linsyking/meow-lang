"""R3: THE WITNESSES, as genuine L-expressions, machine-verified.

THE RESULT (binary alphabet Sigma = {a,b}):

  W  =  [a/ab][ab/aa][b/ba][ab/b][aa/a]      (paper order; 5 constant passes)
       run order:  [a->aa] [b->ab] [ba->b] [aa->ab] [ab->a]
  W  computes  rep1b = "replace the leftmost b by a"  = [a/b]_1
       EXACTLY on all binary strings.  No guards, no tricks: five passes.

  del1b(X) = [a/b]_1-based:  if(contains(X,b), tail(W(X)), X)
       computes "delete the leftmost b" = [eps/b]_1 EXACTLY on all binary
       strings.  The key lemma: when X has a b, W(X) = rep1b(X) has a
       leading a-run of length n0+1 (the replacement 'a' merges into the
       prefix run, or sits at position 0 when X starts with b), so ONE
       head-trim (tail) deletes an 'a' from exactly that run, and
       tail(rep1b(X)) = del1b(X).

MECHANISM (the parity cascade -- why it works):
  Write X = a^n0 b a^n1 b ... b a^nt.
  pass1 [a->aa]     doubles every a-run:                    gaps 2n_j
  pass2 [b->ab]     inserts 'a' before every b:             gaps before
                    b's get +1:  n0 -> 2n0+1, n_j -> 2n_j+1
  pass3 [ba->b]     deletes one 'a' after every b:          post-b gaps -1:
                    gaps 1.. even again; gap 0 KEEPS its +1
                    (the prefix before the first b is the only region
                    that is before-a-b but never after-a-b)
  => after pass 3 the FIRST pre-b gap is the unique ODD one.
  pass4 [aa->ab]    greedy pairs 'aa' from the left of each run:
                    odd run  a^{2m+1} -> (ab)^m . a   (residue 'a' at the
                                                     very end of the run)
                    even run a^{2m}   -> (ab)^m      (ends in 'b')
  => now the junction before the FIRST b reads ...a.b (residue then b),
     while the junction before every LATER b reads ...b.b (the (ab)-block
     ends in 'b'): the first b is the unique b preceded by an 'a'.
  pass5 [ab->a]    greedy collapse: every (ab) block -> 'a'.  The greedy
                    scan resumes at the residue 'a' before the first b,
                    pairs it with that b, and EATS THE FIRST B; before
                    every later b it resumes ON the block-final 'b', finds
                    no 'ab' there, and the b survives.
  => net: gap 0 gains one 'a' (the surviving residue), the first b is
     gone:  W(X) = a^{n0+1} a^{n1} b a^{n2} ... = [a/b]_1 X.

Parts:
  w     Python-level exactness of W (large domains) + tail-trim lemma
  ast   the same as GENUINE L-ASTs (toolkit builders + K/V/C/S only),
        evaluated by the cross-verified ev_eager (rec/lazy_pass/core.py)
  mech  stage-by-stage parity table + edge cases
  lift  status over larger alphabets (documented failure, R4 target)
"""
import itertools
import random
import sys
import time

sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/rec/lazy_pass')

from core import K, V, C, S, ev_eager
import toolkit as LPTK
from oncecore import binstrings, del1b, rep1b, subst

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


# the witness, run order (P -> R means s.replace(P, R))
W_RUN = [('a', 'aa'), ('b', 'ab'), ('ba', 'b'), ('aa', 'ab'), ('ab', 'a')]

# as paper-order (A,B) pairs for the builders:  [A/B] = replace B by A
W_PAPER = [('aa', 'a'), ('ab', 'b'), ('b', 'ba'), ('ab', 'aa'), ('a', 'ab')]


def W_py(X):
    for (P, R) in W_RUN:
        X = X.replace(P, R)
    return X


def del1b_candidate(X):
    if 'b' not in X:
        return X
    return W_py(X)[1:]


# ======================================================================= w
def part_w():
    n = 0
    bad = []
    for L in range(12):
        for t in itertools.product('ab', repeat=L):
            X = ''.join(t)
            n += 1
            if W_py(X) != rep1b(X):
                bad.append(('rep1b', X, W_py(X), rep1b(X)))
            if del1b_candidate(X) != del1b(X):
                bad.append(('del1b', X, del1b_candidate(X), del1b(X)))
    log(f"w: W == [a/b]_1 and guarded-tail(W) == [eps/b]_1 on all {n} "
        f"binary strings <= 11: {len(bad)} failures" + (f" {bad[:4]}" if bad else ""))

    rng = random.Random(11)
    b2 = 0
    for _ in range(400000):
        X = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 60)))
        if W_py(X) != rep1b(X) or del1b_candidate(X) != del1b(X):
            b2 += 1
    log(f"w: 400000 random binary strings <= 59: {b2} failures")

    # the tail-trim lemma in isolation: tail(rep1b(X)) == del1b(X) on b-strings
    lem = 0
    for X in binstrings(11):
        if 'b' in X and rep1b(X)[1:] != del1b(X):
            lem += 1
    log(f"w: tail-trim lemma (tail([a/b]_1 X) == [eps/b]_1 X when b occurs): "
        f"{lem} failures over {len(binstrings(11))} strings <= 11")


# ===================================================================== ast
def W_ast():
    return LPTK.pipe(W_PAPER, V(0))


def del1b_ast(sg):
    cond = LPTK.contains(sg, V(0), K('b'))
    return LPTK.if_(sg, cond, LPTK.tail(sg, W_ast()), V(0))


def ev(ast, X):
    return ev_eager({}, ast, [X])


def part_ast():
    sg = LPTK.BIN
    W = W_ast()
    D = del1b_ast(sg)
    nw = 0
    for L in range(11):
        for t in itertools.product('ab', repeat=L):
            X = ''.join(t)
            nw += 1
            got = ev(W, X)
            if got != rep1b(X):
                log(f"  ast rep1b FAIL at {X!r}: {got!r}")
                return
    log(f"ast: W as a genuine L-AST (5 nested S-nodes, no guards) == [a/b]_1 "
        f"on all {nw} binary strings <= 10 (ev_eager)")

    rng = random.Random(13)
    bw = 0
    for _ in range(20000):
        X = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 50)))
        if ev(W, X) != rep1b(X):
            bw += 1
    log(f"ast: 20000 random binary strings <= 49 (ev_eager): {bw} failures")

    t0 = time.time()
    nd = 0
    for L in range(9):
        for t in itertools.product('ab', repeat=L):
            X = ''.join(t)
            nd += 1
            got = ev(D, X)
            if got != del1b(X):
                log(f"  ast del1b FAIL at {X!r}: {got!r}")
                return
    log(f"ast: del1b = if(contains b, tail(W), X) as a genuine L-AST "
        f"(toolkit guards) == [eps/b]_1 on all {nd} binary strings <= 8 "
        f"(ev_eager), {time.time()-t0:.0f}s")

    rng = random.Random(17)
    bd = 0
    for _ in range(3000):
        X = ''.join(rng.choice('ab') for _ in range(rng.randrange(0, 40)))
        if ev(D, X) != del1b(X):
            bd += 1
    log(f"ast: 3000 random binary strings <= 39 (ev_eager): {bd} failures")


# ==================================================================== mech
def part_mech():
    log("mech: stage table on X = aa b aa b a (n0=2,n1=2,t=1):")
    X = 'aab' + 'aa' + 'b' + 'a'
    stages = [X]
    for (P, R) in W_RUN:
        stages.append(stages[-1].replace(P, R))
    names = ['X', '1 [a->aa]', '2 [b->ab]', '3 [ba->b]', '4 [aa->ab]',
             '5 [ab->a]']
    for nm, s in zip(names, stages):
        log(f"    {nm:12s} {s}")
    log(f"    rep1b(X)  = {rep1b(X)}   del1b(X) = {del1b(X)}")
    # gap parity after stage 3 for a family of gap vectors
    log("mech: gap parities after stage 3 (gap 0 the unique ODD pre-b gap;"
        " the trailing gap is 2n_t-1, odd but harmless -- it is never "
        "before a b, so its residue pairs with nothing and the halving "
        "nets identity there):")
    allok = True
    for (n0, n1, n2) in [(0, 0, 0), (1, 0, 2), (0, 3, 1), (2, 2, 2),
                         (5, 1, 0), (3, 0, 0), (0, 0, 3), (4, 3, 2)]:
        X = 'a' * n0 + 'b' + 'a' * n1 + 'b' + 'a' * n2
        T = X.replace('a', 'aa').replace('b', 'ab').replace('ba', 'b')
        gaps = [len(r) for r in T.split('b')]
        exp = [2 * n0 + 1, 2 * n1, max(0, 2 * n2 - 1)]
        ok = (gaps == exp)
        allok &= ok
        log(f"    n=({n0},{n1},{n2}): T3={T!r} gaps={gaps} expected={exp} "
            f"{'OK' if ok else 'MISMATCH'}")
    log(f"mech: parity account verified on the 8 sampled gap vectors: {allok}")


# ==================================================================== lift
def part_lift():
    """Document the alphabet dependence of W (target of the R4 lift)."""
    for alpha, ml in (('abc', 7), ('abcd', 6)):
        bad = 0
        n = 0
        for L in range(ml + 1):
            for t in itertools.product(alpha, repeat=L):
                X = ''.join(t)
                n += 1
                if 'b' not in X:
                    continue
                if W_py(X)[1:] != del1b(X):
                    bad += 1
        log(f"lift: W over {alpha} <= {ml}: {bad}/{n} strings fail "
            f"(c-chars interrupt the gap runs: pass-4 pairing misaligns the "
            f"residue away from the junction)")


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('w', 'all'):
        log("=== w: python-level exactness ===")
        part_w()
    if which in ('ast', 'all'):
        log("=== ast: genuine L-AST verification (ev_eager) ===")
        part_ast()
    if which in ('mech', 'all'):
        log("=== mech: mechanism documentation ===")
        part_mech()
    if which in ('lift', 'all'):
        log("=== lift: alphabet dependence ===")
        part_lift()
    log(f"total {time.time()-t0:.0f}s")
    with open('/home/cc/projects/meow-lang/docs/proof/research/scratch/once/r3.log',
              'w') as f:
        f.write('\n'.join(LOG))
