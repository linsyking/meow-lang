"""Supplementary checks for the variants section of the paper.

(a) comma-code construction with restart nodes, unconditional n=1 domain:
    failure <=> X1 = b and b in S (the paper's "exactly those" claim).
(b) termination census: all 930 binary rules with |A|, |B| <= 4 (A possibly
    empty, B nonempty), run on all inputs of length <= 9:
    divergent <=> B in A or one of the four rules.
(c) minimality: no divergent rule with B not in A and |A| <= 3.
(d) growth census for total rules with |A|, |B| <= 3.
(e) exact two-node block formula of the towers corollary.
"""
import sys
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/paper_variants')
from verify_variants import strings_upto, repC_comma_restart, rep_ref, restart

CAP = 1000000  # must exceed the slow terminators: the aaab/abbb families take
# up to 3,280 leftmost steps on inputs <= 9 (misclassified as divergent at any
# cap <= 3,280; the original CAP=2000 made `extra == FOUR` fail with 8 rules)

print("=== (a) restart-comma unconditional n=1: fail <=> X1 = b and b in S ===")
evals = fails = bad = 0
for (b, x) in [('a', 'b'), ('b', 'a')]:
    for S in strings_upto('ab', 4):
        for X1 in strings_upto('ab', 2):
            if not X1:
                continue
            for Y1 in strings_upto('ab', 2):
                evals += 1
                got = repC_comma_restart(b, x, [(X1, Y1)], S, 'ab')
                want = rep_ref([(X1, Y1)], S)
                fail = got != want
                pred = (X1 == b and b in S)
                if fail != pred:
                    bad += 1
                    if bad <= 5:
                        print("  MISMATCH", b, x, X1, Y1, S, got, want)
                fails += fail
print(f"[a] {evals} evals, {fails} failures, {bad} biconditional mismatches")

print("=== (b) 930-rule divergence census ===")
FOUR = {('aabb', 'ba'), ('bbaa', 'ab'), ('abba', 'bab'), ('baab', 'aba')}
rules = [(A, B) for A in strings_upto('ab', 4) for B in strings_upto('ab', 4) if B]
assert len(rules) == 930, len(rules)
div = []
nrun = 0
for A, B in rules:
    if B in A:
        div.append((A, B))
        continue
    d = False
    for C in strings_upto('ab', 9):
        nrun += 1
        if restart(A, B, C, cap=CAP) is None:
            d = True
            break
    if d:
        div.append((A, B))
extra = [r for r in div if r[1] not in r[0]]
print(f"[b] {len(rules)} rules, {nrun} runs, {len(div)} divergent "
      f"({sum(1 for r in div if r[1] in r[0])} with B in A, {len(extra)} without)")
print(f"[b] divergent without B in A: {sorted(extra)}")
print(f"[b] extra == FOUR: {set(extra) == FOUR}")

print("=== (c) minimality: divergent with B notin A and |A| <= 3 ===")
small = [(A, B) for A, B in div if B not in A and len(A) <= 3]
print(f"[c] count = {len(small)} (expect 0)")

print("=== (d) growth census, total rules |A|,|B| <= 3 ===")
tot = []
for A, B in rules:
    if len(A) > 3:
        continue
    if (A, B) in div:
        continue
    tot.append((A, B))
print(f"[d] total rules with |A|,|B| <= 3: {len(tot)}")


def M(rule, n):
    A, B = rule
    return max(len(restart(A, B, C, cap=10000)) for C in strings_upto('ab', n))


classes = {'exp': [], 's23': [], 's1': [], 'other': []}
for rule in tot:
    m10, m12 = M(rule, 10), M(rule, 12)
    if m12 >= 2 * m10 and m12 >= 32:
        classes['exp'].append((rule, m10, m12))
    elif m12 >= 18:   # slope >= 1.5
        classes['s23'].append((rule, m12))
    elif m12 <= 13:   # slope ~ 1 (or bounded)
        classes['s1'].append((rule, m12))
    else:
        classes['other'].append((rule, m10, m12))
print(f"[d] exponential: {len(classes['exp'])} -> "
      f"{[(r, m12) for r, _, m12 in classes['exp']]}")
print(f"[d] slope>1: {len(classes['s23'])} -> {classes['s23']}")
print(f"[d] slope~1/bounded: {len(classes['s1'])}")
print(f"[d] unclassified: {classes['other']}")

print("=== (e) block [baa/ab]^m . [ab/aa]^m on b^m a^K (exact formula) ===")
bad = 0
for m in range(0, 4):
    for K in range(0, 9):
        S = 'b' * m + 'a' * K
        t1 = restart('baa', 'ab', S, cap=100000)
        t2 = restart('ab', 'aa', t1, cap=100000)
        want = 'b' * (m + K // 2) + 'a' * (2 ** (K // 2 + 1) - 2 + K % 2)
        if t2 != want:
            bad += 1
            if bad <= 5:
                print("  FAIL", m, K, t2, want)
print(f"[e] {4 * 9} evals, {bad} failures")
