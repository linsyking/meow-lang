"""Corrected (d) and (e): |B| <= 3 restriction; block in the right order."""
import sys
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/paper_variants')
from verify_variants import strings_upto, restart

print("=== (d-fixed) growth census, total rules |A|,|B| <= 3 (A may be eps) ===")
# divergence over inputs <= 9, |A| <= 3, |B| <= 3
div = set()
for A in strings_upto('ab', 3):
    for B in strings_upto('ab', 3):
        if not B or B in A:
            continue
        for C in strings_upto('ab', 9):
            if restart(A, B, C, cap=2000) is None:
                div.add((A, B))
                break
tot = [(A, B) for A in strings_upto('ab', 3) for B in strings_upto('ab', 3)
       if B and (A, B) not in div and not (A == B or B in A)]
print(f"[d] divergent (B in A excluded by proof, plus run-found): {sorted(div)}")
print(f"[d] total rules with |A|,|B| <= 3: {len(tot)}")


def M(rule, n):
    A, B = rule
    return max(len(restart(A, B, C, cap=100000)) for C in strings_upto('ab', n))


exp, sup, lin = [], [], []
for rule in tot:
    m10, m12 = M(rule, 10), M(rule, 12)
    if m12 >= 2 * m10 and m12 >= 32:
        exp.append((rule, m12))
    elif m12 >= 18:
        sup.append((rule, m12))
    else:
        lin.append(rule)
print(f"[d] exponential: {len(exp)} -> {exp}")
print(f"[d] superlinear (<= 3n): {len(sup)} -> {sup}")
print(f"[d] linear/bounded: {len(lin)}")

print("=== (e-fixed) block: [baa/ab]^m . [ab/aa]^m on b^m a^K (right order) ===")
bad = 0
for m in range(0, 4):
    for K in range(0, 9):
        S = 'b' * m + 'a' * K
        t1 = restart('ab', 'aa', S, cap=100000)          # first: aa -> ab
        t2 = restart('baa', 'ab', t1, cap=100000)        # then: amplifier
        want = 'b' * (m + K // 2) + 'a' * (2 ** (K // 2 + 1) - 2 + K % 2)
        if t2 != want:
            bad += 1
            if bad <= 5:
                print("  FAIL", m, K, t2, want)
print(f"[e] {4 * 9} evals, {bad} failures")
