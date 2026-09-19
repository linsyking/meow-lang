"""Total rep variant: patch each rename pattern E_Xi -> E_Xi * G_i with
G_i = if(eq(X_i, eps), m_{n+3}, eps), i.e. G_i = m_{n+3} if X_i = eps else eps.

Expected semantics: rounds with X_i = eps act as the identity, so the value
is rep over the nonempty patterns only (in order). The naive guard
if(eq, id, round) fails by eagerness; this pattern-level guard must not.
"""
import sys
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/paper_variants')
from verify_variants import enc2, dec2, subst, rep_ref, strings_upto


def repC_comma_total(b, x, pairs, S, sigma):
    """repC_comma with guarded rename patterns; total for all inputs."""
    n = len(pairs)
    U = x + b * (n + 4)                    # m_{n+3} = x b^{n+4}
    T = enc2(subst, b, x, S, sigma)
    for i, (Xi, _) in enumerate(pairs, 1):
        EXi = enc2(subst, b, x, Xi, sigma)
        G = U if Xi == '' else ''          # if(eq(X_i, eps), U, eps)
        T = subst(x + b * (i + 1), EXi + G, T)   # rename [m_i / E_Xi G]
        T = subst(EXi + b, x + b * (i + 2), T)   # repair [E_Xi b / m_{i+1}]
    for i in range(len(pairs), 0, -1):
        T = subst(enc2(subst, b, x, pairs[i - 1][1], sigma), x + b * (i + 1), T)
    return dec2(subst, b, x, T, sigma)


ok = True
for sigma in ['ab', 'abc']:
    mx = 4 if sigma == 'ab' else 3
    b, x = sigma[0], sigma[1]
    n_eval = n_bad = 0
    # n = 1..3 rounds; to keep the domain finite, at least one eps pattern
    from itertools import product
    XY = [(X, Y) for X in strings_upto(sigma, 1) for Y in strings_upto(sigma, 1)]
    for n in (1, 2, 3):
        for pairs in product(XY, repeat=n):
            has_eps = any(X == '' for X, _ in pairs)
            if not has_eps:
                continue                     # all-nonempty covered by old checks
            for S in strings_upto(sigma, 4):
                got = repC_comma_total(b, x, list(pairs), S, sigma)
                want = rep_ref([(X, Y) for X, Y in pairs if X != ''], S)
                n_eval += 1
                if got != want:
                    n_bad += 1
                    if n_bad <= 5:
                        print("  FAIL", sigma, pairs, S, got, want)
    print(f"[total-rep {sigma}] {n_eval} evals, {n_bad} failures")
    ok &= (n_bad == 0)

print("ALL OK" if ok else "FAILURES")
