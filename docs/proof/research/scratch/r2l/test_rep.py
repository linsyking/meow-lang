"""rep_n under r2l semantics vs the freezing semantics.

Questions:
(1) sanity: original construction + l2r == leftmost-freezing (paper's theorem),
    on instances satisfying the paper's hypothesis H: |X_i|=1 or X_i not ending in x.
    Also reproduce the paper's Remark failure (X_i ending in x) for l2r.
(2) original construction + r2l == rightmost-freezing?  (expect FAILURES under H)
(3) original construction + r2l under stronger hypothesis H+:
    every |X_i|>=2 pattern ends with a character not in {b,x} (needs |Sigma|>=3).
(4) mirrored construction + r2l == rightmost-freezing under mirrored hypothesis
    HM: |X_i|=1 or X_i not beginning with x.
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l
from toolkit import make_rep, make_rep_mirror, freeze_rep


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def run(sigma, n, xs_len, ys_len, s_len, hypothesis, sem, repfun, freezing):
    """Enumerate instances satisfying `hypothesis(pairs)`; return (tested, fails)."""
    b, x = sigma[0], sigma[1]
    Xs = [s for s in all_strings(sigma, xs_len) if s]
    Ys = all_strings(sigma, ys_len)
    Ss = all_strings(sigma, s_len)
    tested = fails = 0
    first = None
    for S in Ss:
        for pairs in itertools.product(itertools.product(Xs, Ys), repeat=n):
            if not hypothesis(pairs):
                continue
            tested += 1
            got = repfun(S, list(pairs))
            want = freeze_rep(S, list(pairs), rightmost=(freezing == "right"))
            if got != want:
                fails += 1
                if first is None:
                    first = (S, pairs, got, want)
    return tested, fails, first


def hyp_paper(pairs):
    """|X_i| = 1 or X_i does not end with x (x = second char of sigma)."""
    # NOTE: x is fixed by caller context; we use closure via global SIGMA
    x = SIGMA[1]
    return all(len(X) == 1 or not X.endswith(x) for X, Y in pairs)


def hyp_paper_mirror(pairs):
    x = SIGMA[1]
    return all(len(X) == 1 or not X.startswith(x) for X, Y in pairs)


def hyp_strong(pairs):
    b, x = SIGMA[0], SIGMA[1]
    return all(len(X) == 1 or X[-1] not in (b, x) for X, Y in pairs)


def hyp_true(pairs):
    return True


if __name__ == "__main__":
    for sigma in [("b", "x"), ("b", "x", "c")]:
        for n in (1, 2):
            SIGMA = sigma  # closure hack for hypothesis functions
            repL = make_rep(subst_l2r, sigma, n)
            repR = make_rep(subst_r2l, sigma, n)
            repM = make_rep_mirror(subst_r2l, sigma, n)

            t, f, first = run(sigma, n, 2, 2, 5, hyp_paper, subst_l2r, repL, "left")
            print(f"[{sigma}] n={n} orig+l2r vs leftmost-freez (paper hyp): tested={t} fails={f} first={first}")

            t, f, first = run(sigma, n, 2, 2, 5, hyp_paper, subst_r2l, repR, "right")
            print(f"[{sigma}] n={n} orig+r2l vs rightmost-freez (paper hyp): tested={t} fails={f} first={first}")

            t, f, first = run(sigma, n, 2, 2, 5, hyp_strong, subst_r2l, repR, "right")
            print(f"[{sigma}] n={n} orig+r2l vs rightmost-freez (strong hyp): tested={t} fails={f} first={first}")

            t, f, first = run(sigma, n, 2, 2, 5, hyp_paper_mirror, subst_r2l, repM, "right")
            print(f"[{sigma}] n={n} mirrored+r2l vs rightmost-freez (mirror hyp): tested={t} fails={f} first={first}")

            t, f, first = run(sigma, n, 2, 2, 5, hyp_true, subst_r2l, repM, "right")
            print(f"[{sigma}] n={n} mirrored+r2l vs rightmost-freez (NO hyp): tested={t} fails={f} first={first}")
            print()
