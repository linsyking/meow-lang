"""escape_f / unescape_f round trips under r2l, plus paper-remark reproductions.

Paper's escape theorem: f: U -> V bijection with fixed point u_k; (H1) u_1 = u_k
enumerated first; (H2) x not in V. escape_f(S) = rep_n(S, u_1, u_k f(u_1), ...),
unescape_f(S) = rep_n(S, u_k f(u_1), u_1, ...).

We test, for l2r and r2l, with the ORIGINAL rep construction and the MIRRORED one:
  (a) round trip with all valid (H1,H2) choices,
  (b) round trip with extra hypotheses,
  (c) the paper's Remark failure cases (no H1) as controls.
Also: reproduce the paper's Remark rep_n failure for l2r (X_i ending with x).
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


def escape_truth(S, U, f, u1):
    out = []
    for c in S:
        if c in U:
            out.append(u1 + f[c])
        else:
            out.append(c)
    return "".join(out)


def test_paper_remark():
    """Reproduce the paper's Remark (rem:rep-hyp) l2r failure."""
    sigma = ("s1", "s2")  # b = s1, x = s2
    rep = make_rep(subst_l2r, sigma, 2)
    S = "s1s2s1s1s2"
    X1, Y1 = "s1s2", "s2s2s2s1"
    X2, Y2 = "s2s2s2", "s1s1"
    got = rep(S, [(X1, Y1), (X2, Y2)])
    paper_says = "s2s2s2s1s1s1s2"
    want = freeze_rep(S, [(X1, Y1), (X2, Y2)], rightmost=False)
    print("paper remark l2r: got =", got)
    print("  paper says construction gives:", paper_says, "| match:", got == paper_says)
    print("  leftmost-freezing (correct):", want)
    print()


def main():
    test_paper_remark()
    for sigma in [("b", "x", "c"), ("b", "x", "c", "d")]:
        Ss = all_strings(sigma, 5)
        chars = list(sigma)
        # enumerate (b,x) fixed as sigma[0],sigma[1]; U subsets, bijections f with a fixed point
        configs = []
        for r in range(1, len(chars) + 1):
            for U in itertools.combinations(chars, r):
                fixed = [u for u in U]  # fixed point must be in U and f(u)=u
                # f: U -> V injective (then bijective onto V) with some fixed point
                for V in itertools.permutations(chars, r):
                    f = dict(zip(U, V))
                    if len(set(f.values())) < r:
                        continue
                    fps = [u for u in U if f[u] == u]
                    if not fps:
                        continue
                    for u1 in fps:  # (H1): the fixed point enumerated first
                        rest = [u for u in U if u != u1]
                        configs.append((U, f, u1, rest))
        seen = set()
        uniq = []
        for c in configs:
            key = (c[0], tuple(sorted(c[1].items())), c[2], tuple(c[3]))
            if key not in seen:
                seen.add(key); uniq.append(c)
        configs = uniq
        print(f"[{sigma}] escape configs to test: {len(configs)}")

        for sem, semname, repmaker, constname, scheme in [
            (subst_l2r, "l2r", make_rep, "orig", "paper"),
            (subst_r2l, "r2l", make_rep, "orig", "paper"),
            (subst_r2l, "r2l", make_rep_mirror, "mirror", "paper"),
            (subst_r2l, "r2l", make_rep_mirror, "mirror", "mirror-scheme"),
        ]:
            stats = {}
            for (U, f, u1, rest) in configs:
                V = set(f.values())
                H2 = sigma[1] not in V
                strongV = not (V & set(sigma[:2]))          # V disjoint from {b,x}
                u1nex = u1 != sigma[1]                      # u1 != x
                order = [u1] + rest
                if scheme == "paper":
                    # paper's pair structure: u -> u1 f(u); unescape: u1 f(u) -> u
                    esc_pairs = [(u, u1 + f[u]) for u in order]
                    une_pairs = [(u1 + f[u], u) for u in order]
                else:
                    # mirrored scheme: u -> f(u) u1 ; unescape: f(u) u1 -> u
                    esc_pairs = [(u, f[u] + u1) for u in order]
                    une_pairs = [(f[u] + u1, u) for u in order]
                n = len(order)
                repE = repmaker(sem, sigma, n)
                for tag, ok in [("H1H2", H2), ("H1H2+Vbxdj", H2 and strongV),
                                ("H1H2+u1nex", H2 and u1nex), ("noH2", not H2),
                                ("ALL", True)]:
                    if not ok:
                        continue
                    st = stats.setdefault(tag, [0, 0, None])
                    for S in Ss:
                        E = repE(S, esc_pairs)
                        D = repE(E, une_pairs)
                        st[0] += 1
                        if D != S:
                            st[1] += 1
                            if st[2] is None:
                                st[2] = (S, U, dict(f), u1, E, D)
            for tag, (t, fl, first) in sorted(stats.items()):
                print(f"  {semname}/{constname}/{scheme} [{tag}]: tested={t} fails={fl} "
                      f"{'first=' + repr(first) if first else ''}")
        print()


if __name__ == "__main__":
    main()
