"""Verify the paper's toolkit constructions under r2l semantics (and l2r as control).

- enc/dec round trip, enc = morphism, enc image has no bb
- cat(X,Y) = XY
- tail(aS) = S, head(aS) = a
- eq(X,Y) in {top,bot}, if(C,X,Y) selector
Ground truth is computed directly, independent of any substitution.
"""
import itertools
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/r2l")
from sem import subst_l2r, subst_r2l
from toolkit import make_toolkit


def all_strings(alpha, maxlen):
    out = [""]
    for n in range(1, maxlen + 1):
        out += ["".join(t) for t in itertools.product(alpha, repeat=n)]
    return out


def main():
    total = 0
    for sigma in [("b", "x"), ("b", "x", "c"), ("b", "x", "c", "d")]:
        for sem, name in [(subst_l2r, "l2r"), (subst_r2l, "r2l")]:
            tk = make_toolkit(sem, sigma)
            b, x = tk["b"], tk["x"]
            enc, dec, cat, tail, head = tk["enc"], tk["dec"], tk["cat"], tk["tail"], tk["head"]
            Ss = all_strings(sigma, 5)
            n = 0
            for S in Ss:
                E = enc(S)
                if "bb" in E and b + b == "bb":  # no bb in image (b^2 not substring)
                    n += 1; print("  enc bb fail", S) if n <= 3 else None
                if dec(E) != S:
                    n += 1; print("  roundtrip fail", S, E, dec(E)) if n <= 3 else None
                for T in Ss:
                    if enc(S + T) != enc(S) + enc(T):
                        n += 1; print("  morphism fail", S, T) if n <= 3 else None
            print(f"[{sigma}] {name}: enc/dec/morphism failures = {n}")
            total += n

            n = 0
            for X in Ss:
                for Y in Ss:
                    if cat(X, Y) != X + Y:
                        n += 1
                        if n <= 3: print("  cat fail", X, Y, cat(X, Y))
            print(f"[{sigma}] {name}: cat failures = {n}")
            total += n

            n = 0
            for X in Ss:
                want = X[1:] if X else ""
                if tail(X) != want:
                    n += 1
                    if n <= 3: print("  tail fail", repr(X), tail(X), want)
                want = X[:1] if X else ""
                if head(X) != want:
                    n += 1
                    if n <= 3: print("  head fail", repr(X), head(X), want)
            print(f"[{sigma}] {name}: tail/head failures = {n}")
            total += n

            # eq / if: pick top != bot, and top != b for `if`
            tops = [c for c in sigma if c != b]
            top = tops[0]
            bot = b if b != top else tops[1]
            assert top != bot
            eq, if_ = tk["eq"], tk["if_"]
            n = 0
            for X in all_strings(sigma, 4):
                for Y in all_strings(sigma, 4):
                    want = top if X == Y else bot
                    got = eq(X, Y, top, bot)
                    if got != want:
                        n += 1
                        if n <= 3: print("  eq fail", X, Y, got, want)
            print(f"[{sigma}] {name}: eq failures = {n}")
            total += n

            n = 0
            for C in [top, bot]:
                for X in all_strings(sigma, 4):
                    for Y in all_strings(sigma, 4):
                        want = X if C == top else Y
                        got = if_(C, X, Y, top, bot)
                        if got != want:
                            n += 1
                            if n <= 3: print("  if fail", C, X, Y, got, want)
            print(f"[{sigma}] {name}: if failures = {n}")
            total += n
    print("TOTAL FAILURES:", total)


if __name__ == "__main__":
    main()
