"""Experiment 8: sound per-pair search: is total unary [A/B]^u expressible in L
by constant pipelines? Deep search with proper witnesses + post-verification.

Witnesses: all strings <= 8 over {a,b}, plus a^m, b^m, (ab)^m, (ba)^m, a^m b^n,
b^n a^m for m,n up to 16. Post-check any found pipeline on 2000 random strings
up to length 40 + a^60 (to kill halving-style false positives).
"""
import itertools
import random
from substlib import eq_unsafe, subst_safe, all_strings

CAP = 3000


def U(A, B_, C):
    return eq_unsafe(A, B_, C, CAP)


def build_witnesses():
    W = all_strings("ab", 7)
    for m in range(9, 17):
        W.append("a" * m)
        W.append("b" * m)
        W.append("ab" * (m // 2) + "a" * (m % 2))
        W.append("ba" * (m // 2) + "b" * (m % 2))
        W.append("a" * m + "b" * (m // 2))
        W.append("b" * (m // 2) + "a" * m)
        W.append("ab" * 4 + "a" * m)
        W.append("a" * m + "ab" * 4)
    return list(dict.fromkeys(W))


def deep_search(A, B_, depths_lens):
    W = build_witnesses()
    TGT = [U(A, B_, s) for s in W]
    if any(t == "DIVERGE" for t in TGT):
        return "PARTIAL"
    random.seed(3)

    def postverify(pipeline):
        for _ in range(2000):
            n = random.randint(0, 40)
            S = "".join(random.choice("ab") for _ in range(n))
            cur = S
            for R, P in pipeline:
                cur = subst_safe(R, P, cur)
            if cur != U(A, B_, S):
                return False
        for m in [30, 60]:
            cur = "a" * m
            for R, P in pipeline:
                cur = subst_safe(R, P, cur)
            if cur != U(A, B_, "a" * m):
                return False
            cur = "b" * m
            for R, P in pipeline:
                cur = subst_safe(R, P, cur)
            if cur != U(A, B_, "b" * m):
                return False
        return True

    order = sorted(range(len(W)), key=lambda i: len(W[i]))
    WO = [W[i] for i in order]
    TO = [TGT[i] for i in order]

    for depth, maxR, maxP in depths_lens:
        Rs = ["".join(p) for n in range(0, maxR + 1) for p in itertools.product("ab", repeat=n)]
        Ps = ["".join(p) for n in range(1, maxP + 1) for p in itertools.product("ab", repeat=n)]
        passes = [(R, P) for R in Rs for P in Ps]
        found = None

        def rec(k, acc):
            nonlocal found
            if found is not None:
                return
            if k == depth:
                for s, t in zip(WO, TO):
                    cur = s
                    for R, P in acc:
                        cur = subst_safe(R, P, cur)
                    if cur != t:
                        return
                cand = list(acc)
                if postverify(cand):
                    found = cand
                return
            for (R, P) in passes:
                acc.append((R, P))
                rec(k + 1, acc)
                acc.pop()
                if found is not None:
                    return

        rec(0, [])
        if found is not None:
            return found
    return None


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        pairs = [tuple(sys.argv[1:3])]
    else:
        pairs = None
    if pairs is None:
        pairs = [("a", "aa"), ("aab", "ba"), ("a", "ab"), ("bba", "ab"), ("ba", "aab"),
             ("aa", "ab"), ("b", "ba"), ("ab", "ba"), ("ba", "ab"), ("ba", "b"),
             ("ab", "bb"), ("b", "a"), ("bb", "a"), ("aab", "b"), ("ab", "aab")]
    plan = [(3, 3, 3), (4, 2, 2)]
    for A, B_ in pairs:
        r = deep_search(A, B_, plan)
        print(f"pair (A={A!r}, B={B_!r}): {'DIVERGES(B in A)' if r == 'PARTIAL' else ('NOT FOUND (deep)' if r is None else r)}", flush=True)
