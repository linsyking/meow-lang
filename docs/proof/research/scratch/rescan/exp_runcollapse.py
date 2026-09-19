"""Experiment 7: hard verification of the run-collapse-in-L construction, and
per-pair search: is every TOTAL unary [A/B]^u L-expressible by constant pipelines?

Construction found: runcollapse = [e/ab][e/aba][aab/a] (rightmost pass first:
aab/a, then e/aba, then e/ab).
"""
import itertools
import random
from substlib import eq_unsafe, subst_safe, all_strings

CAP = 3000


def U(A, B_, C):
    return eq_unsafe(A, B_, C, CAP)


def runcollapse(S):
    out = []
    prev = None
    for ch in S:
        if ch == "a" and prev == "a":
            continue
        out.append(ch)
        prev = ch
    return "".join(out)


def rc_L(S):
    s = subst_safe("aab", "a", S)
    s = subst_safe("", "aba", s)
    s = subst_safe("", "ab", s)
    return s


if __name__ == "__main__":
    # exhaustive over {a,b} up to 14, {a,b,c} up to 9, plus a^300 and randoms
    bad = 0
    for S in all_strings("ab", 14):
        if rc_L(S) != runcollapse(S):
            bad += 1
            if bad < 5:
                print("MISMATCH", S, rc_L(S), runcollapse(S))
    print(f"exhaustive |S|<=14 over {{a,b}}: {'OK' if not bad else bad}")
    bad = 0
    for S in all_strings("abc", 9):
        if rc_L(S) != runcollapse(S):
            bad += 1
            if bad < 5:
                print("MISMATCH3", S, rc_L(S), runcollapse(S))
    print(f"exhaustive |S|<=9 over {{a,b,c}}: {'OK' if not bad else bad}")
    random.seed(7)
    bad = 0
    for _ in range(3000):
        n = random.randint(15, 60)
        S = "".join(random.choice("ab") for _ in range(n))
        if rc_L(S) != runcollapse(S):
            bad += 1
            if bad < 5:
                print("MISMATCH-rand", S, rc_L(S), runcollapse(S))
    print(f"3000 random strings len 15-60: {'OK' if not bad else bad}")
    for m in [50, 100, 300]:
        if rc_L("a" * m) != "a":
            print("MISMATCH a^", m)
    for m in [20, 50]:
        if rc_L("b" + "a" * m) != "ba":
            print("MISMATCH b a^", m)
        if rc_L("a" * m + "b") != "ab":
            print("MISMATCH a^ b", m)
    print("long pure-a / boundary cases: done")

    # Per-pair: is total unary [A/B]^u expressible by constant L-pipelines?
    def search_pair(A, B_, depth=3, maxR=3, maxP=3, wit_extra=()):
        W = all_strings("ab", 8)
        W += ["".join(x) for x in wit_extra]
        W += ["a" * 12, "b" * 12, "ab" * 8, "ba" * 8, "a" * 12 + "b" * 7, "b" * 7 + "a" * 12,
              "ab" * 5 + "a" * 9, ("ab" + "a" * 3) * 4]
        W = list(dict.fromkeys(W))
        TGT = [U(A, B_, s) for s in W]
        if any(t == "DIVERGE" for t in TGT):
            return "PARTIAL-PAIR"
        Rs = ["".join(p) for n in range(0, maxR + 1) for p in itertools.product("ab", repeat=n)]
        Ps = ["".join(p) for n in range(1, maxP + 1) for p in itertools.product("ab", repeat=n)]
        passes = [(R, P) for R in Rs for P in Ps]
        # order witnesses by length (short = fast discrimination)
        order = sorted(range(len(W)), key=lambda i: len(W[i]))
        WO = [W[i] for i in order]
        TO = [TGT[i] for i in order]
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
                found = list(acc)
                return
            for (R, P) in passes:
                acc.append((R, P))
                rec(k + 1, acc)
                acc.pop()
                if found is not None:
                    return

        rec(0, [])
        return found

    pairs = [("a", "aa"), ("ab", "ba"), ("ba", "ab"), ("aab", "ba"), ("a", "ab"),
             ("b", "ab"), ("bba", "ab"), ("ab", "a"), ("bb", "ab"), ("ba", "aab"),
             ("aab", "ab"), ("aa", "ab"), ("b", "ba"), ("ab", "b")]
    for A, B_ in pairs:
        r = search_pair(A, B_)
        print(f"pair (A={A!r}, B={B_!r}): {'NOT FOUND' if r is None else ('diverges' if r == 'PARTIAL-PAIR' else r)}")
