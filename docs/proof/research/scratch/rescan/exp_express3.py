"""Experiment 6: corrected searches.

(b'') run-collapse vs constant L-pipelines with EXTENDED witness set including
      pure-a strings up to length 2^depth+1 (kills the [a/aa]^k halving false
      positives which only work up to length 2^k).
(f') fixed totality check: [A/B]^u and [A/B]^r diverge on C  <=>  (B in A and B in C).
(g)  restart [a/aa]^r = run-collapse? exhaustive check.
(e') proper eps-set search: depth-2 pipeline Q over pattern/replacement pools with
      Q(S) = ''  <=>  'a' in S.
"""
import itertools
from substlib import eq_unsafe, subst_safe, all_strings

CAP = 3000


def U(A, B_, C):
    return eq_unsafe(A, B_, C, CAP)


def restart(A, B_, C, cap=6000):
    if B_ == "":
        return None
    s = C
    steps = 0
    while B_ in s:
        steps += 1
        if steps > cap:
            return "DIVERGE"
        p = s.find(B_)
        s = s[:p] + A + s[p + len(B_):]
    return s


def runcollapse(S):
    out = []
    prev = None
    for ch in S:
        if ch == "a" and prev == "a":
            continue
        out.append(ch)
        prev = ch
    return "".join(out)


if __name__ == "__main__":
    # (b'') extended witness set
    W = all_strings("ab", 7)
    W += ["a" * m for m in range(8, 21)]
    W += ["a" * m + "b" + "a" * m for m in range(0, 7)]
    W += ["b" + "a" * m for m in range(8, 17)]
    W += ["a" * m + "b" for m in range(8, 17)]
    W = list(dict.fromkeys(W))
    TGT = [runcollapse(s) for s in W]
    # order: most 'aa'-dense first (fast pruning)
    idx = sorted(range(len(W)), key=lambda i: -W[i].count("aa"))
    WO = [W[i] for i in idx]
    TO = [TGT[i] for i in idx]
    print(f"witness set size: {len(W)}")

    def search(depth, maxR, maxP, label):
        Rs = ["".join(p) for n in range(0, maxR + 1) for p in itertools.product("ab", repeat=n)]
        Ps = ["".join(p) for n in range(1, maxP + 1) for p in itertools.product("ab", repeat=n)]
        passes = [(R, P) for R in Rs for P in Ps]
        found = None
        cnt = 0

        def rec(k, acc):
            nonlocal found, cnt
            if found:
                return
            if k == depth:
                cnt += 1
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
                # quick partial evaluation on the densest witness to prune hard
                s0, t0 = WO[0], TO[0]
                cur = s0
                ok = True
                for R2, P2 in acc:
                    cur = subst_safe(R2, P2, cur)
                if cur != t0:
                    # even the first witness fails with current FULL pipeline;
                    # but more passes could fix it -- can't prune this way. skip prune.
                    pass
                rec(k + 1, acc)
                acc.pop()
                if found:
                    return

        rec(0, [])
        print(f"(b'') {label}: passes={len(passes)} searched={cnt} found={found}")

    search(3, 3, 3, "depth<=3, |A|<=3,|B|<=3 (extended witnesses incl. a^20)")
    search(4, 2, 2, "depth<=4, |A|<=2,|B|<=2")
    search(2, 4, 4, "depth<=2, |A|<=4,|B|<=4")

    # (f') fixed totality equivalence
    bad_u = bad_r = 0
    ex = []
    for A in ["".join(p) for n in range(0, 4) for p in itertools.product("ab", repeat=n)]:
        for B_ in ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]:
            for C in all_strings("ab", 5):
                pred = (B_ in A) and (B_ in C)
                u = U(A, B_, C)
                r = restart(A, B_, C)
                if (u == "DIVERGE") != pred:
                    bad_u += 1
                    if len(ex) < 4:
                        ex.append(("u", A, B_, C, u, pred))
                if (r == "DIVERGE") != pred:
                    bad_r += 1
                    if len(ex) < 4:
                        ex.append(("r", A, B_, C, r, pred))
    print(f"(f') divergence domain = (B in A and B in C): rescan violations={bad_u}, restart violations={bad_r} {ex}")

    # (g) restart [a/aa] = run-collapse?
    bad = 0
    for S in all_strings("ab", 10):
        if restart("a", "aa", S) != runcollapse(S):
            bad += 1
            if bad < 4:
                print("restart runcollapse mismatch", S)
    print(f"(g) [a/aa]^r == run-collapse on all |S|<=10: {'OK' if not bad else bad}")

    # (e') eps-set search: Q = pass2.pass1 (safe), pools as functions of S.
    def const(c):
        return (lambda S: c)

    def noa(S):
        return S.replace("a", "")

    def nob(S):
        return S.replace("b", "")

    def swp(S):
        return S.replace("a", "b")

    def swq(S):
        return S.replace("b", "a")

    def delaa(S):
        return S.replace("aa", "")

    def delab(S):
        return S.replace("ab", "")

    def delba(S):
        return S.replace("ba", "")

    def rpl(S):  # [a/S] S  = 'a' if S else ''
        return "a" if S else ""

    def rpr(S):  # [S/a] S = S with every a replaced by S (grows)
        return S.replace("a", S) if S else S

    patpool = [("a", const("a")), ("b", const("b")), ("ab", const("ab")), ("ba", const("ba")),
               ("aa", const("aa")), ("bb", const("bb")), ("X1", lambda S: S), ("noa", noa),
               ("nob", nob), ("swp", swp), ("swq", swq), ("delaa", delaa), ("delab", delab),
               ("delba", delba), ("rpl", rpl)]
    reppool = [("", const("")), ("a", const("a")), ("b", const("b")), ("ab", const("ab")),
               ("X1", lambda S: S), ("noa", noa), ("nob", nob), ("rpr", rpr)]
    Cs = all_strings("ab", 6)

    def ev_pass(rep_f, pat_f, S):
        p = pat_f(S)
        if p == "":
            return "UNDEF"
        return S.replace(p, rep_f(S))

    hits = []
    tested = 0
    for n1, f1 in reppool:
        for m1, g1 in patpool:
            for n2, f2 in reppool:
                for m2, g2 in patpool:
                    tested += 1
                    ok = True
                    for S in Cs:
                        v1 = ev_pass(f1, g1, S)
                        if v1 == "UNDEF":
                            val = "UNDEF"
                        else:
                            val = ev_pass(f2, g2, v1)
                        want = "" if "a" in S else "NONEMPTY"
                        got = "UNDEF" if val == "UNDEF" else ("" if val == "" else "NONEMPTY")
                        if got != want:
                            ok = False
                            break
                    if ok:
                        hits.append((n1, m1, n2, m2))
    print(f"(e') eps-set depth-2 search over richer pool: tested={tested}, hits={hits}")
