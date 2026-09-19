"""Experiment 5: sound searches.

(b') Exhaustive search: does any CONSTANT-pattern baseline pipeline (depth <= 3,
     patterns/replacements length <= 3 over {a,b}; also depth <= 4, lengths <= 2)
     equal run-collapse on ALL strings up to length 8? Early exit per witness.
(e) epsilon-set search: does any small L-expression Q (constant or simple
     variable patterns) satisfy  Q(S) = eps  <=>  'a' in S ?  (needed for L to
     express the partial identity [a/a]^u; conjecture: no).
(f) restart vs rescan comparison.
"""
import itertools
from substlib import eq_unsafe, subst_safe, all_strings

CAP = 2000


def U(A, B_, C):
    return eq_unsafe(A, B_, C, CAP)


def restart(A, B_, C, cap=5000):
    """[A/B]^r C: on each match, replace and rescan the WHOLE string from 0."""
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
    WITNESSES = all_strings("ab", 8)  # 511 strings
    TGT = [runcollapse(s) for s in WITNESSES]

    # (b') sound exhaustive constant-pipeline search
    def search(depth, maxR, maxP, label):
        Rs = ["".join(p) for n in range(0, maxR + 1) for p in itertools.product("ab", repeat=n)]
        Ps = ["".join(p) for n in range(1, maxP + 1) for p in itertools.product("ab", repeat=n)]
        passes = [(R, P) for R in Rs for P in Ps]
        # order witnesses so that cheap discriminating ones come first
        order = sorted(range(len(WITNESSES)),
                       key=lambda i: -(WITNESSES[i].count("aa")))
        WO = [WITNESSES[i] for i in order]
        TO = [TGT[i] for i in order]
        found = None
        cnt = 0

        def rec(k, acc):
            nonlocal found, cnt
            if found:
                return
            if k == depth:
                cnt += 1
                # verify acc (list of passes, applied right-to-left) on all witnesses
                for s, t in zip(WO, TO):
                    cur = s
                    for R, P in acc:  # acc[0] applied FIRST
                        cur = subst_safe(R, P, cur)
                    if cur != t:
                        return
                found = list(acc)
                return
            for (R, P) in passes:
                acc.append((R, P))
                # partial check: evaluate current suffix on first witness for speed
                rec(k + 1, acc)
                acc.pop()
                if found:
                    return

        rec(0, [])
        print(f"(b') {label}: passes={len(passes)} searched={cnt} found={found}")
        return found

    search(3, 3, 3, "depth<=3, |A|<=3,|B|<=3")
    search(4, 2, 2, "depth<=4, |A|<=2,|B|<=2")
    search(2, 4, 4, "depth<=2, |A|<=4,|B|<=4")

    # (e) epsilon-set search for Q(S) = eps <=> 'a' in S
    # pool of pattern expressions (evaluated on S): constants, X1, [e/a]X1, [e/b]X1
    Sigma = "ab"
    Cs = all_strings("ab", 6)

    def pat_const(c):
        return lambda S: c

    def pat_var(S):
        return S

    def pat_noa(S):
        return S.replace("a", "")

    def pat_nob(S):
        return S.replace("b", "")

    def pat_swapa(S):  # [b/a] S
        return S.replace("a", "b")

    def pat_runcol_a(S):  # [a/aa] safe? no: use [a/aaa] safe halving as an example variable-free
        return S

    pats = [("const:" + c, (lambda c: lambda S: c)(c))
            for c in ["a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "abb", "aba", "baa", "bba"]]
    pats += [("X1", pat_var), ("noa", pat_noa), ("nob", pat_nob), ("swapa", pat_swapa)]
    reps = [("const:" + c, (lambda c: lambda S: c)(c)) for c in ["", "a", "b", "aa", "ab", "ba", "bb"]]
    reps += [("X1", pat_var), ("noa", pat_noa), ("nob", pat_nob)]

    # depth-2 pipelines of safe passes with these patterns/replacements, scrutinee X1:
    # Q = pass2 . pass1 applied to S; check Q(S) = '' <=> 'a' in S for all S in Cs
    hits = []
    tested = 0
    for (n1, f1) in reps:
        for (m1, g1) in pats:
            if g1("") == "" and m1.startswith("const"):
                continue
            for (n2, f2) in reps:
                for (m2, g2) in pats:
                    if g2("") == "" and m2.startswith("const"):
                        continue
                    tested += 1
                    ok = True
                    for S in Cs:
                        # pass 1: [f1/g1] on S (safe semantics), then pass 2
                        p1 = g1(S)
                        if p1 == "":
                            ok = False
                            break
                        mid = S.replace(p1, f1(S)) if p1 else S
                        p2 = g2(mid)
                        if p2 == "":
                            ok = False
                            break
                        val = mid.replace(p2, f2(mid))
                        want = "" if "a" in S else "NONEMPTY"
                        got = "" if val == "" else "NONEMPTY"
                        if got != want:
                            ok = False
                            break
                    if ok:
                        hits.append((n1, m1, n2, m2))
    print(f"(e) eps-set search: tested={tested} pipelines matching ('' <=> a in S): {hits}")

    # (f) restart vs rescan vs safe census
    diff_rs, diff_rr, diff_sr, agree = [], [], [], 0
    div_u, div_r = 0, 0
    for A in ["".join(p) for n in range(0, 3) for p in itertools.product("ab", repeat=n)]:
        for B_ in ["".join(p) for n in range(1, 3) for p in itertools.product("ab", repeat=n)]:
            for C in all_strings("ab", 5):
                s = subst_safe(A, B_, C)
                u = U(A, B_, C)
                r = restart(A, B_, C)
                if u == "DIVERGE":
                    div_u += 1
                if r == "DIVERGE":
                    div_r += 1
                if u != "DIVERGE" and r != "DIVERGE":
                    if u == r:
                        agree += 1
                    elif len(diff_rs) < 6 and (A, B_) not in [(d[0], d[1]) for d in diff_rs]:
                        diff_rs.append((A, B_, C, s, u, r))
                # totality-equivalence check
                if (u == "DIVERGE") != (B_ in A) or (r == "DIVERGE") != (B_ in A):
                    print("TOTALITY MISMATCH", A, B_, C, u, r)
    print(f"(f) restart vs rescan: agreeing-defined={agree}, rescan-diverged={div_u}, restart-diverged={div_r}")
    print(f"    sample differences (A,B,C, safe, rescan, restart): {diff_rs}")
