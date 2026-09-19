"""Experiment 4: expressibility.

(a) Verify [a/aa]^u = run-collapse (map every maximal a-run to a single 'a'),
    exhaustively on all strings over {a,b} up to length 10.
(b) Search L (baseline) CONSTANT-pattern pipelines for run-collapse:
    depth <= 3 with patterns/replacements up to length 3, and depth <= 4 with
    lengths <= 2, over Sigma={a,b}. Early exit on witness mismatch.
(c) Check cat via rep_2 over |Sigma|=4 (patterns a,b; rep encoding chars c,d)
    -- predicted to diverge when the concatenated data contains 'c'.
(d) Small search for core-2ary cat over Sigma={a,b} in the U-calculus.
"""
import itertools
from substlib import eq_unsafe, all_strings, subst_safe

CAP = 2000


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


if __name__ == "__main__":
    # (a)
    bad = 0
    for S in all_strings("ab", 10):
        if U("a", "aa", S) != runcollapse(S):
            bad += 1
            if bad < 4:
                print("runcollapse mismatch", S, U("a", "aa", S), runcollapse(S))
    print(f"(a) [a/aa]^u == run-collapse on all |S|<=10 over {{a,b}}: {'OK' if not bad else bad}")

    # (b) L-pipeline search: safe passes only (this is the baseline L).
    witnesses = [s for s in all_strings("ab", 8)]
    target = {s: runcollapse(s) for s in witnesses}
    # quick target on witnesses
    def matches_target(fn):
        for s in witnesses:
            if fn(s) != target[s]:
                return False
        return True

    def mk_pipeline(passes):
        def f(s):
            for R, P in passes:  # apply right-to-left: passes[0] applied LAST
                pass
            cur = s
            for R, P in reversed(passes):
                cur = subst_safe(R, P, cur)
            return cur
        return f

    # depth 1..3, patterns <= 3
    Rs = ["".join(p) for n in range(0, 4) for p in itertools.product("ab", repeat=n)]
    Ps = ["".join(p) for n in range(1, 4) for p in itertools.product("ab", repeat=n)]
    passes = [(R, P) for R in Rs for P in Ps]
    print(f"(b) pass space size (len<=3): {len(passes)}")

    # precompute: witness order by discriminating power: test on a few strings first
    quick = ["a", "aa", "aaa", "aaaa", "ba", "aba", "aab", "ab", "bb", "bab", "aabbaab", "aaabaaa", "baaa"]

    def equals_target(passes_):
        for s in quick:
            cur = s
            for R, P in reversed(passes_):
                cur = subst_safe(R, P, cur)
            if cur != runcollapse(s):
                return False
        for s in witnesses:
            cur = s
            for R, P in reversed(passes_):
                cur = subst_safe(R, P, cur)
            if cur != target[s]:
                return False
        return True

    found = None
    cnt = 0
    # depth 1
    for p1 in passes:
        cnt += 1
        if equals_target([p1]):
            found = [p1]
            break
    if not found:
        # depth 2
        for p1 in passes:
            for p2 in passes:
                cnt += 1
                if equals_target([p1, p2]):
                    found = [p1, p2]
                    break
            if found:
                break
    print(f"(b) depth<=2 search: found={found} (after {cnt} pipelines)")

    # depth 3 with pruning: first filter by behavior on quick witnesses using
    # incremental composition (compose pass lists as functions on quick set).
    qw = quick
    tgt_quick = [runcollapse(s) for s in qw]

    def eval_quick(pl):
        vals = []
        for s in qw:
            cur = s
            for R, P in reversed(pl):
                cur = subst_safe(R, P, cur)
            vals.append(cur)
        return tuple(vals)

    # generate all depth-2 behaviors on quick set, then extend
    layer2 = {}
    for p1 in passes:
        for p2 in passes:
            v = eval_quick([p1, p2])
            if v not in layer2:
                layer2[v] = [p1, p2]
    print(f"(b) distinct depth-2 behaviors on quick witnesses: {len(layer2)}")
    hit = None
    for v, pl in layer2.items():
        for p3 in passes:
            if eval_quick(pl + [p3]) == tuple(tgt_quick):
                hit = pl + [p3]
                break
        if hit:
            break
    if hit:
        print("(b) depth-3 candidate on quick witnesses:", hit, "verifying on full witness set...")
        print("   full match:", equals_target(hit))
    else:
        print("(b) depth<=3 (len<=3) search: run-collapse NOT FOUND (quick-witness filtered)")

    # depth 4 with len<=2
    Rs2 = ["".join(p) for n in range(0, 3) for p in itertools.product("ab", repeat=n)]
    Ps2 = ["".join(p) for n in range(1, 3) for p in itertools.product("ab", repeat=n)]
    passes2 = [(R, P) for R in Rs2 for P in Ps2]
    hit4 = None
    layer = {tuple(qw): []}  # identity behavior
    cur_layer = {tuple(qw): []}
    behaviors = {tuple(qw)}
    # BFS over behaviors on quick set
    frontier = {tuple(qw): []}
    for depth in range(1, 5):
        newf = {}
        for v, pl in frontier.items():
            # apply one more pass ON TOP (leftmost position = applied last)
            for (R, P) in passes2:
                # evaluate: pl passes then this pass
                nv = []
                ok = True
                for s in qw:
                    cur = s
                    for RR, PP in reversed(pl):
                        cur = subst_safe(RR, PP, cur)
                    cur = subst_safe(R, P, cur)
                    nv.append(cur)
                nv = tuple(nv)
                if nv == tuple(tgt_quick):
                    hit4 = pl + [(R, P)]
                    break
                if nv not in behaviors:
                    newf[nv] = pl + [(R, P)]
                    behaviors.add(nv)
            if hit4:
                break
        if hit4:
            break
        frontier = newf
        print(f"(b) depth {depth}: frontier size {len(frontier)}, total behaviors {len(behaviors)}")
    if hit4:
        print("(b) depth-4 candidate (len<=2):", hit4, "full match:", equals_target(hit4))
    else:
        print(f"(b) depth<=4 (len<=2) BFS exhausted: run-collapse NOT FOUND ({len(behaviors)} behaviors)")

    # (c) cat via rep_2 over Sigma={a,b,c,d}: patterns 'a','b'; rep encoding chars c,d.
    def encd(S):  # enc' with b'=c, x'=d
        return U("dc", "c", S)

    def decd(S):
        return U("c", "dc", S)

    def cat_rep2(X, Y):
        # rep_2(ab, a, X, b, Y): S='ab', X_1='a',Y_1=X, X_2='b',Y_2=Y
        # construction: dec'((prod_{i=1..2} [E_Yi/m_{i+1}]) (prod_{i=2..1} [E_Xi b'/m_{i+2}][m_i/E_Xi]) enc'(S))
        # products compose right-to-left: renaming passes run i=1,2; instantiation i=2,1
        m = lambda i: "d" + "c" * (i + 1)
        s = encd("ab")
        if s == "DIVERGE":
            return "DIVERGE"
        # renaming i=1: [m_1/E_X1] then repair [E_X1 c / m_2]... order: ([E_X1 b'/m_2][m_1/E_X1]) i=1 first
        EX1 = encd("a")
        EX2 = encd("b")
        if EX1 == "DIVERGE" or EX2 == "DIVERGE":
            return "DIVERGE"
        s = U(m(1), EX1, s)
        if s == "DIVERGE":
            return "DIVERGE"
        s = U(EX1 + "c", m(2), s)
        if s == "DIVERGE":
            return "DIVERGE"
        s = U(m(2), EX2, s)
        if s == "DIVERGE":
            return "DIVERGE"
        s = U(EX2 + "c", m(3), s)
        if s == "DIVERGE":
            return "DIVERGE"
        # instantiation i=2 then i=1: prod_{i=1<-2}: [E_Y2/m_2][E_Y1/m_1]?? right-to-left: i=2 first
        EY2 = encd(Y)
        EY1 = encd(X)
        if EY1 == "DIVERGE" or EY2 == "DIVERGE":
            return "DIVERGE"
        s = U(EY2, m(2), s)
        if s == "DIVERGE":
            return "DIVERGE"
        s = U(EY1, m(1), s)
        if s == "DIVERGE":
            return "DIVERGE"
        return decd(s)

    ok = div = wrong = 0
    exd = exw = None
    for X in all_strings("abcd", 2):
        for Y in all_strings("abcd", 2):
            r = cat_rep2(X, Y)
            if r == "DIVERGE":
                div += 1
                if exd is None:
                    exd = (X, Y)
            elif r != X + Y:
                wrong += 1
                if exw is None:
                    exw = (X, Y, r)
            else:
                ok += 1
    print(f"(c) cat via rep_2 over |Sigma|=4: ok={ok} diverged={div} (first {exd}) wrong={wrong} {exw}")

    # (d) small search: core 2-ary U-expressions for cat over {a,b}.
    # passes: [R/P] where R,P drawn from pool of simple core exprs evaluated on (X1,X2).
    def ev(e, X1, X2):
        # e: ('var',1|2) | ('const',s) | ('pass', Rexpr, Pexpr, scrutinee)
        k, v = e
        if k == "var":
            return X1 if v == 1 else X2
        if k == "const":
            return v
        raise ValueError

    pool_R = [("var", 1), ("var", 2), ("const", ""), ("const", "a"), ("const", "b"),
              ("const", "ab"), ("const", "ba")]
    pool_P = [("var", 1), ("var", 2), ("const", "a"), ("const", "b"), ("const", "ab"),
              ("const", "ba"), ("const", "aa"), ("const", "bb")]
    scrut = [("var", 1), ("var", 2), ("const", "ab"), ("const", "ba"), ("const", "aab"), ("const", "abab")]

    tests = [(X, Y) for X in all_strings("ab", 2) for Y in all_strings("ab", 2)]

    def eval_pipeline(pipeline, X1, X2):
        # pipeline = list of (R, P) applied right-to-left to scrutinee
        cur = None
        for (R, P) in reversed(pipeline):
            if cur is None:
                # rightmost pass applies to... we handle scrutinee separately
                pass
        return None

    # simpler: enumerate depth-2 pipelines of the form [R2/P2][R1/P1](scrut)
    found_cat = None
    checked = 0
    for scr in scrut:
        for R1, P1 in [(r, p) for r in pool_R for p in pool_P]:
            for R2, P2 in [(r, p) for r in pool_R for p in pool_P]:
                checked += 1
                good = True
                for X1, Y1 in tests:
                    def val(e):
                        return ev(e, X1, Y1)
                    s = val(scr)
                    for R, P in [(R1, P1), (R2, P2)]:
                        r_ = val(R)
                        p_ = val(P)
                        if p_ == "":
                            good = False
                            break
                        s = U(r_, p_, s)
                        if s == "DIVERGE":
                            good = False
                            break
                    if not good or s != X1 + Y1:
                        good = False
                        break
                if good:
                    found_cat = (scr, (R1, P1), (R2, P2))
                    break
            if found_cat:
                break
        if found_cat:
            break
    print(f"(d) core-2ary cat search (depth 2, small pools): found={found_cat} ({checked} pipelines tested)")
