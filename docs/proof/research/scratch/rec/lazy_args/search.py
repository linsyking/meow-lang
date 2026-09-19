# search.py -- exhaustive search for the SMALLEST operational separations
# between the lazy-args and eager semantics of L_rec.
#
# Search space (stated precisely, cf. REPORT.md section 8):
#   * Sigma = {a, b}; constants are ATOMS from {'', 'a'}: every constant
#     string is one node, and termination / liveness / acyclicity depend only
#     on the expression structure (the epsilon/non-epsilon distinction is the
#     only constant-value distinction that can matter, for err-vs-value).
#   * 1 or 2 functions (F, and optionally G), arities in {0, 1, 2}.
#   * Bodies: arbitrary expressions over the own parameters, pass, cat, and
#     calls to F and G with matching arities.
#   * main: any expression over the input variables containing >= 1 call node
#     (a call-free main makes the program trivially non-recursive).
#   * Program size = sum of node counts of all bodies + main.
#
# STRONG separation: lazy machine halts with a value on some input while the
# eager machine yields a value on NO input (diverges, or errs everywhere).
# WEAK separation: both halt, but eager errs on some input where lazy yields
# a value (dead argument that can err).
#
# Theorem-based filters used to cut the space (each is proved in REPORT.md):
#   - eager-halting => lazy-halting (live unfolding is a collapse of the
#     full one), so strong separation <=> lazy-halts & eager-diverges.
#   - a separating program contains a call cycle, hence some body contains a
#     call node; pools are pre-filtered accordingly.

import itertools
import sys

sys.setrecursionlimit(100000)

import lrec as L

CONSTS = ['', 'a']


def compositions(total, parts):
    if parts == 1:
        return [(total,)] if total >= 1 else []
    res = []
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            res.append((first,) + rest)
    return res


class Pools:
    """Expression pools by size, for a fixed variable count and function
    signature.  Also keeps the sub-pools containing at least one call."""

    def __init__(self, budget, nvars, fns):
        self.fns = fns
        self.nvars = nvars
        by = {1: [L.V(v) for v in range(nvars)] + [L.K(c) for c in CONSTS]}
        for g, ar in fns:
            if ar == 0:
                by[1].append(L.Call(g))
        for n in range(2, budget + 1):
            acc = []
            for i in range(1, n - 1):
                for a in by[i]:
                    for b in by[n - 1 - i]:
                        acc.append(L.Cat(a, b))
            for i in range(1, n - 2):
                for j in range(1, n - 1 - i):
                    k = n - 1 - i - j
                    for r in by[i]:
                        for p in by[j]:
                            for e in by[k]:
                                acc.append(L.Pas(r, p, e))
            for g, ar in fns:
                if ar == 0:
                    continue
                for sizes in compositions(n - 1, ar):
                    pools = [by[s] for s in sizes]
                    for tup in itertools.product(*pools):
                        acc.append(L.Call(g, *tup))
            seen, out = set(), []
            for e in acc:
                if e not in seen:
                    seen.add(e)
                    out.append(e)
            by[n] = out
        self.by = by
        self.with_call = {n: [e for e in by[n] if has_call(e)]
                          for n in by}

    def get(self, n, calls_only=False):
        if calls_only:
            return self.with_call.get(n, [])
        return self.by.get(n, [])


def has_call(E):
    t = E[0]
    if t == 'call':
        return True
    if t == 'cat':
        return has_call(E[1]) or has_call(E[2])
    if t == 'pass':
        return any(has_call(x) for x in E[1:4])
    return False


def sample_inputs(nin):
    if nin == 0:
        return [()]
    if nin == 1:
        return [('',), ('a',), ('b',), ('ab',), ('ba',)]
    return [(x, y) for x in ('', 'a', 'b') for y in ('', 'a', 'b')]


def lazy_has_value(prog, cap=3000):
    S = L.liveness(prog)
    try:
        U, _ = L.unfold(prog, S, cap=cap)
    except L.CapExceeded:
        return None
    for inp in sample_inputs(prog.ninputs):
        if L.eval_plain(U, {i: s for i, s in enumerate(inp)})[0] == 'val':
            return True
    return False


def machine_confirm_strong(prog):
    """Operational confirmation of a strong separation."""
    lz_val = eg_val = False
    eg_kinds = set()
    for inp in sample_inputs(prog.ninputs):
        m = L.Machine(prog, budget=100000)
        try:
            r = m.ev(prog.main, {i: ('inp', s) for i, s in enumerate(inp)})
            lz_val = lz_val or (r[0] == 'val')
        except (L.Timeout, RecursionError):
            eg_kinds.add('lazy?')  # should not happen for halting programs
        m = L.Machine(prog, budget=6000)
        try:
            r = m.ee(prog.main, {i: ('inp', s) for i, s in enumerate(inp)})
            eg_val = eg_val or (r[0] == 'val')
            eg_kinds.add('err' if r[0] == 'err' else 'val')
        except (L.Timeout, RecursionError):
            eg_kinds.add('diverge')
    return lz_val, eg_val, eg_kinds


def two_fn_programs(total):
    """All 2-function programs of exactly `total` nodes whose bodies and main
    satisfy the stated space; yields (program, (arF, arG))."""
    for arF in (0, 1, 2):
        for arG in (0, 1, 2):
            fns = [('F', arF), ('G', arG)]
            # pools for F bodies (nvars=arF), G bodies (nvars=arG), mains
            # (nvars=arF); budgets: bodies at most total-2 (>=1 for the other
            # body and main each)
            pF = Pools(total - 2, arF, fns)
            pG = Pools(total - 2, arG, fns)
            pM = Pools(total - 2, arF, fns)
            for nF in range(1, total - 1):
                rest = total - nF
                for nG in range(1, rest):
                    nmain = rest - nG
                    # at least one body must contain a call (recursion
                    # somewhere), else no cycle can exist
                    Fs = pF.get(nF, calls_only=True)
                    Gs = pG.get(nG)
                    Ms = pM.get(nmain, calls_only=True) if nmain >= 1 else []
                    for bodyF in Fs:
                        for bodyG in Gs:
                            for main in Ms:
                                yield (L.Program({'F': (arF, bodyF),
                                                  'G': (arG, bodyG)},
                                                 main, arF), (arF, arG))
                    if not Fs:
                        # F body has no call: G's body must carry the cycle
                        Fs0 = pF.get(nF)
                        Gs = [g for g in pG.get(nG) if has_call(g)]
                        for bodyF in Fs0:
                            for bodyG in Gs:
                                for main in Ms:
                                    yield (L.Program({'F': (arF, bodyF),
                                                      'G': (arG, bodyG)},
                                                     main, arF), (arF, arG))


def one_fn_programs(total):
    """Programs whose main and F-body both contain >= 1 call node -- the only
    ones that can possibly separate (a reachable call cycle needs a call in
    main and a call in some body; with one function the only body is F's)."""
    for arF in (0, 1, 2):
        fns = [('F', arF)]
        p = Pools(total, arF, fns)
        for n in range(1, total):
            Bs = p.get(n, calls_only=True)
            Ms = p.get(total - n, calls_only=True)
            for body in Bs:
                for main in Ms:
                    yield L.Program({'F': (arF, body)}, main, arF), arF


def search(max_total=7, one_fn_max=6, verbose=True):
    counts = {}
    strong = []
    weak = []
    # ---- one function: the lemma says none separates
    for total in range(1, one_fn_max + 1):
        n = sep = 0
        for prog, ar in one_fn_programs(total):
            n += 1
            if L.terminates_eager(prog):
                continue          # eager halts => lazy halts => no separation
            if L.terminates_lazy(prog):
                sep += 1
                print("  !!! ONE-FUNCTION SEPARATION (contradicts lemma):")
                print(prog.show())
        counts[('1fn', total)] = (n, sep)
        if verbose:
            print(f"  1-function programs of size {total}: {n} scanned,"
                  f" {sep} separations (lemma: 0)")
    # ---- two functions
    for total in range(1, max_total + 1):
        n = ns = nw = 0
        for prog, ars in two_fn_programs(total):
            n += 1
            if L.terminates_eager(prog):
                # possible weak separation: both halt, eager errs somewhere
                if lazy_has_value(prog) is True:
                    # operational check
                    lz_val, eg_val, kinds = machine_confirm_strong(prog)
                    if lz_val and not eg_val and 'err' in kinds:
                        nw += 1
                        if len(weak) < 50:
                            weak.append((total, prog))
                continue
            if L.terminates_lazy(prog) and lazy_has_value(prog) is True:
                ns += 1
                if len(strong) < 1000:
                    strong.append((total, prog))
        counts[('2fn', total)] = (n, ns, nw)
        if verbose:
            print(f"  2-function programs of size {total}: {n} scanned,"
                  f" {ns} strong, {nw} weak separations")
    return counts, strong, weak


if __name__ == '__main__':
    max_total = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    one_fn_max = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    print(f"Exhaustive separation search: 2-function total <= {max_total},"
          f" 1-function total <= {one_fn_max}")
    counts, strong, weak = search(max_total, one_fn_max)
    print("\ncounts:", counts)
    for label, lst in (("STRONG (eager diverges)", strong),
                       ("WEAK (eager errs on a dead argument)", weak)):
        if not lst:
            print(f"\nNo {label} found")
            continue
        best = min(t for t, p in lst)
        winners = [p for t, p in lst if t == best]
        print(f"\nSMALLEST {label}: total size {best}, {len(winners)} programs")
        shown = 0
        for p in winners:
            if shown >= 10:
                print(f"  ... and {len(winners) - shown} more of the same size")
                break
            print(p.show())
            print("   size", p.size())
            lz_val, eg_val, kinds = machine_confirm_strong(p)
            S = L.liveness(p)
            U, _ = L.unfold(p, S, cap=5000)
            print("   S* =", sorted(S), " E' =", L.show(U),
                  " lazy-value:", lz_val, " eager-value:", eg_val,
                  " eager kinds:", kinds)
            assert lz_val and not eg_val
            shown += 1
