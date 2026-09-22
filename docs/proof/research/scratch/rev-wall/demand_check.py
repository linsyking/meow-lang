#!/usr/bin/env python3
# rev-wall round 4 (DEMAND LEMMA) battery: the demand-side composition on D(k;3).
# Invocation: /usr/bin/python3 -W ignore demand_check.py   (cwd: rev-wall/)
# All parts < 60 s total; the machine CONFIRMS hand derivations; it does not
# replace them.  Engine construction re-implemented from Lane C's round-15C
# T6 general engine (verify_t6_general.py, build(letters)) with attribution.
import sys, time, random
sys.path.insert(0, '.')
T0 = time.time()
def MARK(s): print('  [%.1fs] %s' % (time.time() - T0, s), flush=True)
import prov as PV
from lcore import K, V, C, S

X = V(0)
B = 3
def dk(k):     return 'b'.join('a' * (B ** m) for m in range(k + 1))
def ev(e, w):  return PV.content(PV.lden(e, (PV.lab_input(w),)))
def pp_short(e):
    t = e[0]
    if t == 'K': return repr(e[1])
    if t == 'V': return 'X'
    if t == 'C': return '(' + pp_short(e[1]) + '.' + pp_short(e[2]) + ')'
    return '[' + pp_short(e[1]) + '/' + pp_short(e[2]) + ']' + pp_short(e[3])

# ---------------------------------------------------------------- tagged eval
# Atom tags: input atoms are bare ints (the input position); constant atoms
# ('K', nid, p).  When S-node nid fires copy #f, every inserted atom's tag is
# prepended (nid, f, .).  A tag that is still a bare int = an input atom NEVER
# routed through any replacement (F-pure); a tag whose head is nid was
# inserted by node nid's f-th firing (remnant-channel atoms at nid are exactly
# those whose head is not nid).
class Bail(Exception): pass
LIMIT = 20000
FIRES = {}          # nid -> firing count (incl. epsilon-replacement deletions)

def tev(e, w, nid_box):
    t = e[0]
    if t == 'K':
        nid = nid_box[0]; nid_box[0] += 1
        return [(ch, ('K', nid, p)) for p, ch in enumerate(e[1])]
    if t == 'V':
        return [(ch, i) for i, ch in enumerate(w)]
    if t == 'C':
        return tev(e[1], w, nid_box) + tev(e[2], w, nid_box)
    if t == 'S':
        nid = nid_box[0]; nid_box[0] += 1
        R = tev(e[1], w, nid_box)
        P = tev(e[2], w, nid_box)
        F = tev(e[3], w, nid_box)
        if len(P) == 0: raise PV.Undefined
        if max(len(R), len(P), len(F)) > LIMIT: raise Bail
        Ps = ''.join(c for c, _ in P)
        Fs = ''.join(c for c, _ in F)
        out, i, n, f = [], 0, len(F), 0
        while i < n:
            j = Fs.find(Ps, i)
            if j < 0:
                out.extend(F[i:]); break
            out.extend(F[i:j]); f += 1
            out.extend((c, (nid, f, tg)) for c, tg in R)
            i = j + len(P)
        FIRES[nid] = f
        return out
    raise ValueError(t)

def tchars(v): return ''.join(c for c, _ in v)
def leafpos(tg):
    """walk routing history to the leaf; input position or None (constant)"""
    while isinstance(tg, tuple) and tg[0] != 'K':
        tg = tg[2]
    return tg if isinstance(tg, int) else None
def rdepth(tg):
    d = 0
    while isinstance(tg, tuple) and tg[0] != 'K':
        d += 1; tg = tg[2]
    return d

def snodes(e, acc=None):
    if acc is None: acc = []
    if e[0] == 'S':
        acc.append(e); snodes(e[1], acc); snodes(e[2], acc); snodes(e[3], acc)
    elif e[0] == 'C':
        snodes(e[1], acc); snodes(e[2], acc)
    return acc

# ---------------------------------------------------------------- part A: D1
print('== A: D1 per-node remnant-order preservation (FU position flow) ==')
MARK('start')
CONSTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'abb']
def rand_expr(rng, depth):
    if depth == 0:
        return X if rng.random() < 0.5 else K(rng.choice(CONSTS))
    r = rng.random()
    if r < 0.25:
        return C(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1))
    return S(rand_expr(rng, depth - 1), rand_expr(rng, depth - 1),
             rand_expr(rng, depth - 1))

rng = random.Random(20260922)
nexpr = nchk = nviol = nskip = 0
while nexpr < 300:
    e = rand_expr(rng, 3); nexpr += 1
    nodes = snodes(e)
    try:
        top = tev(e, dk(3), [0])
        if tchars(top) != ev(e, dk(3)): nskip += 1; continue
    except (PV.Undefined, Bail):
        nskip += 1; continue
    ok_this = True
    for nd in nodes:
        try:
            vF = tev(nd[3], dk(3), [100000])   # F-child value (own id base)
            vN = tev(nd, dk(3), [200000])     # node value; node's own id = 200000
            if tchars(vN) != ev(nd, dk(3)): continue
        except (PV.Undefined, Bail):
            continue
        mynid = 200000                          # first id allocated = this node
        # X-descended atom positions, in order, of F's value:
        pF = [p for p in (leafpos(tg) for _, tg in vF) if p is not None]
        # remnant-channel atoms of the node's value (head is not mynid):
        pR = [p for p in (leafpos(tg) for _, tg in vN
                          if not (isinstance(tg, tuple) and tg[0] == mynid))
              if p is not None]
        # D1: pR must be a subsequence of pF (remnant channel preserves order):
        it = iter(pF)
        if not all(any(x == y for y in it) for x in pR):
            ok_this = False; nviol += 1
            print('  D1 VIOLATION at expr %d: %s' % (nexpr, pp_short(nd)))
        nchk += 1
    if not ok_this:
        break
print('  A: %d exprs, %d node-checks, %d skipped (bail/mismatch), %d violations'
      % (nexpr, nchk, nskip, nviol))
print('  A: D1 remnant-channel order preservation:',
      'VERIFIED' if nviol == 0 else 'REFUTED')
MARK('A done')

# ------------------------------------------------- part B: the T6 engine, D(k;3)
print('== B: T6 engine on D(k;3): rev + provenance trichotomy census ==')
def build(letters):
    """Lane C's round-15C general engine, re-implemented (attribution above)."""
    k = len(letters); seps = sorted(set(letters))
    mrg = X
    for s in seps: mrg = S(K(''), K(s), mrg)
    def del_last(E, s):
        return S(K(''), C(K(s), C(mrg, K('a'))), C(C(E, mrg), K('a')))
    def del_first(E, s):
        return S(K(''), C(C(K('a'), mrg), K(s)), C(C(K('a'), mrg), E))
    Ds = []
    for m in range(k):
        E = X
        for t in range(m):      E = del_first(E, letters[t])
        for t in range(k - 1, m, -1): E = del_last(E, letters[t])
        Ds.append(S(K(letters[m]), E, C(C(mrg, K(letters[m])), mrg)))
    T = Ds[k - 1]
    for m in range(k - 2, -1, -1): T = C(C(T, K('a')), Ds[m])
    Efull = T
    for s in seps: Efull = S(K(s), C(K(s), C(mrg, K('a'))), Efull)
    return Efull, Ds, mrg

def runsof(w):
    out, r = [], 0
    for ch in w:
        if ch == 'b': out.append(None); r += 1
        else: out.append(r)
    return out

for k in (2, 3, 4, 5):
    E, Ds, mrg = build(['b'] * k)
    w = dk(k)
    ok = ev(E, w) == w[::-1]
    v = tev(E, w, [0])
    ok2 = tchars(v) == w[::-1]
    runmap = runsof(w)
    runs, cur = [], []
    for c, tg in v:
        if c == 'a': cur.append(tg)
        else:
            if cur: runs.append(cur); cur = []
    if cur: runs.append(cur)
    def ridx(tg):
        p = leafpos(tg)
        return runmap[p] if p is not None else 'K'
    T1 = T2 = T3 = 0
    T1labels = set()
    for r in runs:
        labs = set(ridx(tg) for tg in r)
        pure = all(isinstance(tg, int) for tg in r)
        if pure and len(labs) == 1:
            T1 += 1; T1labels |= labs
        elif len(labs) == 1:       T2 += 1
        else:                       T3 += 1
    bb_routed = sum(1 for c, tg in v if c == 'b' and isinstance(tg, tuple))
    bb_pure = sum(1 for c, tg in v if c == 'b' and isinstance(tg, int))
    print('  k=%d: rev %s (tagged-eval %s); runs=%d  T1(F-pure clean)=%d '
          'T2(copy-routed clean)=%d  T3(merged/multi)=%d; b: routed=%d input=%d'
          % (k, 'VERIFIED' if ok else 'REFUTED', 'ok' if ok2 else 'MISMATCH',
             len(runs), T1, T2, T3, bb_routed, bb_pure))
    print('       T1 labels: %s (D1\'\': all F-pure single-label runs share '
          'ONE label -> %s)' % (sorted(T1labels),
          'VERIFIED' if len(T1labels) <= 1 else 'REFUTED'))
MARK('B done')

# ------------------------------------------- part C: the engine's supply ledger
print('== C: engine ledger k=4,5: per-S-node firings, pattern deep amounts, '
      'anchored offsets ==')
for k in (4, 5):
    E, Ds, mrg = build(['b'] * k)
    w = dk(k)
    nodes = snodes(E)
    tot_fire = 0; multi = 0; l22viol = 0
    for nd in nodes:
        try:
            vN = tev(nd, w, [300000])
            if tchars(vN) != ev(nd, w): continue
        except (PV.Undefined, Bail):
            continue
        fires = FIRES.get(300000, 0)
        tot_fire += fires
        if fires >= 2: multi += 1
        try:
            Pv = tev(nd[2], w, [400000])
            plens = [len(z) for z in tchars(Pv).split('b') if z]
            deep = sorted(set(x for x in plens if x >= 9))
            if len(deep) > 4:
                l22viol += 1
                print('    L2.2 VIOLATION: %d distinct deep pattern amounts '
                      '%s at %s' % (len(deep), deep, pp_short(nd)))
        except (PV.Undefined, Bail):
            pass
    box_offsets = set()
    for D in Ds:
        try:
            Dv = tchars(tev(D, w, [500000]))
            box_offsets.add(len(Dv.split('b')[0]))
        except (PV.Undefined, Bail):
            pass
    # the del-chain walks: L_m's S-node count = the end-walk to junction m
    walks = [len(snodes(Ds[m][2])) for m in range(k)]
    print('  k=%d: %d S-nodes, total firings %d (multi-firing nodes %d), '
          'L2.2 violations %d; distinct D_m head sums (anchored offsets '
          'realized) = %d of %d junctions' % (k, len(nodes), tot_fire, multi,
          l22viol, len(box_offsets), k))
    print('       L_m del-chain lengths (end-walks to junction m): %s '
          '(total %d = Theta(k^2); the Omega(k) floor is the k distinct '
          'offsets)' % (walks, sum(walks)))
MARK('C done')

# --------------------------------------------------- part D: the plant picture
print('== D: plant census at k=4: output b positions vs top-anchored sums ==')
k = 4
E, Ds, mrg = build(['b'] * k)
w = dk(k)
v = tev(E, w, [0])
amass = 0; plants = []
for c, tg in v:
    if c == 'a': amass += 1
    else: plants.append(amass)
tops = [sum(B ** s for s in range(k - t, k + 1)) for t in range(k)]
print('  output b a-masses: %s' % plants)
print('  top-anchored sums: %s' % tops)
print('  match:', 'VERIFIED' if plants == tops else 'MISMATCH')
bd = [rdepth(tg) for c, tg in v if c == 'b']
print('  b routing depths: %s' % bd)
print('  (every output b is a ROUTED plant: carried by a D_m box splice; the '
      'input b positions are bottom-anchored, the output ones top-anchored)')
MARK('D done')
print('ROUND 4 BATTERY COMPLETE')
