"""ROUND 1b: re-verify (independently, with lcore.den) the coordinator's
new positive results:  last, init, rotate-right-by-1, swap-first-last
are ALL in L -- built from the ANCHOR trick:

    T   = enc^2_x(X) . bb          (anchor bb fresh: b-runs<=1 in images)
    P_s = x . s . bb               (constant; occurs iff last(X) = s,
                                     only at the junction)
    occurrence of a constant is testable:  contains(T, P_s) via eq
    last(X)  = if X=eps then eps else if P_a occurs then a else b
    init(X)  = if X=eps then eps else dec^2([eps/P_s] T) for the matching s
    rotr1    = cat(last, init);  swapfl = cat(last, tail(init), head)

These are POSITIVE CONTROLS for every candidate rev-excluding invariant.
"""
import sys
import lcore as L
from lcore import K, V, C, comp, den, den_try, rev, battery

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN                              # b_='a', x_='b', TOP='b', BOT='a'
A = sg.b + sg.b                          # 'aa' anchor
PA = sg.x + 'a' + A                      # 'baaa'
PB = sg.x + 'b' + A                      # 'bbaa'


def T():
    return C(tk.enc2(sg, V(0)), K(A))    # enc^2(X) . aa


def last_expr():
    return tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                  tk.if_(sg, tk.contains(sg, T(), PA), K('a'), K('b')))


def init_expr():
    return tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                  tk.if_(sg, tk.contains(sg, T(), PA),
                         tk.dec2(sg, comp([('', PA)], T())),
                         tk.dec2(sg, comp([('', PB)], T()))))


def rotr1_expr():
    return tk.cat(sg, last_expr(), init_expr())


def swapfl_expr():
    # w[n-1] . w[1:n-1] . w[0]
    return tk.cat(sg, last_expr(),
                  tk.cat(sg, tk.tail(sg, init_expr()), tk.head(sg, V(0))))


tests = battery(8)     # 511 strings
fails = {'last': 0, 'init': 0, 'rotr1': 0, 'swapfl': 0}
for X in tests:
    want = {'last': X[-1:], 'init': X[:-1],
            'rotr1': (X[-1:] + X[:-1]),
            'swapfl': X[-1:] + X[1:-1] + X[:1]}   # naive swap; n<=1 degenerate
    for name, e in [('last', last_expr()), ('init', init_expr()),
                    ('rotr1', rotr1_expr()), ('swapfl', swapfl_expr())]:
        r = den_try(e, (X,))
        if r[0] != 'ok' or r[1] != want[name]:
            fails[name] += 1
            if fails[name] <= 3:
                print(f'  {name} FAIL on {X!r}: got {r}, want {want[name]!r}')
print(f'last/init/rotr1/swapfl over 511 strings |w|<=8 ({{a,b}}): fails = {fails}')
total = sum(fails.values())
print('ALL PASS' if total == 0 else 'FAILURES PRESENT')

# sizes, for the record
for name, e in [('last', last_expr()), ('init', init_expr()),
                ('rotr1', rotr1_expr()), ('swapfl', swapfl_expr())]:
    print(f'  size({name}) = {L.size(e)}')
