"""R2 library: L-expressible unary functions of the input w, for use as
patterns / replacements in pipeline synthesis.

Two families:
  PATTERNS  -- must be TOTAL-NONEMPTY (value != epsilon for every w,
               including w = epsilon), else the pass [R/P] is undefined
               somewhere and the pipeline cannot compute total rev
               (paper def:safe Anch predicate).
  REPLACEMENTS -- anything L-expressible.

Each item = (name, builder).  `vals(name)(w)` is the value; builders return
ASTs so any found pipeline is a genuine L expression.
"""
import sys

import lcore as L
from lcore import K, V, C, comp, pipe

sys.path.insert(0, L._LAZY_PASS)
import toolkit as tk   # noqa: E402

sg = tk.BIN                              # b_='a', x_='b', TOP='b', BOT='a'

# ---------------------------------------------------------------- anchored
# right-end surgery (coordinator's anchor trick; re-verified round 1b)
_A = sg.b + sg.b                         # 'aa'
_PA = sg.x + 'a' + _A                    # 'baaa'
_PB = sg.x + 'b' + _A                    # 'bbaa'


def _T():
    return C(tk.enc2(sg, V(0)), K(_A))    # enc^2(X) . aa


def last_expr():
    return tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                  tk.if_(sg, tk.contains(sg, _T(), _PA), K('a'), K('b')))


def init_expr():
    return tk.if_(sg, tk.eq(sg, V(0), K('')), K(''),
                  tk.if_(sg, tk.contains(sg, _T(), _PA),
                         tk.dec2(sg, comp([('', _PA)], _T())),
                         tk.dec2(sg, comp([('', _PB)], _T()))))


def rotr1_expr():
    return tk.cat(sg, last_expr(), init_expr())


def swapfl_expr():
    return tk.cat(sg, last_expr(),
                  tk.cat(sg, tk.tail(sg, init_expr()), tk.head(sg, V(0))))


def rot1_expr():
    return tk.cat(sg, tk.tail(sg, V(0)), tk.head(sg, V(0)))


def halve_expr():
    """paper prop:unary-once's H = [b/a][eps/b][a/bb] (rightmost runs first):
    on b^n gives b^floor(n/2); on general strings a blended halving."""
    return pipe([('a', 'bb'), ('', 'b'), ('b', 'a')], V(0))


def tail2_expr():
    return tk.tail(sg, tk.tail(sg, V(0)))


def tail3_expr():
    return tk.tail(sg, tk.tail(sg, tk.tail(sg, V(0))))


def catc(c):
    def b():
        return K(c)
    return b


def prepend(c):
    def b():
        return C(K(c), V(0))
    return b


def append(c):
    def b():
        return C(V(0), K(c))
    return b


def _g(f):
    """wrap a 0-arg builder"""
    return f


# PATTERNS: total-nonempty L-functions
PATTERNS = {
    'a': catc('a'), 'b': catc('b'),
    'aa': catc('aa'), 'ab': catc('ab'), 'ba': catc('ba'), 'bb': catc('bb'),
    'aaa': catc('aaa'), 'aab': catc('aab'), 'abb': catc('abb'),
    'baa': catc('baa'), 'bba': catc('bba'), 'bbb': catc('bbb'),
    'aba': catc('aba'), 'bab': catc('bab'),
    'aX': prepend('a'), 'bX': prepend('b'),
    'Xa': append('a'), 'Xb': append('b'),
    'aXi': lambda: C(K('a'), init_expr()),
    'iXa': lambda: C(init_expr(), K('a')),
    'aenc': lambda: C(K('a'), tk.enc(sg, V(0))),
    'enca': lambda: C(tk.enc(sg, V(0)), K('a')),
    'enc2aa': lambda: C(tk.enc2(sg, V(0)), K('aa')),
    'arot1': lambda: C(K('a'), rot1_expr()),
    'rot1a': lambda: C(rot1_expr(), K('a')),
    'arotr': lambda: C(K('a'), rotr1_expr()),
    'bbX': prepend('bb'), 'Xbb': append('bb'),
}

# REPLACEMENTS: any L-function (empty values allowed)
REPLACEMENTS = {
    'eps': catc(''), 'a': catc('a'), 'b': catc('b'),
    'aa': catc('aa'), 'ab': catc('ab'), 'ba': catc('ba'), 'bb': catc('bb'),
    'X': lambda: V(0),
    'tailX': lambda: tk.tail(sg, V(0)),
    'tail2X': tail2_expr, 'tail3X': tail3_expr,
    'headX': lambda: tk.head(sg, V(0)),
    'lastX': last_expr, 'initX': init_expr,
    'rot1X': rot1_expr, 'rotr1X': rotr1_expr, 'swapflX': swapfl_expr,
    'XX': lambda: C(V(0), V(0)),
    'aX': prepend('a'), 'bX': prepend('b'),
    'Xa': append('a'), 'Xb': append('b'),
    'encX': lambda: tk.enc(sg, V(0)),
    'enc2X': lambda: tk.enc2(sg, V(0)),
    'decX': lambda: tk.dec(sg, V(0)),
    'halveX': halve_expr,
    'abX': lambda: C(K('ab'), V(0)),
    'Xab': lambda: C(V(0), K('ab')),
    'XaX': lambda: C(C(V(0), K('a')), V(0)),
}
