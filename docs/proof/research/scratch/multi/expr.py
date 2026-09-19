"""Expression-level verification of the comma-code construction.

A tiny evaluator for paper-style expressions:
  E ::= Xi | W | [R/P]E | E1 E2        (Definition "Substitution Expressions")
with the paper's denotation (right-to-left composition inside [R/P]E applied
to the scrutinee).  We build the uniform expression
  RepComma_n(S; X1,Y1; ...; Xn,Yn)
with variables and check it denotes the freezing semantics rep_ref on
random and adversarial inputs, including undefinedness behaviour when some
X_i = epsilon.
"""
import sys, random
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/multi")
from core import subst, rep_ref, all_strings

class Expr:
    def __init__(self, kind, *args):
        self.kind = kind      # 'var' | 'const' | 'subst' | 'cat'
        self.args = args
    def __call__(self, env):
        if self.kind == 'var':
            return env[self.args[0]]
        if self.kind == 'const':
            return self.args[0]
        if self.kind == 'cat':
            return self.args[0](env) + self.args[1](env)
        if self.kind == 'subst':
            R, P, E = self.args
            p = P(env)
            if p == "":
                raise ValueError("empty pattern: undefined")
            return subst(R(env), p, E(env))
    def __str__(self):
        if self.kind == 'var': return self.args[0]
        if self.kind == 'const': return repr(self.args[0])
        if self.kind == 'cat': return f"({self.args[0]} {self.args[1]})"
        R, P, E = self.args
        return f"[{R}/{P}]{E}"

def Var(n): return Expr('var', n)
def Kon(s): return Expr('const', s)
def Cat(a, b): return Expr('cat', a, b)
def Pass(R, P, E): return Expr('subst', R, P, E)

def pipeline(passes, E):
    """passes applied left-to-right: passes[0] runs FIRST."""
    for R, P in passes:
        E = Pass(R, P, E)
    return E

def enc2_expr(b, x, alphabet, X):
    """enc2 as passes on expression X: [xx/x] first, then [xc/c] for c != x."""
    passes = [(Kon(x + x), Kon(x))]
    for c in alphabet:
        if c != x:
            passes.append((Kon(x + c), Kon(c)))
    return pipeline(passes, X)

def dec2_expr(b, x, alphabet, X):
    passes = []
    for c in alphabet:
        if c != x:
            passes.append((Kon(c), Kon(x + c)))
    passes.append((Kon(x), Kon(x + x)))
    return pipeline(passes, X)

def RepComma_expr(b, x, alphabet, n, S, XYs):
    """The uniform expression for rep_n with the comma code.

    S: variable name; XYs: list of (Xvar, Yvar) names, length n.
    """
    E = enc2_expr(b, x, alphabet, Var(S))
    for i, (Xv, _) in enumerate(XYs, start=1):
        m_i = x + b * (i + 1)
        m_next = x + b * (i + 2)
        E = Pass(Kon(m_i), enc2_expr(b, x, alphabet, Var(Xv)), E)
        E = Pass(Cat(enc2_expr(b, x, alphabet, Var(Xv)), Kon(b)), Kon(m_next), E)
    for i in range(n, 0, -1):
        Yv = XYs[i - 1][1]
        m_i = x + b * (i + 1)
        E = Pass(enc2_expr(b, x, alphabet, Var(Yv)), Kon(m_i), E)
    E = dec2_expr(b, x, alphabet, E)
    return E

# ---------------------------------------------------------------------------
# Verify at the expression level, n = 1..3, against rep_ref.
# ---------------------------------------------------------------------------
random.seed(4242)
b, x, alphabet = "a", "b", "ab"
fails = 0
trials = 0
for n in [1, 2, 3]:
    E = RepComma_expr(b, x, alphabet, n, "S",
                      [(f"X{i}", f"Y{i}") for i in range(1, n + 1)])
    for _ in range(150):
        vals = {}
        env = {"S": "".join(random.choice(alphabet) for _ in range(random.randint(0, 16)))}
        pairs = []
        for i in range(1, n + 1):
            Xi = "".join(random.choice(alphabet) for _ in range(random.randint(1, 3)))
            Yi = "".join(random.choice("abcde") for _ in range(random.randint(0, 3)))
            env[f"X{i}"] = Xi; env[f"Y{i}"] = Yi
            pairs.append((Xi, Yi))
        trials += 1
        got = E(env)
        want = rep_ref(pairs, env["S"])
        if got != want:
            fails += 1
            print("EXPR FAIL:", pairs, env["S"], "want", want, "got", got)
            if fails > 5: break
    if fails > 5: break
print(f"expression-level check: {trials} trials, {fails} failures")

# Undefinedness agreement: if some Xi = epsilon the expression is undefined.
E2 = RepComma_expr("a", "b", "ab", 2, "S", [("X1", "Y1"), ("X2", "Y2")])
undef_ok = True
for Xi in ["", "a"]:
    try:
        E2({"S": "ab", "X1": Xi, "Y1": "c", "X2": "b", "Y2": "d"})
        if Xi == "":
            undef_ok = False
    except ValueError:
        if Xi != "":
            undef_ok = False
print("undefinedness agreement (X1 = eps => undefined):", "OK" if undef_ok else "FAIL")

# ---------------------------------------------------------------------------
# The flat, fully-constant pipeline for the paper's shadowing instance:
#   f(S) = rep_2(S; ab->bbba; bbb->aa)   over Sigma = {a,b}, (b,x)=(a,b).
# Print it as a list of passes.
# ---------------------------------------------------------------------------
pairs = [("ab", "bbba"), ("bbb", "aa")]
flat = []
def C(s): return s
# enc2 passes
flat.append((x + x, x))
for c in alphabet:
    if c != x:
        flat.append((x + c, c))
from core import enc2
for i, (X, _) in enumerate(pairs, start=1):
    flat.append((x + b * (i + 1), enc2(b, x, X, alphabet)))          # rename
    flat.append((enc2(b, x, X, alphabet) + b, x + b * (i + 2)))      # repair
for i in range(len(pairs), 0, -1):
    Y = pairs[i - 1][1]
    flat.append((enc2(b, x, Y, alphabet), x + b * (i + 1)))          # instantiate
for c in alphabet:
    if c != x:
        flat.append((c, x + c))                                      # dec2
flat.append((x, x + x))

def run_flat(S):
    T = S
    for R, P in flat:
        T = subst(R, P, T)
    return T

bad = [S for S in all_strings("ab", 9) if run_flat(S) != rep_ref(pairs, S)]
print(f"\nflat constant pipeline for the shadowing instance: "
      f"{len(flat)} passes, agreement on all 1023 strings over {{a,b}} len<=9: "
      f"{'OK' if not bad else bad[:5]}")
print("passes (replacement, pattern), applied left to right:")
for i, (R, P) in enumerate(flat):
    print(f"  {i+1:2d}. [{R}/{P}]")
