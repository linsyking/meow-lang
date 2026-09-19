"""Selection ('if') for once-r: can any small expression compute
  sel-ends-b : X -> "a" if X ends with 'b' else "b"   (right-anchored test)
  sel-starts-a: X -> "a" if X starts with 'a' else "b" (left-anchored test)
plus a final independent verification of the toolkit constructions on a
large random test set.
"""
import itertools, random, sys
from search_oncer import gen_core, gen_all, UNI
from core import Var, Const, Subst, Cat, evalE, show, subst_once_r, subst_L

def t_selrb(x): return "a" if x[-1:] == "b" else "b"
def t_sella(x): return "a" if x[:1] == "a" else "b"
TARGETS = {"sel-ends-b": t_selrb, "sel-starts-a": t_sella}

found = {}
exprs = []
for n in (1, 4, 7):
    exprs += gen_core(n, 1)
for n in range(2, 8):
    exprs += gen_all(n, 1)
tested = 0
for E in exprs:
    vals = []
    ok = True
    for x in UNI:
        v = evalE(E, subst_once_r, [x])
        if v is None:
            ok = False; break
        vals.append(v)
    if not ok:
        continue
    tested += 1
    for name, f in TARGETS.items():
        if vals == [f(x) for x in UNI]:
            found.setdefault(name, []).append(show(E))
print(f"[once-r sel search] {len(exprs)} exprs, {tested} total")
for name in TARGETS:
    if name in found:
        print(f"   FOUND  {name}: {found[name][:3]}")
    else:
        print(f"   absent {name}")

# ---- toolkit constructions: independent large random verification ----
random.seed(42)
SIG = "ab"
def rnd(n=6): return "".join(random.choice(SIG) for _ in range(random.randint(0, n)))

X0, X1 = Var(0), Var(1)
catE  = Subst(Const("y"), Const("a"), Subst(Const("x"), Const("b"), Const("ba")))
# careful: replacements must be the VARIABLES. Use Var nodes as replacements:
catE  = Subst(Var(1), Const("a"), Subst(Var(0), Const("b"), Const("ba")))
dupE  = Subst(Var(0), Const("a"), Subst(Var(0), Const("b"), Const("ba")))
appE  = Subst(Var(0), Const("a"), Const("ab"))
preE  = Subst(Var(0), Const("a"), Const("ba"))
delrbE= Subst(Const(""), Const("b"), Var(0))
dblE  = Subst(Const("bb"), Const("b"), Subst(Var(0), Const("b"), Var(0)))
wrE   = Subst(Const("q"), Var(0), Var(0))          # whole-replace [q/X]X
enc1  = Subst(Const("xb"), Const("b"), Var(0))     # escape rightmost b
dec1  = Subst(Const("b"), Const("xb"), Var(0))

fails = 0
for _ in range(4000):
    x, y = rnd(), rnd()
    if evalE(catE, subst_once_r, [x, y]) != x + y: fails += 1; print("cat FAIL", x, y)
    if evalE(dupE, subst_once_r, [x]) != x + x: fails += 1; print("dup FAIL", x)
    if evalE(appE, subst_once_r, [x]) != x + "b": fails += 1; print("app FAIL", x)
    if evalE(preE, subst_once_r, [x]) != "b" + x: fails += 1; print("pre FAIL", x)
    if evalE(delrbE, subst_once_r, [x]) != t_selrb.__globals__['t_selrb'](x) and False: pass
    exp = x[:x.rfind("b")] + x[x.rfind("b")+1:] if "b" in x else x
    if evalE(delrbE, subst_once_r, [x]) != exp: fails += 1; print("delrb FAIL", x)
    if x and evalE(wrE, subst_once_r, [x]) != "q": fails += 1; print("wr FAIL", x)
    if evalE(enc1, subst_once_r, [x]) is None: fails += 1
    v = evalE(enc1, subst_once_r, [x])
    if v is not None and evalE(dec1, subst_once_r, [v]) != x:
        fails += 1; print("enc1/dec1 FAIL", x)
for m in range(0, 12):
    v = evalE(dblE, subst_once_r, ["b" * m])
    if v != "b" * (2 * m):
        fails += 1; print("dbl FAIL", m, v)
print("toolkit random verification:", "ALL PASS" if fails == 0 else f"{fails} FAILURES")

# baseline comparison: the paper's cat (enc/dec based) vs once-r's 2-pass cat
# (sizes): once-r cat uses 2 Subst nodes + 2 Const = size 7 core.
print("once-r cat expression:", show(catE), " core:", not isinstance(catE, Cat))
