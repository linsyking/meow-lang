"""Exp 10d: per-pass analysis of rep_n under restart.

Q1: for the renaming pass [m_i / E]^m on texts in normal form, when does it
    agree with the baseline pass [m_i / E]?  (Exact Agreement route: baseline
    output must be E-free.)
Q2: is (H') exactly 'enc(X_i) in {x, xb}' (i.e. X_i in {x, b}) -- the precise
    divergence condition for the renaming pass -- or do junction-created
    occurrences also diverge?
"""
import sys
sys.path.insert(0, "/home/cc/projects/meow-lang/docs/proof/research/scratch/restart")
from substlib import *

B, X = 'a', 'b'   # escaped char = 'a', escape char = 'b'


def enc(s):
    return subst(X + B, B, s)


def dec(s):
    return subst(B, X + B, s)


def is_image(s):
    return dec(s) is not None and enc(dec(s)) == s if True else False


# --- Q2: renaming pass divergence condition, from scratch on random normal-form texts
import itertools


def normal_form_texts(fraglens, markers):
    """fraglens: lengths of enc-images; markers: list of marker indices"""
    parts = []
    for L in fraglens:
        parts.append(enc("cd" * L)[:L])  # arbitrary image of length L: use enc of some string
    # simpler: build text as concat of enc(S_j) and markers
    out = ""
    for i, m in enumerate(markers):
        if i < len(fraglens):
            out += enc("c" * fraglens[i]) if fraglens[i] else ""
        out += X + B * (m + 1)
    if len(fraglens) > len(markers):
        out += enc("c" * fraglens[-1])
    return out


print("=== Q2: which E make [m_i/E]^m diverge on some normal-form text? ===")
# E ranges over enc-images of short strings; texts: fragments over {c,d,a} + markers
frag_strings = ["", "c", "d", "a", "cc", "cd", "ca", "ac", "aa", "aaa", "cca", "caa"]
texts = []
for n in range(0, 3):
    for combo in itertools.product(frag_strings + ["m0", "m1", "m2"], repeat=n):
        t = ""
        for p in combo:
            t += (X + B * 2 if p == "m0" else X + B * 3 if p == "m1" else X + B * 4 if p == "m2" else enc(p))
        texts.append(t)
texts = list(dict.fromkeys(texts))
print("   texts:", len(texts))

Eset = [enc(w) for w in all_strings("abcd", 3)] + [enc(w) for w in all_strings("abcd", 4) if w.count("a") <= 2]
div_E = set()
for E in dict.fromkeys(Eset):
    if E == "":
        continue
    for i in range(0, 4):
        mi = X + B * (i + 1)
        if E in mi:
            div_E.add(E)
            continue
        for t in texts:
            if E not in t:
                continue
            try:
                restart(mi, E, t, cap=800)
            except Diverge:
                div_E.add(E)
                break
        if E in div_E:
            break
div_words = sorted(set(dec(e) for e in div_E))
print("   E causing divergence somewhere (as words):", div_words[:20])
print("   all of form x or xb^j?", all(w == X or (w[0] == X and set(w[1:]) == {B}) for w in div_words))
print("   among these, which are actual enc-images:", sorted(w for w in div_words if enc(w) in set(div_E)))

print()
print("=== Q1: per-pass restart vs baseline for rep_2 on (H)+(H') instances ===")


def repC_passes(S, pairs):
    """returns list of (passname, before, baseline_after, restart_after)"""
    T = enc(S)
    log = []
    for i, (Xi, Yi) in enumerate(pairs, start=1):
        mi = X + B * (i + 1)
        mnext = X + B * (i + 2)
        E = enc(Xi)
        tb = subst(mi, E, T)
        try:
            tr, _ = restart(mi, E, T, cap=20000)
        except Diverge:
            tr = "DIV"
        log.append(("rename%d" % i, T, tb, tr, E))
        T2 = tb
        tr2 = tr if tr != "DIV" else None
        tb2 = subst(E + B, mnext, T2)
        try:
            tr2b, _ = restart(E + B, mnext, T2 if tr2 is None else tr2, cap=20000)
        except Diverge:
            tr2b = "DIV"
        # follow the RESTART trajectory
        if tr == "DIV":
            return log, "DIV"
        tb3 = subst(E + B, mnext, tr)
        try:
            tr3, _ = restart(E + B, mnext, tr, cap=20000)
        except Diverge:
            tr3 = "DIV"
        log.append(("repair%d" % i, tr, tb3, tr3, E + B))
        T = tr if tr3 == "DIV" else tr3
        if tr3 == "DIV":
            return log, "DIV"
        T = tr3
    for i, (Xi, Yi) in reversed(list(enumerate(pairs, start=1))):
        mi = X + B * (i + 1)
        tb = subst(enc(Yi), mi, T)
        try:
            tr, _ = restart(enc(Yi), mi, T, cap=20000)
        except Diverge:
            tr = "DIV"
        log.append(("inst%d" % i, T, tb, tr, mi))
        if tr == "DIV":
            return log, "DIV"
        T = tr
    return log, dec(T)


def respects_H(pairs):
    return all(len(Xi) == 1 or not Xi.endswith(X) for (Xi, Yi) in pairs)


stats = {"rename": [0, 0], "repair": [0, 0], "inst": [0, 0]}  # [agree, differ]
nfail_notfree = 0
for S in list(all_strings("abcd", 3)):
    for X1 in all_patterns("abcd", 1, 2):
        for X2 in all_patterns("abcd", 1, 2):
            pairs = [(X1, "cd"), (X2, "dcd")]
            if not respects_H(pairs):
                continue
            # apply (H') minimal: Xi not in {x, b} = {'b','a'}
            if any(Xi in ("b", "a") for (Xi, Yi) in pairs):
                continue
            log, fin = repC_passes(S, pairs)
            for (name, before, tb, tr, pat) in log:
                kind = name.rstrip("0123456789")
                if tr == "DIV":
                    stats[kind][1] += 1
                elif tb == tr:
                    stats[kind][0] += 1
                    if pat and tb.count(pat if kind != "rename" else pat) > 0:
                        pass
                else:
                    stats[kind][1] += 1
                    if stats[kind][1] <= 3 and kind == "rename":
                        print("   rename differ:", repr(name), "E=", repr(pat))
                        print("      before:", repr(before), "base:", repr(tb), "restart:", repr(tr))
print("   per-pass agreement (agree, differ/diverge):", stats)

print()
print("=== check: on (H')-violating instances, which pass diverges? ===")
cnt = {"rename": 0, "repair": 0}
for S in list(all_strings("abcd", 3)):
    for X1 in all_patterns("abcd", 1, 2):
        for X2 in all_patterns("abcd", 1, 2):
            pairs = [(X1, "cd"), (X2, "dcd")]
            if not respects_H(pairs):
                continue
            bad = [(i, Xi) for i, (Xi, Yi) in enumerate(pairs, 1) if Xi in ("b", "a")]
            if not bad:
                continue
            log, fin = repC_passes(S, pairs)
            for (name, before, tb, tr, pat) in log:
                if tr == "DIV":
                    cnt[name.rstrip("0123456789")] += 1
                    break
print("   divergence by pass kind:", cnt)
