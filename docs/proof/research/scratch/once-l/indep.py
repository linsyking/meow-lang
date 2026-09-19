# Independent Substitution lemma: the B != eps hypothesis.
import itertools

S3 = ["".join(t) for n in range(7) for t in itertools.product("abc", repeat=n)]
A2 = ["".join(t) for n in range(3) for t in itertools.product("abc", repeat=n)]

def bad_cases(f):  # f(A,B,C,S) -> bool whether lemma violated
    bad = []
    for A in A2:
        for Cp in A2:
            if not Cp or set(A) & set(Cp): continue
            for B in A2:
                if not B or set(A) & set(B): continue   # require B != eps
                for S in S3:
                    if (A in S) != (A in f(B, Cp, S)):
                        bad.append((A, B, Cp, S))
    return bad

bad_all = bad_cases(lambda B,C,S: S.replace(C, B))       # baseline replace-all
bad_once = bad_cases(lambda B,C,S: S.replace(C, B, 1))    # once

# And with B = eps allowed (paper's literal statement):
def bad_cases_eps(f):
    bad = []
    for A in A2:
        for Cp in A2:
            if not Cp or set(A) & set(Cp): continue
            for B in [""]:
                for S in S3:
                    if (A in S) != (A in f(B, Cp, S)):
                        bad.append((A, B, Cp, S))
                        return bad
    return bad

print("INDEP with B!=eps  | baseline replace-all violations:", len(bad_all), bad_all[:2])
print("INDEP with B!=eps  | once            violations:", len(bad_once), bad_once[:2])
print("INDEP with B=eps   | baseline replace-all counterexample:", bad_cases_eps(lambda B,C,S: S.replace(C,B)))
print("INDEP with B=eps   | once            counterexample:", bad_cases_eps(lambda B,C,S: S.replace(C,B,1)))
