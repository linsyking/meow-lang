// verify_hot.cpp -- compute-heavy kernels of the alphabet-invariance round,
// ported from the Python batteries per the standing constraint (C/C++ for
// CPU-bound work; Python only as glue). Caps and the undefined-
// classification rule (undefined <=> some pattern value is empty, strict)
// are IDENTICAL to the Python references (meow.py, verify_alignment.py,
// verify_transfer.py, verify_unary.py, verify_palindromes.py); every
// deterministic count below must match the corresponding Python log line.
//
// Sections:
//   HA1  dictionary family comma-free + Fib sizes        (align: A1)
//   HA2  alignment occ(c(B)) in c(C) = ell*occ(B)        (align: A2)
//   HA3  pass transfer L/once/R/kth at the pass level    (align: A3L/A3v)
//   HT1  Direction 1 at the expression level, L/once/R  (transfer: T1/T2)
//   HU1  exhaustive unary space size<=7 + target maps    (unary: U1b/U1b')
//   HU3  binary profiles vs unary space (+PRNG sample)   (unary: U3)
//   HP   middle-marker family + palindromic maxima      (palindromes: P1/P3)
#include <cstdio>
#include <cstdint>
#include <cmath>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <optional>
#include <algorithm>
#include <functional>

using std::string;
using std::vector;
using std::optional;

typedef optional<string> Opt;

static int nfail = 0;
static void report(const char* name, long cases, long bad) {
    printf("%-58s %12ld cases %8ld mismatches\n", name, cases, bad);
    if (bad) nfail++;
}

// ---------- primitives (port of meow.py; same semantics) ----------
static Opt subst(const string& A, const string& B, const string& C) {
    if (B.empty()) return std::nullopt;
    string res; size_t i = 0;
    while (true) {
        size_t j = C.find(B, i);
        if (j == string::npos) { res.append(C, i, string::npos); return res; }
        res.append(C, i, j - i);
        res.append(A);
        i = j + B.size();
    }
}
static Opt once_subst(const string& A, const string& B, const string& C) {
    if (B.empty()) return std::nullopt;
    size_t j = C.find(B);
    if (j == string::npos) return C;
    return C.substr(0, j) + A + C.substr(j + B.size());
}
static long rfind_within(const string& C, const string& B, size_t end) {
    // python C.rfind(B, 0, end): last j with j+|B| <= end and C[j:j+|B|]==B
    size_t hi = std::min(end, C.size());
    if (hi < B.size()) return -1;
    for (long k = (long)(hi - B.size()); k >= 0; --k)
        if (C.compare((size_t)k, B.size(), B) == 0) return k;
    return -1;
}
static Opt rsubst(const string& A, const string& B, const string& C) {
    if (B.empty()) return std::nullopt;
    vector<string> pieces;
    size_t i = C.size();
    while (true) {
        long j = rfind_within(C, B, i);
        if (j < 0) { pieces.push_back(C.substr(0, i)); break; }
        pieces.push_back(C.substr(j + B.size(), i - (j + B.size())));
        pieces.push_back(A);
        i = (size_t)j;
    }
    string res;
    for (auto it = pieces.rbegin(); it != pieces.rend(); ++it) res += *it;
    return res;
}
static Opt kth_subst(const string& A, const string& B, const string& C, int k) {
    if (B.empty()) return std::nullopt;
    vector<size_t> pos;
    size_t i = 0;
    while (true) {
        size_t j = C.find(B, i);
        if (j == string::npos) break;
        pos.push_back(j);
        i = j + B.size();
    }
    if ((int)pos.size() < k) return C;
    size_t j = pos[k - 1];
    return C.substr(0, j) + A + C.substr(j + B.size());
}
struct Mode { int kind; int k; };   // 0=L 1=once 2=R 3=kth
static Opt apply_pass(const Mode& m, const string& A, const string& B, const string& C) {
    if (B.empty()) return std::nullopt;
    switch (m.kind) {
        case 0: return subst(A, B, C);
        case 1: return once_subst(A, B, C);
        case 2: return rsubst(A, B, C);
        default: return kth_subst(A, B, C, m.k);
    }
}
static vector<size_t> occ_positions(const string& C, const string& B) {
    vector<size_t> res;
    if (B.empty()) { for (size_t i = 0; i <= C.size(); ++i) res.push_back(i); return res; }
    size_t i = 0;
    while (true) {
        size_t j = C.find(B, i);
        if (j == string::npos) return res;
        res.push_back(j);
        i = j + 1;
    }
}

// ---------- expression arena ----------
struct Node { int tag; int a, b, c; };   // 0 var(a) 1 const(a) 2 pass(a,b,c) 3 cat(a,b)
static vector<Node> ND;
static vector<string> CS;
static int mkVar(int i)              { ND.push_back({0, i, 0, 0}); return (int)ND.size() - 1; }
static int mkConst(const string& w)  { CS.push_back(w); ND.push_back({1, (int)CS.size() - 1, 0, 0}); return (int)ND.size() - 1; }
static int mkPass(int R, int P, int E){ ND.push_back({2, R, P, E}); return (int)ND.size() - 1; }
static int mkCat(int E1, int E2)     { ND.push_back({3, E1, E2, 0}); return (int)ND.size() - 1; }

static Opt ev(int E, const vector<string>& args, const Mode& m) {
    const Node& n = ND[E];
    if (n.tag == 0) return args[n.a];
    if (n.tag == 1) return CS[n.a];
    if (n.tag == 3) {
        Opt v1 = ev(n.a, args, m), v2 = ev(n.b, args, m);
        if (!v1 || !v2) return std::nullopt;
        return *v1 + *v2;
    }
    Opt vR = ev(n.a, args, m), vP = ev(n.b, args, m), vE = ev(n.c, args, m);
    if (!vR || !vP || !vE) return std::nullopt;
    return apply_pass(m, *vR, *vP, *vE);
}
static int sizeE(int E) {
    const Node& n = ND[E];
    if (n.tag <= 1) return 1;
    if (n.tag == 3) return 1 + sizeE(n.a) + sizeE(n.b);
    return 1 + sizeE(n.a) + sizeE(n.b) + sizeE(n.c);
}
static int transferE(int E, const std::map<char, string>& cmap) {
    const Node& n = ND[E];
    if (n.tag == 0) return E;
    if (n.tag == 1) {
        string w;
        for (char ch : CS[n.a]) w += cmap.at(ch);
        return mkConst(w);
    }
    if (n.tag == 3) return mkCat(transferE(n.a, cmap), transferE(n.b, cmap));
    return mkPass(transferE(n.a, cmap), transferE(n.b, cmap), transferE(n.c, cmap));
}
static string enc(const std::map<char, string>& cmap, const string& S) {
    string r;
    for (char ch : S) r += cmap.at(ch);
    return r;
}

// ---------- generators ----------
static vector<string> all_strings_upto(const string& alpha, int maxlen) {
    // all strings of length 0..maxlen, sorted (python all_strings)
    vector<string> res;
    res.push_back("");
    vector<string> cur;
    cur.push_back("");
    for (int d = 0; d < maxlen; ++d) {
        vector<string> next;
        for (auto& s : cur) for (char c : alpha) next.push_back(s + c);
        cur = next;
        res.insert(res.end(), cur.begin(), cur.end());
    }
    std::sort(res.begin(), res.end());
    return res;
}
static vector<string> exact_len(const string& alpha, int k) {
    // all strings of exact length k, sorted
    vector<string> res;
    if (k == 0) { res.push_back(""); return res; }
    vector<string> cur;
    cur.push_back("");
    for (int d = 0; d < k; ++d) {
        vector<string> next;
        for (auto& s : cur) for (char c : alpha) next.push_back(s + c);
        cur = next;
    }
    res = cur;
    std::sort(res.begin(), res.end());
    return res;
}
// the double-a family: { a a m b : m in gamma^{ell-3}, 'aa' not in m, m[0]!=a }
static vector<string> dict_family(const string& gamma, char a, char b, int ell) {
    vector<string> res;
    for (auto& m : exact_len(gamma, ell - 3)) {
        if (m.find(string(1, a) + a) != string::npos) continue;
        if (ell > 3 && !m.empty() && m[0] == a) continue;
        res.push_back(string(1, a) + a + m + b);
    }
    return res;
}
static bool comma_free(const vector<string>& D) {
    std::set<string> Ds(D.begin(), D.end());
    int ell = (int)D[0].size();
    for (auto& u : D) for (auto& v : D) {
        string uv = u + v;
        for (int p = 1; p < ell; ++p)
            if (Ds.count(uv.substr(p, ell))) return false;
    }
    return true;
}
static std::map<char, string> make_coding(const string& src, const string& tgt) {
    char a = tgt[0], b = tgt[1];
    int ell = 3;
    while ((int)dict_family(tgt, a, b, ell).size() < (int)src.size()) ell++;
    vector<string> D = dict_family(tgt, a, b, ell);
    std::map<char, string> cmap;
    string s = src;
    std::sort(s.begin(), s.end());
    for (size_t i = 0; i < s.size(); ++i) cmap[s[i]] = D[i];
    return cmap;
}

int main() {
    const string SIG = "abc", GAM = "xy";
    std::map<char, string> cmap = make_coding(SIG, GAM);
    string cs;
    for (auto& kv : cmap) cs += kv.first + string("->") + kv.second + " ";
    int ellc = (int)cmap.begin()->second.size();
    printf("coding c: abc->xy ell=%d (%s)\n", ellc, cs.c_str());

    // ---------- HA1: family comma-free + Fib sizes ----------
    {
        long n = 0, bad = 0;
        string gams[3] = {"xy", "xyz", "wxyz"};
        for (auto& g : gams)
            for (int ell = 3; ell <= 9; ++ell) {
                n++;
                if (!comma_free(dict_family(g, g[0], g[1], ell))) bad++;
            }
        long fib1 = 1, fib2 = 1;                   // Fib(ell-2), F(1)=F(2)=1
        for (int ell = 3; ell <= 12; ++ell) {
            if ((long)dict_family("xy", 'x', 'y', ell).size() != fib1) bad++;
            long t = fib1 + fib2; fib1 = fib2; fib2 = t;
        }
        report("HA1 family comma-free (21 dicts) + Fib sizes", n + 10, bad);
    }

    // ---------- HA2: alignment ----------
    {
        long n = 0, bad = 0;
        vector<string> Bs = all_strings_upto(SIG, 3), Cs = all_strings_upto(SIG, 5);
        for (auto& B : Bs) {
            if (B.empty()) continue;
            string cB = enc(cmap, B);
            for (auto& C : Cs) {
                string cC = enc(cmap, C);
                vector<size_t> got = occ_positions(cC, cB), want;
                for (size_t s : occ_positions(C, B)) want.push_back(ellc * s);
                n++;
                if (got != want) bad++;
            }
        }
        report("HA2 alignment occ(c(B)) in c(C) = ell*occ(B)", n, bad);
    }

    // ---------- HA3: pass transfer, all four semantics ----------
    {
        long n = 0, bad = 0;
        vector<string> A3 = all_strings_upto(SIG, 3), C4 = all_strings_upto(SIG, 4);
        for (auto& A : A3) for (auto& B : A3) {
            if (B.empty()) continue;
            for (auto& C : C4) {
                n++;
                Opt l = subst(enc(cmap, A), enc(cmap, B), enc(cmap, C));
                Opt r = subst(A, B, C);
                if (l != (r ? Opt(enc(cmap, *r)) : Opt(std::nullopt))) bad++;
            }
        }
        report("HA3L pass transfer [cA/cB]cC = c([A/B]C)", n, bad);
    }
    {
        long n = 0, bad = 0;
        Mode modes[5] = {{1,0},{2,0},{3,1},{3,2},{3,3}};
        vector<string> A2 = all_strings_upto(SIG, 2), C3 = all_strings_upto(SIG, 3);
        for (auto& A : A2) for (auto& B : A2) {
            if (B.empty()) continue;
            for (auto& C : C3) for (auto& m : modes) {
                n++;
                Opt l = apply_pass(m, enc(cmap, A), enc(cmap, B), enc(cmap, C));
                Opt rr = apply_pass(m, A, B, C);
                Opt r = rr ? Opt(enc(cmap, *rr)) : Opt(std::nullopt);
                if (l != r) bad++;
            }
        }
        report("HA3v once/R/kth pass transfer", n, bad);
    }

    // ---------- HT1: Direction 1 at the expression level ----------
    vector<int> leaves;
    leaves.push_back(mkVar(0));
    for (auto& w : all_strings_upto(SIG, 2)) leaves.push_back(mkConst(w));
    vector<int> SP1 = leaves;
    for (auto R : leaves) for (auto P : leaves) for (auto E : leaves)
        SP1.push_back(mkPass(R, P, E));
    for (auto E1 : leaves) for (auto E2 : leaves) SP1.push_back(mkCat(E1, E2));
    printf("expression space: %zu depth<=1 expressions\n", SP1.size());

    {
        long n = 0, bad = 0, und = 0;
        Mode L = {0, 0};
        vector<string> IN = all_strings_upto(SIG, 4);
        for (int E : SP1) {
            int Ec = transferE(E, cmap);
            for (auto& S : IN) {
                n++;
                Opt v1 = ev(E, {S}, L);
                Opt v2 = ev(Ec, {enc(cmap, S)}, L);
                if ((!v1) != (!v2)) { bad++; continue; }
                if (!v1) { und++; continue; }
                if (*v2 != enc(cmap, *v1)) bad++;
            }
        }
        report("HT1 Dir-1 (all depth<=1 exprs, |S|<=4, L)", n, bad);
        printf("     undefined (matching both sides): %ld\n", und);
    }
    for (int kind = 1; kind <= 2; ++kind) {     // once, R
        long n = 0, bad = 0;
        Mode m = {kind, 0};
        vector<string> IN = all_strings_upto(SIG, 3);
        for (int E : SP1) {
            int Ec = transferE(E, cmap);
            for (auto& S : IN) {
                n++;
                Opt v1 = ev(E, {S}, m);
                Opt v2 = ev(Ec, {enc(cmap, S)}, m);
                if ((!v1) != (!v2)) { bad++; continue; }
                if (v1 && *v2 != enc(cmap, *v1)) bad++;
            }
        }
        report(kind == 1 ? "HT1 Dir-1 under once (|S|<=3)"
                         : "HT1 Dir-1 under R (|S|<=3)", n, bad);
    }

    // ---------- HU1: exhaustive unary space, size <= 7 ----------
    std::set<vector<int>> uprof;
    {
        vector<int> ul;
        ul.push_back(mkVar(0));
        for (int k = 0; k < 5; ++k) ul.push_back(mkConst(string(k, 'a')));
        std::map<int, vector<int>> bySize;       // exact size -> expressions
        bySize[1] = ul;
        for (int s = 2; s <= 7; ++s) {
            vector<int> res;
            for (int a = 1; a < s; ++a) {        // cat: 1+a+b = s
                int b = s - 1 - a;
                if (b < 1) break;
                for (int E1 : bySize[a]) for (int E2 : bySize[b])
                    res.push_back(mkCat(E1, E2));
            }
            for (int a = 1; a < s; ++a)          // pass: 1+a+b+c = s
                for (int b = 1; b < s - a; ++b) {
                    int c = s - 1 - a - b;
                    if (c < 1) break;
                    for (int R : bySize[a]) for (int P : bySize[b])
                        for (int E : bySize[c]) res.push_back(mkPass(R, P, E));
                }
            bySize[s] = res;
        }
        long total = 0;
        Mode L = {0, 0};
        for (auto& kv : bySize) for (int E : kv.second) {
            total++;
            vector<int> p;
            for (int nn = 0; nn <= 24; ++nn) {
                Opt v = ev(E, {string(nn, 'a')}, L);
                p.push_back(v ? (int)v->size() : -1);
            }
            uprof.insert(p);
        }
        printf("HU1 exhaustive unary space size<=7: %ld expressions, "
               "%zu distinct length maps on n=0..24\n", total, uprof.size());
        // PRNG supplement mirroring the Python reference's 3000 random
        // depth<=4 unary expressions (rand_unary(4)); independent sample.
        uint64_t st1 = 20260922ULL;
        auto rnd1 = [&]() {
            st1 += 0x9E3779B97F4A7C15ULL;
            uint64_t z = st1;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
            return z ^ (z >> 31);
        };
        auto r011 = [&]() { return (double)(rnd1() >> 11) / 9007199254740992.0; };
        std::function<int(int)> ru = [&](int d) -> int {
            if (d == 0) {
                if (r011() < 0.5) return mkVar(0);
                return mkConst(string((int)(rnd1() % 5), 'a'));
            }
            if (r011() < 0.7)
                return mkPass(ru(d - 1), ru(d - 1), ru(d - 1));
            return mkCat(ru(d - 1), ru(d - 1));
        };
        for (int i = 0; i < 3000; ++i) {
            int E = ru(4);
            vector<int> p;
            for (int nn = 0; nn <= 24; ++nn) {
                Opt v = ev(E, {string(nn, 'a')}, L);
                p.push_back(v ? (int)v->size() : -1);
            }
            uprof.insert(p);
        }
        printf("HU1 with 3000 random depth<=4 supplement: "
               "%zu distinct length maps (Python reference, own sample: 2091)\n",
               uprof.size());
        auto has = [&](const vector<int>& p) { return uprof.count(p) > 0; };
        vector<std::pair<const char*, vector<int>>> tg;
        auto mk = [&](long (*f)(long)) {
            vector<int> p;
            for (long x = 0; x <= 24; ++x) p.push_back((int)f(x));
            return p;
        };
        tg.push_back({"id n",        mk([](long n){ return n; })});
        tg.push_back({"2n",          mk([](long n){ return 2*n; })});
        tg.push_back({"n^2",         mk([](long n){ return n*n; })});
        tg.push_back({"n+1",         mk([](long n){ return n+1; })});
        tg.push_back({"n^4",         mk([](long n){ return n*n*n*n; })});
        tg.push_back({"floor(n/2)",  mk([](long n){ return n/2; })});
        tg.push_back({"ceil(n/2)",   mk([](long n){ return (n+1)/2; })});
        tg.push_back({"n mod 2",     mk([](long n){ return n%2; })});
        tg.push_back({"max(n-1,0)",  mk([](long n){ return n>0?n-1:0; })});
        tg.push_back({"2^n",         mk([](long n)->long{ return (long)(1LL<<n); })});
        for (auto& t : tg)
            printf("     target %-12s: %s\n", t.first, has(t.second) ? "FOUND" : "NOT FOUND");
        int sq = mkPass(mkVar(0), mkConst("a"), mkVar(0));
        int n4 = mkPass(sq, mkConst("a"), sq);
        bool ok = true;
        for (int nn = 0; nn <= 24; ++nn) {
            Opt v = ev(n4, {string(nn, 'a')}, {0, 0});
            if (!v || (int)v->size() != nn*nn*nn*nn) ok = false;
        }
        printf("     n^4 witness [[X/a]X / a]([X/a]X) at size %d: %s\n",
               sizeE(n4), ok ? "exact" : "FAIL");
        if (!ok) nfail++;
    }

    // ---------- HU3: binary profiles vs the unary space ----------
    {
        vector<int> bl;
        bl.push_back(mkVar(0));
        for (auto& w : all_strings_upto("ab", 2)) bl.push_back(mkConst(w));
        vector<int> B1 = bl;
        for (auto R : bl) for (auto P : bl) for (auto E : bl)
            B1.push_back(mkPass(R, P, E));
        for (auto E1 : bl) for (auto E2 : bl) B1.push_back(mkCat(E1, E2));
        // PRNG supplement: 2000 random depth<=3 binary expressions
        uint64_t st = 20260922ULL;
        auto rnd = [&]() {
            st += 0x9E3779B97F4A7C15ULL;
            uint64_t z = st;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
            return z ^ (z >> 31);
        };
        auto r01 = [&]() { return (double)(rnd() >> 11) / 9007199254740992.0; };
        std::function<int(int)> rb = [&](int d) -> int {
            if (d == 0) {
                if (r01() < 0.5) return mkVar(0);
                int len = (int)(rnd() % 4);
                string w;
                for (int i = 0; i < len; ++i) w += (char)('a' + (rnd() % 2));
                return mkConst(w);
            }
            if (r01() < 0.7)
                return mkPass(rb(d - 1), rb(d - 1), rb(d - 1));
            return mkCat(rb(d - 1), rb(d - 1));
        };
        vector<int> BR;
        for (int i = 0; i < 2000; ++i) BR.push_back(rb(3));
        // unary comparison set on n=0..12 with constant shifts (cap 400, k<=64)
        std::set<vector<int>> uset;
        for (auto& u : uprof) {
            vector<int> t(u.begin(), u.begin() + 13);
            uset.insert(t);
            bool alldef = true;
            for (int x : t) if (x < 0) alldef = false;
            if (!alldef) continue;
            for (int k = 0; k <= 64; ++k) {
                bool cap = true;
                for (int x : t) if (x + k > 400) { cap = false; break; }
                if (!cap) break;
                vector<int> s;
                for (int x : t) s.push_back(x + k);
                uset.insert(s);
            }
        }
        Mode L = {0, 0};
        long total = 0, missing = 0;
        std::set<vector<int>> miss;
        for (int E : B1) {
            vector<int> p;
            for (int nn = 0; nn <= 12; ++nn) {
                Opt v = ev(E, {string(nn, 'a')}, L);
                p.push_back(v ? (int)v->size() : -1);
            }
            bool tot = true;
            for (int x : p) if (x < 0) { tot = false; break; }
            if (!tot) continue;
            total++;
            if (!uset.count(p)) { missing++; miss.insert(p); }
        }
        printf("HU3a deterministic binary profiles (%zu depth<=1 exprs): "
               "%ld total, %ld missing from unary size<=7 (+shifts)\n",
               B1.size(), total, missing);
        for (auto& p : miss) {
            printf("     missing:");
            for (int x : p) printf(" %d", x);
            printf("\n");
        }
        long t2 = 0, m2 = 0;
        std::set<vector<int>> miss2;
        for (int E : BR) {
            vector<int> p;
            for (int nn = 0; nn <= 12; ++nn) {
                Opt v = ev(E, {string(nn, 'a')}, L);
                p.push_back(v ? (int)v->size() : -1);
            }
            bool tot = true;
            for (int x : p) if (x < 0) { tot = false; break; }
            if (!tot) continue;
            t2++;
            if (!uset.count(p)) { m2++; miss2.insert(p); }
        }
        printf("HU3b PRNG supplement (2000 random depth<=3): "
               "%ld total, %ld missing (independent sample)\n", t2, m2);
        for (auto& p : miss2) {
            printf("     missing:");
            for (int x : p) printf(" %d", x);
            printf("\n");
        }
    }

    // ---------- HP: palindromic families and maxima ----------
    {
        long n = 0, bad = 0;
        string gams[2] = {"abc", "abcd"};
        for (auto& g : gams) for (int mu = 0; mu < 2; ++mu) {
            char m = g[mu];
            string rest;
            for (char c : g) if (c != m) rest += c;
            for (int mm = 1; mm <= 5; ++mm) {
                vector<string> D;
                for (auto& a : exact_len(rest, mm))
                    D.push_back(a + m + string(a.rbegin(), a.rend()));
                n++;
                bool pal = true;
                for (auto& w : D) if (w != string(w.rbegin(), w.rend())) pal = false;
                long want = 1;
                for (int i = 0; i < mm; ++i) want *= (long)rest.size();
                if (!pal || !comma_free(D) || (long)D.size() != want) bad++;
            }
        }
        report("HP middle-marker family palindromic+comma-free+size", n, bad);
    }
    {
        auto palindromes = [](int ell) {
            vector<string> res;
            string alpha = "ab";
            int half = ell / 2;
            for (auto& h : exact_len(alpha, half)) {
                string rev(h.rbegin(), h.rend());
                if (ell % 2) for (char c : alpha) res.push_back(h + c + rev);
                else res.push_back(h + rev);
            }
            std::sort(res.begin(), res.end());
            return res;
        };
        for (int ell : {3, 4, 5, 6, 7, 9}) {
            vector<string> P = palindromes(ell);
            vector<string> best;
            std::function<void(int, vector<string>&)> srch =
                [&](int i, vector<string>& cur) {
                    if ((long)cur.size() + ((long)P.size() - i) <= (long)best.size()) return;
                    if (i == (int)P.size()) { best = cur; return; }
                    cur.push_back(P[i]);
                    if (comma_free(cur)) srch(i + 1, cur);
                    cur.pop_back();
                    srch(i + 1, cur);
                };
            vector<string> cur;
            srch(0, cur);
            printf("HP binary ell=%d: %zu palindromes, max comma-free "
                   "palindromic set: %zu\n", ell, P.size(), best.size());
            if (!comma_free(best)) { printf("     NOT COMMA-FREE (bug)\n"); nfail++; }
        }
    }

    printf(nfail ? "SOME FAILURES\n" : "ALL OK\n");
    return nfail ? 1 : 0;
}
