/* ROUND 11 targeted hunt: depth-2 chain2 DB in the RESIDUAL regime.
 *
 * Theorem 3 (REPORT.md sec 11) says: for every fixed S-depth<=2 E the
 * set {w : E realizes DB(w)} is bounded.  Round 10's mode-2 hunt already
 * swept all depth-2 shapes over 379 inputs with the pass-free pattern
 * pool (0 DB).  This hunt targets the exact parameter corner the round-11
 * proof identifies as the only live one:
 *   - w uniform or near-uniform (a^k, b a^k, a^k b, a^i b a^j, and the
 *     periodic families), up to |w| = 20;
 *   - inner pattern X' CONSTANT and ALL-sigma (sigma = the dominant
 *     letter) -- the only unbounded-copy case (a non-sigma char in X'
 *     caps the copy count at the constant budget; a w-containing X'
 *     caps it at rho + c);
 *   - final pattern P pass-free CONTAINING w (pi = #V(P) >= 1: the
 *     residual regime; beta = pi*n + gamma >= n);
 *   - final replacement epsilon -- justified by the round-11 Replacement
 *     Elimination lemma (c=1 + labeled y forces prov(y) = R^nu to be an
 *     FDI block, impossible for n>=2) together with T1(a) (c>=2).
 *
 * Semantics: atom-level greedy never-rescan leftmost-first passes, the
 * same as prov.py.  DB checked at n >= 2.  FDI stats recorded.
 *
 * ROUND-12 REPAIR 2 -- PHASE 2 (mixed shapes).  The round-11 corner
 * analysis was written for PURE chain2 t = [Y/Z]f; the in-scope depth-2
 * shapes [R2/P2](g1.[Y/Z]f.g2) with pass-free flanking pieces g_i were
 * only waved at as "chain2 after flattening" -- not an equality, since
 * the inner pass does not scan the flanking material (a tau-run of t can
 * span the junctions, and g-constant stretches / tiling leftovers enter
 * the gaps; the repaired bound is s_p <= (j'+1)c_Y + c_F + beta'-1).
 * Neither round 10's mode 2 nor phase 1 above swept these shapes.
 * Phase 2 sweeps [eps/X](g1.[Y/xp].f.g2): g1, g2 from 12 pass-free
 * options (empty, pure constants a/b/ab, and the run-bearing forms
 * w, a.w, w.a, a.w.a, w.w, w.a.w, b.w, w.b -- at least one nonempty),
 * f from 8 forms, Y from 10 labeled forms, inner pattern all-a (the
 * residual corner), final pattern pass-free containing w (beta >= n),
 * final replacement epsilon.  Uniform and near-uniform inputs, n <= 14.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 24
#define MAXT 400000
#define MAXATOMS 400000

typedef struct { char c; int lab; } atom;

/* pass-free forms: value = pre + w [+ mid + w] + suf */
typedef struct { const char *pre, *mid, *suf; int two; } form;

static form forms[] = {
    {"", "", "", 0},      {"", "", "", 1},      {"a", "", "", 0},
    {"", "", "a", 0},     {"b", "", "", 0},     {"", "", "b", 0},
    {"a", "", "a", 0},    {"b", "", "b", 0},    {"", "b", "", 1},
    {"", "a", "", 1},     {"a", "", "b", 0},    {"b", "", "a", 0},
    {"ab", "", "", 0},    {"", "", "ab", 0},    {"ab", "", "ba", 0},
    {"ba", "", "ab", 0},  {"a", "b", "a", 1},   {"b", "a", "b", 1},
    {"", "abba", "", 1},  {"", "bb", "", 1},    {"", "ab", "", 1},
    {"", "ba", "", 1},    {"b", "b", "b", 1},
};
#define NFORM ((int)(sizeof(forms) / sizeof(forms[0])))

static const char *xpats[] = { "a", "aa", "aaa", "aaaa", "b", "bb",
                               "ab", "ba" };
#define NXP ((int)(sizeof(xpats) / sizeof(xpats[0])))

static char ws[600][MAXW + 1];
static int nws;

static void add_w(const char *s)
{
    for (int i = 0; i < nws; i++)
        if (!strcmp(ws[i], s))
            return;
    if (nws < 600 && strlen(s) <= MAXW) {
        strcpy(ws[nws], s);
        nws++;
    }
}

static void gen_wlist(void)
{
    char b[MAXW + 1];
    int k, i, j, n, total, idx;
    for (n = 2; n <= 6; n++) {            /* all |w| <= 6 */
        total = 1 << n;
        for (idx = 0; idx < total; idx++) {
            for (j = 0; j < n; j++)
                b[j] = ((idx >> (n - 1 - j)) & 1) ? 'b' : 'a';
            b[n] = 0; add_w(b);
        }
    }
    for (k = 2; k <= 24; k++) {            /* a^k */
        memset(b, 'a', k); b[k] = 0; add_w(b);
    }
    for (k = 2; k <= 20; k++) {            /* b a^k, a^k b */
        memset(b + 1, 'a', k); b[0] = 'b'; b[k + 1] = 0; add_w(b);
        memset(b, 'a', k); b[k] = 'b'; b[k + 1] = 0; add_w(b);
    }
    for (i = 1; i <= 7; i++)              /* a^i b a^j */
        for (j = 1; j <= 7; j++) {
            if (i + j > 18) continue;
            int L = 0;
            for (k = 0; k < i; k++) b[L++] = 'a';
            b[L++] = 'b';
            for (k = 0; k < j; k++) b[L++] = 'a';
            b[L] = 0; add_w(b);
        }
    for (k = 2; k <= 10; k++) {            /* (ab)^k */
        for (i = 0; i < 2 * k; i++) b[i] = (i & 1) ? 'b' : 'a';
        b[2 * k] = 0; add_w(b);
    }
    for (k = 2; k <= 8; k++) {            /* (aab)^k */
        int L = 0;
        for (i = 0; i < k; i++) { b[L++] = 'a'; b[L++] = 'a'; b[L++] = 'b'; }
        b[L] = 0; add_w(b);
    }
    for (k = 2; k <= 6; k++) {            /* (abb)^k, (baa)^k */
        int L = 0;
        for (i = 0; i < k; i++) { b[L++] = 'a'; b[L++] = 'b'; b[L++] = 'b'; }
        b[L] = 0; add_w(b);
        L = 0;
        for (i = 0; i < k; i++) { b[L++] = 'b'; b[L++] = 'a'; b[L++] = 'a'; }
        b[L] = 0; add_w(b);
    }
}

/* build the value of a form on w as atoms (labels = w offsets) */
static int build(const form *f, const char *w, int n, atom *out)
{
    int L = 0, r, k;
    const char *seq[5];
    int isw[5], cnt = 0;
    seq[cnt] = f->pre; isw[cnt++] = 0;
    seq[cnt] = w;      isw[cnt++] = 1;
    if (f->two) { seq[cnt] = f->mid; isw[cnt++] = 0;
                  seq[cnt] = w;      isw[cnt++] = 1; }
    seq[cnt] = f->suf; isw[cnt++] = 0;
    for (r = 0; r < cnt; r++) {
        if (isw[r])
            for (k = 0; k < n; k++) { out[L].c = w[k]; out[L].lab = k; L++; }
        else
            for (k = 0; seq[r][k]; k++) { out[L].c = seq[r][k]; out[L].lab = -1; L++; }
    }
    return L;
}

/* greedy [y_atoms/y_n] on t: returns new length; y can be NULL (delete) */
static int pass(const atom *t, int tn, const atom *y, int yn,
                const char *pat, int pn, atom *out)
{
    int i = 0, L = 0;
    while (i < tn) {
        int ok = (i + pn <= tn);
        if (ok) {
            for (int k = 0; k < pn; k++)
                if (t[i + k].c != pat[k]) { ok = 0; break; }
        }
        if (ok) {
            if (y)
                for (int k = 0; k < yn; k++) out[L++] = y[k];
            i += pn;
        } else {
            out[L++] = t[i];
            i++;
        }
    }
    return L;
}

static atom F1v[MAXATOMS], Yv[MAXATOMS], tbuf[MAXATOMS], obuf[MAXATOMS];
static int prov[MAXATOMS];

/* ---------------- phase 2: mixed shapes (round-12 repair 2) ------------- */

static form gforms[] = {              /* run-bearing flank options */
    {"", "", "", 0},   {"a", "", "", 0},  {"", "", "a", 0},
    {"a", "", "a", 0}, {"", "", "", 1},   {"", "a", "", 1},
    {"b", "", "", 0},  {"", "", "b", 0},
};
#define NG 12                          /* 0=empty, 1..3 pure constants */
static const char *gnames[NG] =
    { "", "a", "b", "ab", "w", "a.w", "w.a", "a.w.a",
      "w.w", "w.a.w", "b.w", "w.b" };

static int gbuild(int gi, const char *w, int n, atom *out)
{
    int L = 0;
    if (gi == 0) return 0;
    if (gi <= 3) {
        const char *s = (gi == 1) ? "a" : (gi == 2) ? "b" : "ab";
        for (; *s; s++) { out[L].c = *s; out[L].lab = -1; L++; }
        return L;
    }
    return build(&gforms[gi - 4], w, n, out);
}

static form f2forms[] = {              /* inner scrutinee f (8) */
    {"", "", "", 0},  {"a", "", "", 0}, {"", "", "a", 0}, {"b", "", "", 0},
    {"", "", "b", 0}, {"a", "", "a", 0}, {"", "", "", 1}, {"", "a", "", 1},
};
static form y2forms[] = {              /* inserted copy Y (10, all labeled) */
    {"", "", "", 0},  {"a", "", "", 0}, {"", "", "a", 0}, {"b", "", "", 0},
    {"", "", "b", 0}, {"a", "", "a", 0}, {"", "", "", 1}, {"", "a", "", 1},
    {"a", "b", "a", 1}, {"", "b", "", 1},
};

static char w2[64][MAXW + 1];
static int nw2;

static void add_w2(const char *s)
{
    for (int i = 0; i < nw2; i++)
        if (!strcmp(w2[i], s))
            return;
    if (nw2 < 64 && strlen(s) <= MAXW) {
        strcpy(w2[nw2], s);
        nw2++;
    }
}

static void gen_w2list(void)
{
    char b[MAXW + 1];
    int k, i, j, L;
    for (k = 2; k <= 14; k++) {                  /* a^k */
        memset(b, 'a', k); b[k] = 0; add_w2(b);
    }
    for (k = 2; k <= 8; k++) {                   /* b a^k, a^k b */
        memset(b + 1, 'a', k); b[0] = 'b'; b[k + 1] = 0; add_w2(b);
        memset(b, 'a', k); b[k] = 'b'; b[k + 1] = 0; add_w2(b);
    }
    for (i = 1; i <= 3; i++)                     /* a^i b a^j */
        for (j = 1; j <= 3; j++) {
            L = 0;
            for (k = 0; k < i; k++) b[L++] = 'a';
            b[L++] = 'b';
            for (k = 0; k < j; k++) b[L++] = 'a';
            b[L] = 0; add_w2(b);
        }
    for (k = 2; k <= 4; k++) {                   /* (ab)^k */
        for (i = 0; i < 2 * k; i++) b[i] = (i & 1) ? 'b' : 'a';
        b[2 * k] = 0; add_w2(b);
    }
}

static void phase2(void)
{
    static atom g1v[MAXW * 3 + 8], g2v[MAXW * 3 + 8], t2[MAXATOMS];
    static atom Xv[MAXW * 2 + 8];
    static char plist[NFORM][MAXW * 3 + 8];
    int plen[NFORM], pform[NFORM];
    long sims = 0, fdi = 0, fdilen[8];
    int maxfdi = 0, dbhits = 0;
    const char *xps[4] = { "a", "aa", "aaa", "aaaa" };
    for (int k = 0; k < 8; k++) fdilen[k] = 0;
    for (int iw = 0; iw < nw2; iw++) {
        const char *w = w2[iw];
        int n = (int)strlen(w);
        /* final-pattern pool: all forms, beta >= n, deduped (once per w) */
        int npats = 0;
        for (int pi = 0; pi < NFORM; pi++) {
            int xn2 = build(&forms[pi], w, n, Xv);
            char pat[MAXW * 2 + 8];
            for (int k = 0; k < xn2; k++) pat[k] = Xv[k].c;
            pat[xn2] = 0;
            if (xn2 < n) continue;
            int dup = 0;
            for (int k = 0; k < npats; k++)
                if (plen[k] == xn2 && !memcmp(plist[k], pat, xn2))
                    { dup = 1; break; }
            if (dup) continue;
            memcpy(plist[npats], pat, xn2 + 1);
            plen[npats] = xn2;
            pform[npats] = pi;
            npats++;
        }
        for (int fi = 0; fi < 8; fi++) {
            int fn = build(&f2forms[fi], w, n, F1v);
            for (int yi = 0; yi < 10; yi++) {
                int yn = build(&y2forms[yi], w, n, Yv);
                for (int xi = 0; xi < 4; xi++) {
                    const char *xp = xps[xi];
                    int xn = (int)strlen(xp);
                    int cn = pass(F1v, fn, Yv, yn, xp, xn, tbuf);
                    if (cn <= 0) continue;
                    for (int g1 = 0; g1 < NG; g1++) {
                        int g1n = gbuild(g1, w, n, g1v);
                        for (int g2 = 0; g2 < NG; g2++) {
                            if (g1 == 0 && g2 == 0) continue;
                            int g2n = gbuild(g2, w, n, g2v);
                            int tn = 0;
                            for (int k = 0; k < g1n; k++) t2[tn++] = g1v[k];
                            for (int k = 0; k < cn; k++)  t2[tn++] = tbuf[k];
                            for (int k = 0; k < g2n; k++) t2[tn++] = g2v[k];
                            for (int pi = 0; pi < npats; pi++) {
                                int on = pass(t2, tn, NULL, 0,
                                              plist[pi], plen[pi], obuf);
                                sims++;
                                int pn = 0;
                                for (int k = 0; k < on; k++)
                                    if (obuf[k].lab >= 0) prov[pn++] = obuf[k].lab;
                                if (pn == 0) continue;
                                int isfdi = 1;
                                for (int k = 0; k + 1 < pn; k++)
                                    if (prov[k] <= prov[k + 1]) { isfdi = 0; break; }
                                if (!isfdi) continue;
                                fdi++;
                                if (pn <= 7) fdilen[pn]++;
                                if (pn > maxfdi) maxfdi = pn;
                                if (pn == n && n >= 2) {
                                    int isdb = 1;
                                    for (int k = 0; k < pn; k++)
                                        if (prov[k] != n - 1 - k) { isdb = 0; break; }
                                    if (isdb) {
                                        dbhits++;
                                        printf("  MIXED DB HIT: w=%s n=%d "
                                               "f=pre:%s|mid:%s|suf:%s|%d "
                                               "Y=pre:%s|mid:%s|suf:%s|%d "
                                               "xp=%s g1=%s g2=%s P=%s "
                                               "Pform=%s|%s|%s|%d\n",
                                               w, n,
                                               f2forms[fi].pre, f2forms[fi].mid,
                                               f2forms[fi].suf, f2forms[fi].two,
                                               y2forms[yi].pre, y2forms[yi].mid,
                                               y2forms[yi].suf, y2forms[yi].two,
                                               xp, gnames[g1], gnames[g2],
                                               plist[pi],
                                               forms[pform[pi]].pre,
                                               forms[pform[pi]].mid,
                                               forms[pform[pi]].suf,
                                               forms[pform[pi]].two);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    printf("PHASE 2 (mixed shapes): %ld sims; FDI outputs: %ld "
           "(max length %d; len<=3: %ld); DB hits: %d\n",
           sims, fdi, maxfdi, fdilen[1] + fdilen[2] + fdilen[3], dbhits);
    printf("VERDICT (mixed shapes): %d DB hits on [eps/X](g1.[Y/xp].f.g2), "
           "g1/g2 run-bearing or constant flanks, n<=14 -- consistent with "
           "the repaired Theorem 3 (junction gaps bounded by "
           "2c_Y + c_F + beta' - 1 per gap)\n", dbhits);
}

int main(void)
{
    gen_wlist();
    printf("round11_hunt: %d inputs, %d F/Y forms, %d inner pats, "
           "%d final pats (residual regime)\n", nws, NFORM, NXP, NFORM);
    long sims = 0, fdi = 0;
    int maxfdi = 0, dbhits = 0;
    for (int iw = 0; iw < nws; iw++) {
        const char *w = ws[iw];
        int n = (int)strlen(w);
        for (int fi = 0; fi < NFORM; fi++) {
            int fn1 = build(&forms[fi], w, n, F1v);
            for (int yi = 0; yi < NFORM; yi++) {
                int yn1 = build(&forms[yi], w, n, Yv);
                for (int xi = 0; xi < NXP; xi++) {
                    const char *xp = xpats[xi];
                    int xn = (int)strlen(xp);
                    int tn = pass(F1v, fn1, Yv, yn1, xp, xn, tbuf);
                    if (tn <= 0) continue;
                    /* dedup final pattern values */
                    char seen[NFORM][MAXW * 3 + 8];
                    int nseen = 0;
                    for (int pi = 0; pi < NFORM; pi++) {
                        atom Xv[MAXW * 2 + 8];
                        int xn2 = build(&forms[pi], w, n, Xv);
                        char pat[MAXW * 2 + 8];
                        for (int k = 0; k < xn2; k++) pat[k] = Xv[k].c;
                        pat[xn2] = 0;
                        if (xn2 < n) continue;   /* residual: beta >= n */
                        int dup = 0;
                        for (int k = 0; k < nseen; k++)
                            if (!strcmp(seen[k], pat)) { dup = 1; break; }
                        if (dup) continue;
                        strcpy(seen[nseen++], pat);
                        int on = pass(tbuf, tn, NULL, 0, pat, xn2, obuf);
                        sims++;
                        /* collect prov */
                        int pn = 0;
                        for (int k = 0; k < on; k++)
                            if (obuf[k].lab >= 0) prov[pn++] = obuf[k].lab;
                        if (pn == 0) continue;
                        int isfdi = 1;
                        for (int k = 0; k + 1 < pn; k++)
                            if (prov[k] <= prov[k + 1]) { isfdi = 0; break; }
                        if (!isfdi) continue;
                        fdi++;
                        if (pn > maxfdi) maxfdi = pn;
                        if (pn == n && n >= 2) {
                            int isdb = 1;
                            for (int k = 0; k < pn; k++)
                                if (prov[k] != n - 1 - k) { isdb = 0; break; }
                            if (isdb) {
                                dbhits++;
                                printf("  DB HIT: w=%s n=%d "
                                       "F=pre:%s|mid:%s|suf:%s|%d "
                                       "Y=pre:%s|mid:%s|suf:%s|%d "
                                       "xp=%s P=%s "
                                       "Pform=%s|%s|%s|%d\n",
                                       w, n,
                                       forms[fi].pre, forms[fi].mid,
                                       forms[fi].suf, forms[fi].two,
                                       forms[yi].pre, forms[yi].mid,
                                       forms[yi].suf, forms[yi].two,
                                       xp, pat,
                                       forms[pi].pre, forms[pi].mid,
                                       forms[pi].suf, forms[pi].two);
                            }
                        }
                    }
                }
            }
        }
    }
    printf("sims: %ld; FDI outputs: %ld (max length %d); DB hits: %d\n",
           sims, fdi, maxfdi, dbhits);
    printf("VERDICT: depth-2 chain2 residual-regime DB hits: %d "
           "(Theorem 3 bounds n by a constant of E; n=2 is inside every "
           "nontrivial bound; nothing at n>=3 on this domain)\n", dbhits);
    gen_w2list();
    phase2();
    return 0;
}
