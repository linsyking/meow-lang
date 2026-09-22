/* search.c — constructive search for the ONCE crux (oncecrux scratch dir).
 *
 * PROBLEM (main.tex thm:marking / cor:once-crux): is the constant once-node
 * [babba/baa]_1 computable in L restricted to the marked world
 * W0 = (ba|bb|baa)*  (there: replace the leftmost 'aa' by 'abba')?
 * A pipeline computing it on W0 closes the paper's main open problem.
 *
 * Modes (argv[1]):
 *   selftest <cls>            dump pass table + batteries + pair table for
 *                             Python cross-checking (xcheck.py)
 *   pairenum [maxlen]         enumerate all structurally fresh (M,A0) pairs
 *   sanity  <cls> <depth>     plain-text world, target [a/b]_1 (must find W)
 *   crux    <cls> <depth>     world (ba|bb|baa)*, target [babba/baa]_1
 *   trunc   <cls> <depth>     world (ba|bb|baa)*, target tau = prefix before
 *                             leftmost 'aa' (whole text if none)
 *   pair <M> <A0> <cls> <d>   world (ba|bb|M)*, target [A0/M]_1
 *   pairs  <cls> <depth>      run `pair` over ALL enumerated pairs (|M|,|A0|<=6)
 *   mitm <w:s|c|t> <g> <f>    meet-in-the-middle depth g+f, class W
 *
 * Classes: W   = pats {a,b}^{1..2}, repls {a,b}^{<=2}          (36 passes)
 *          C3  = pats {a,b}^{1..3}, repls {a,b}^{0..3}        (196 passes)
 *          C3p = C3 minus pattern "aaa" (never occurs in W0)  (182 passes)
 * Pipelines in RUN order; a pass [R/P] replaces every greedy leftmost
 * disjoint occurrence of P by R, never rescanning inserted text.
 *
 * Sound prunes in the DFS:
 *   - length prune: len * maxrl^(remaining) < tgtlen  => cut (each pass grows
 *     the text at most maxrl x: every input char emits <= maxrl chars);
 *   - final-pass length arithmetic: out = L + k(|R|-|P|) for the (single,
 *     determined) match count k, so (tgtlen-L) must be divisible by |R|-|P|
 *     with 0 <= k <= L/|P| (and L == tgtlen when |R| == |P|) -- necessary
 *     condition, checked before applying;
 *   - early aborts inside apply() vs the final target length (only used on
 *     the last pass, where they are sound);
 *   - active-pass prune (default ON; `noactive` disables): a pass changing no
 *     battery text at a non-final level is dropped -- deleting inert passes
 *     from any battery-matching pipeline gives a shorter matching
 *     subsequence, which the search then enumerates.
 *   - deepmatch (default ON; `nodeepmatch` restores the prior-art semantics
 *     of stopping a branch at its first battery match): report the match and
 *     keep exploring extensions (they may behave differently off-battery).
 * Wall-clock cap (tlimit=..., default 55 s) and node cap (maxnodes=...) abort
 * cleanly; g_aborted=1 marks an INCOMPLETE search.
 *
 * Compile: gcc -O3 -march=native -fopenmp -o search search.c
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <time.h>
#include <stdbool.h>

#ifdef _OPENMP
#include <omp.h>
#endif

#define MAXS    4096     /* DFS string buffer */
#define NBMAX   8        /* micro battery texts */
#define MAXPASS 256      /* passes per class */
#define MAXD    8        /* max pipeline depth */
#define MAXTOKL 16       /* max token length (pairs <= 6 + slack) */
#define FBMAX   4096     /* full battery capacity */
#define MITMBS  2048      /* MITM string buffer */

/* ------------------------------------------------------------------ timing */
static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}
static double g_t0, g_tlimit = 55.0;
static volatile int g_stop = 0;      /* deadline/cap reached: unwind */
static volatile int g_aborted = 0;   /* 1 => search incomplete */
static long long g_maxnodes = 0;      /* 0 = unlimited (per thread) */
static long long g_nodes = 0;        /* total admitted children (this run) */
static long long g_found = 0;        /* battery-matching pipelines (this run) */
static long long g_found_total = 0;  /* across pair runs */
static int g_nthreads = 1;
static int g_deepmatch = 1;
static char g_ctx[128] = "";

static void tick(void) {
    if (g_stop) return;
    if (now_s() - g_t0 > g_tlimit) { g_stop = 1; g_aborted = 1; }
}

/* ------------------------------------------------------------------- misc */
static uint64_t rngst = 0x9E3779B97F4A7C15ULL;
static uint64_t xr(void) {
    rngst ^= rngst << 13; rngst ^= rngst >> 7; rngst ^= rngst << 17;
    return rngst;
}
static void lg(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt); vprintf(fmt, ap); va_end(ap);
    printf("\n"); fflush(stdout);
}
static long long ipow(int b, int e) {
    long long r = 1; while (e-- > 0) r *= b; return r;
}

/* ------------------------------------------------------------------ class */
typedef struct {
    char name[8];
    int npass, maxrl;
    char P[MAXPASS][4]; int Pl[MAXPASS];
    char R[MAXPASS][4]; int Rl[MAXPASS];
} cls_t;
static cls_t CLS;

static void cls_build(const char *name) {
    const char *pats[24]; const char *reps[24];
    int np = 0, nr = 0;
    const char *all1[] = {"a","b"};
    const char *all2[] = {"aa","ab","ba","bb"};
    const char *all3[] = {"aaa","aab","aba","abb","baa","bab","bba","bbb"};
    if (!strcmp(name, "W")) {
        for (int i = 0; i < 2; i++) pats[np++] = all1[i];
        for (int i = 0; i < 4; i++) pats[np++] = all2[i];
        reps[nr++] = ""; for (int i = 0; i < 2; i++) reps[nr++] = all1[i];
        for (int i = 0; i < 4; i++) reps[nr++] = all2[i];
    } else if (!strcmp(name, "C3") || !strcmp(name, "C3p")) {
        for (int i = 0; i < 2; i++) pats[np++] = all1[i];
        for (int i = 0; i < 4; i++) pats[np++] = all2[i];
        for (int i = 0; i < 8; i++)
            if (strcmp(name, "C3p") || strcmp(all3[i], "aaa")) pats[np++] = all3[i];
        reps[nr++] = ""; for (int i = 0; i < 2; i++) reps[nr++] = all1[i];
        for (int i = 0; i < 4; i++) reps[nr++] = all2[i];
        for (int i = 0; i < 8; i++) reps[nr++] = all3[i];
    } else { fprintf(stderr, "bad class %s\n", name); exit(2); }
    CLS.npass = 0; CLS.maxrl = 0;
    snprintf(CLS.name, sizeof CLS.name, "%s", name);
    for (int r = 0; r < nr; r++)
        for (int p = 0; p < np; p++) {
            if (!strcmp(reps[r], pats[p])) continue;      /* identity pass */
            int i = CLS.npass;
            snprintf(CLS.R[i], 4, "%s", reps[r]); CLS.Rl[i] = (int)strlen(reps[r]);
            snprintf(CLS.P[i], 4, "%s", pats[p]); CLS.Pl[i] = (int)strlen(pats[p]);
            if (CLS.Rl[i] > CLS.maxrl) CLS.maxrl = CLS.Rl[i];
            CLS.npass++;
        }
}

/* ------------------------------------------------------------------ world */
typedef struct {
    char mode;                       /* 's' sanity 'c' crux 't' trunc 'p' pair */
    char M[MAXTOKL], A0[MAXTOKL]; int Ml, A0l;
    char tok[3][MAXTOKL]; int tokl[3];   /* product tokens {ba,bb,mark} */
} world_t;
static world_t W_;

static void world_crux(world_t *w) {
    memset(w, 0, sizeof *w);
    w->mode = 'c'; snprintf(w->M, MAXTOKL, "baa"); snprintf(w->A0, MAXTOKL, "babba");
    w->Ml = 3; w->A0l = 5;
    snprintf(w->tok[0], MAXTOKL, "ba"); w->tokl[0] = 2;
    snprintf(w->tok[1], MAXTOKL, "bb"); w->tokl[1] = 2;
    snprintf(w->tok[2], MAXTOKL, "baa"); w->tokl[2] = 3;
}
static void world_trunc(world_t *w) { world_crux(w); w->mode = 't'; }
static void world_sanity(world_t *w) { memset(w, 0, sizeof *w); w->mode = 's'; }
static void world_pair(world_t *w, const char *M, const char *A0) {
    memset(w, 0, sizeof *w);
    w->mode = 'p';
    snprintf(w->M, MAXTOKL, "%s", M); w->Ml = (int)strlen(M);
    snprintf(w->A0, MAXTOKL, "%s", A0); w->A0l = (int)strlen(A0);
    snprintf(w->tok[0], MAXTOKL, "ba"); w->tokl[0] = 2;
    snprintf(w->tok[1], MAXTOKL, "bb"); w->tokl[1] = 2;
    snprintf(w->tok[2], MAXTOKL, "%s", M); w->tokl[2] = w->Ml;
}

/* the oracle target restricted to the world */
static void target(const world_t *w, const char *in, char *out) {
    const char *p; int n;
    switch (w->mode) {
    case 's':                                  /* [a/b]_1 on plain texts */
        p = strchr(in, 'b');
        if (!p) { strcpy(out, in); return; }
        n = (int)(p - in);
        memcpy(out, in, (size_t)n); out[n] = 'a'; strcpy(out + n + 1, p + 1);
        return;
    case 'c': case 'p':                        /* [A0/M]_1 */
        p = strstr(in, w->M);
        if (!p) { strcpy(out, in); return; }
        n = (int)(p - in);
        memcpy(out, in, (size_t)n);
        memcpy(out + n, w->A0, (size_t)w->A0l);
        strcpy(out + n + w->A0l, p + w->Ml);
        return;
    case 't':                                  /* tau: prefix before 'aa' */
        p = strstr(in, "aa");
        if (!p) { strcpy(out, in); return; }
        n = (int)(p - in);
        memcpy(out, in, (size_t)n); out[n] = 0;
        return;
    }
    strcpy(out, in);
}

/* ---------------------------------------------------------------- battery */
static char BAT_IN[NBMAX][MAXS], BAT_TGT[NBMAX][MAXS];
static int NB, TGL[NBMAX];

/* micro battery token sequences (indices: 0=ba 1=bb 2=mark):
 *  {mark,bb,ba} {ba,bb,mark} {ba,mark,ba,mark} {ba,bb} {mark} {mark,mark,ba} */
static const int MSEQ[6][4] = {{2,1,0},{0,1,2},{0,2,0,2},{0,1},{2},{2,2,0}};
static const int MLEN[6]    = {3,3,4,2,1,3};

static void micro_battery(const world_t *w, int ntexts) {
    if (ntexts > NBMAX) ntexts = NBMAX;
    if (w->mode == 's') {
        static const char *ins[8] =
            {"abaab","bab","aabbaab","bba","a","ab","aabb","ba"};
        NB = ntexts;
        for (int j = 0; j < NB; j++) {
            strcpy(BAT_IN[j], ins[j]);
            target(w, BAT_IN[j], BAT_TGT[j]);
        }
    } else {
        NB = ntexts;
        for (int j = 0; j < NB; j++) {
            int o = 0, starts[8], nst = 0;
            for (int k = 0; k < MLEN[j]; k++) {
                int t = MSEQ[j][k];
                if (t == 2) starts[nst++] = o;          /* mark-token start */
                memcpy(BAT_IN[j] + o, w->tok[t], (size_t)w->tokl[t]);
                o += w->tokl[t];
            }
            BAT_IN[j][o] = 0;
            /* freshness assert: every occurrence of M starts at a mark-token */
            if (w->mode == 'c' || w->mode == 'p') {
                const char *q = BAT_IN[j];
                while ((q = strstr(q, w->M)) != NULL) {
                    int pos = (int)(q - BAT_IN[j]), okm = 0;
                    for (int k = 0; k < nst; k++) if (starts[k] == pos) okm = 1;
                    if (!okm) {
                        fprintf(stderr, "FRESHNESS VIOLATION in battery text %d\n", j);
                        exit(3);
                    }
                    q++;
                }
            }
            target(w, BAT_IN[j], BAT_TGT[j]);
        }
    }
    for (int j = 0; j < NB; j++) TGL[j] = (int)strlen(BAT_TGT[j]);
}

/* full battery: all token products of 0..5 tokens + 512 random 1..12 */
static char FB_IN[FBMAX][MAXS], FB_TGT[FBMAX][MAXS];
static int FB_N;
static void rand_product(const world_t *w, int maxtok, char *out) {
    int n = 1 + (int)(xr() % (uint64_t)maxtok), o = 0;
    for (int i = 0; i < n; i++) {
        int t = (int)(xr() % 3);
        memcpy(out + o, w->tok[t], (size_t)w->tokl[t]); o += w->tokl[t];
    }
    out[o] = 0;
}
static void build_full_battery(const world_t *w) {
    FB_N = 0;
    if (w->mode == 's') {
        for (int len = 0; len <= 10 && FB_N < FBMAX; len++)
            for (long v = 0; v < (1L << len) && FB_N < FBMAX; v++) {
                char *s = FB_IN[FB_N];
                for (int i = 0; i < len; i++) s[i] = (v >> i & 1) ? 'b' : 'a';
                s[len] = 0; FB_N++;
            }
        rngst = 4242;
        for (int i = 0; i < 512 && FB_N < FBMAX; i++) {
            int len = 1 + (int)(xr() % 24), o = 0;
            char *s = FB_IN[FB_N];
            for (int k = 0; k < len; k++) s[o++] = (xr() & 1) ? 'a' : 'b';
            s[o] = 0; FB_N++;
        }
    } else {
        for (int k = 0; k <= 5; k++) {
            long cnt = 1; for (int i = 0; i < k; i++) cnt *= 3;
            for (long v = 0; v < cnt; v++) {
                char *s = FB_IN[FB_N]; int o = 0; long vv = v;
                for (int i = 0; i < k; i++) {
                    int t = (int)(vv % 3); vv /= 3;
                    memcpy(s + o, w->tok[t], (size_t)w->tokl[t]); o += w->tokl[t];
                }
                s[o] = 0; FB_N++;
                if (FB_N >= FBMAX) { fprintf(stderr, "FB overflow\n"); exit(3); }
            }
        }
        rngst = 1717;
        for (int i = 0; i < 512 && FB_N < FBMAX; i++)
            rand_product(w, 12, FB_IN[FB_N]), FB_N++;
    }
    for (int j = 0; j < FB_N; j++) target(w, FB_IN[j], FB_TGT[j]);
}

/* ------------------------------------------------------------------- pass */
static int apply(int pi, const char *in, char *out, int tgtlen) {
    const char *P = CLS.P[pi], *R = CLS.R[pi];
    const int lp = CLS.Pl[pi], lr = CLS.Rl[pi], G = CLS.maxrl;
    int i = 0, o = 0, n = (int)strlen(in);
    while (i < n) {
        if (i + lp <= n && !memcmp(in + i, P, (size_t)lp)) {
            if (tgtlen >= 0) {
                if (o + lr > tgtlen) return 0;
                if (o + lr + G * (n - i - lp) < tgtlen) return 0;
            }
            memcpy(out + o, R, (size_t)lr); o += lr; i += lp;
        } else {
            if (tgtlen >= 0) {
                if (o + 1 > tgtlen) return 0;
                if (o + 1 + G * (n - i - 1) < tgtlen) return 0;
            }
            out[o++] = in[i++];
        }
    }
    out[o] = 0;
    return 1;
}

/* ------------------------------------------------------- dynamic buffers */
typedef struct { char *s; size_t cap; } dstr_t;
static void densure(dstr_t *d, size_t need) {
    if (need > d->cap) {
        d->cap = need * 2 + 64;
        d->s = realloc(d->s, d->cap);
        if (!d->s) { perror("realloc"); exit(4); }
    }
}
static void dapply(int pi, const char *in, dstr_t *out) {
    size_t n = strlen(in);
    densure(out, n * (size_t)CLS.maxrl + 1);
    apply(pi, in, out->s, -1);
}

/* --------------------------------------------------------- verification */
/* returns #mismatches (>=0), or -1 on time abort; stops early at limit */
static long long run_on_texts(const int *path, int depth,
                              char (*ins)[MAXS], char (*tgts)[MAXS], int n,
                              long long limit, int show) {
    dstr_t a = {0}, b = {0};
    long long bad = 0;
    for (int j = 0; j < n; j++) {
        densure(&a, strlen(ins[j]) + 1); strcpy(a.s, ins[j]);
        for (int k = 0; k < depth; k++) {
            dapply(path[k], a.s, &b);
            dstr_t t = a; a = b; b = t;
        }
        if (strcmp(a.s, tgts[j])) {
            bad++;
            if (show && bad <= 3)
                lg("    mismatch: in=%s got=%s want=%s", ins[j], a.s, tgts[j]);
            if (limit > 0 && bad >= limit) break;
        }
        if ((j & 1023) == 1023) tick();
        if (g_stop) { free(a.s); free(b.s); return -1; }
    }
    free(a.s); free(b.s);
    return bad;
}
/* escalation: random long texts (token products / plain strings), targets
 * computed on the fly; returns #mismatches or -1 on abort */
static long long run_on_random(const world_t *w, const int *path, int depth,
                               long long ntr, int maxlen, unsigned seed) {
    dstr_t a = {0}, b = {0}, in = {0}, tg = {0};
    long long bad = 0;
    uint64_t rs = seed;
    for (long long t = 0; t < ntr; t++) {
        int n = 1 + (int)(rs % (uint64_t)maxlen), o = 0;
        densure(&in, (size_t)maxlen * MAXTOKL + 2);
        if (w->mode == 's') {
            for (int i = 0; i < n; i++) {
                rs = rs * 6364136223846793005ULL + 1442695040888963407ULL;
                in.s[o++] = (rs >> 33) & 1 ? 'b' : 'a';
            }
        } else {
            for (int i = 0; i < n; i++) {
                int k = (int)(rs % 3);
                rs = rs * 6364136223846793005ULL + 1442695040888963407ULL;
                memcpy(in.s + o, w->tok[k], (size_t)w->tokl[k]);
                o += w->tokl[k];
            }
        }
        in.s[o] = 0;
        densure(&tg, (size_t)o + (size_t)w->A0l + 2);
        target(w, in.s, tg.s);
        densure(&a, (size_t)o + 1); strcpy(a.s, in.s);
        for (int k = 0; k < depth; k++) {
            dapply(path[k], a.s, &b);
            dstr_t x = a; a = b; b = x;
        }
        if (strcmp(a.s, tg.s)) {
            bad++;
            if (bad <= 3) lg("    ESC mismatch: in=%s got=%s want=%s", in.s, a.s, tg.s);
        }
        if ((t & 2047) == 2047) tick();
        if (g_stop) { free(a.s); free(b.s); free(in.s); free(tg.s); return -1; }
    }
    free(a.s); free(b.s); free(in.s); free(tg.s);
    return bad;
}

static void verify_candidate(const int *path, int depth) {
    char pl[2048]; pl[0] = 0;
    for (int i = 0; i < depth; i++) {
        char buf[64];
        snprintf(buf, sizeof buf, "[%s/%s]%s", CLS.R[path[i]], CLS.P[path[i]],
                 i + 1 < depth ? " " : "");
        if (strlen(pl) + strlen(buf) + 1 < sizeof pl) strcat(pl, buf);
    }
    lg("  run order (d=%d): %s", depth, pl);
    long long bad = run_on_texts(path, depth, FB_IN, FB_TGT, FB_N, 5, 1);
    if (g_stop && bad < 0) { lg("  verify: TIME ABORT"); return; }
    if (bad != 0) {
        lg("  full battery: %s%lld FAIL(S) of %d -- rejected",
           bad >= 5 ? ">= " : "", bad, FB_N);
        return;
    }
    lg("  *** FULL BATTERY PASS: %d texts ***", FB_N);
    long long e1 = run_on_random(&W_, path, depth, 300000, 40, 0xC0FFEE);
    if (e1 != 0) { lg("  escalation(<=40 tok): %lld fails -- rejected", e1); return; }
    lg("  *** ESCALATION-1 PASS: 300000 random products (<=40 tokens) ***");
    long long e2 = run_on_random(&W_, path, depth, 200000, 120, 0xBADF00D);
    if (e2 != 0) { lg("  escalation(<=120 tok): %lld fails -- rejected", e2); return; }
    lg("  *** ESCALATION-2 PASS: 200000 random products (<=120 tokens) ***");
    lg("  *** CANDIDATE SURVIVED ALL BATTERIES -- ESCALATE FOR HAND VERIFICATION ***");
}

static void report_candidate(const int *path, int depth) {
#pragma omp critical(repcand)
    {
        g_found++;
        lg("CANDIDATE depth %d: %s", depth, g_ctx);
        for (int i = 0; i < depth; i++)
            lg("  pass %d: [%s/%s]", i, CLS.R[path[i]], CLS.P[path[i]]);
        verify_candidate(path, depth);
    }
}

/* ------------------------------------------------------------------- DFS */
typedef char lv_t[MAXD + 2][NBMAX][MAXS];
static long long GPW[MAXD + 2];      /* maxrl^d */

static int at_target(lv_t lv, int depth) {
    for (int j = 0; j < NB; j++)
        if (strcmp(lv[depth][j], BAT_TGT[j])) return 0;
    return 1;
}

/* extend lv[depth] by pass pi into lv[depth+1] under the admission rules */
static int admit(lv_t lv, int depth, int pi, int maxd, int active, int *changed) {
    const int lp = CLS.Pl[pi], lr = CLS.Rl[pi];
    const long long gpow = GPW[maxd - depth];
    int ok = 1;
    *changed = 0;
    for (int j = 0; j < NB && ok; j++) {
        const int L = (int)strlen(lv[depth][j]);
        const int tl = TGL[j];
        if ((long long)L * gpow < (long long)tl) return 0;   /* growth prune */
        if (depth + 1 == maxd) {
            if (lr == lp) { if (L != tl) return 0; }
            else {
                int d = tl - L;
                if (d % (lr - lp) != 0) return 0;
                int k = d / (lr - lp);
                if (k < 0 || k > L / lp) return 0;
            }
            ok = apply(pi, lv[depth][j], lv[depth + 1][j], tl);
            if (ok) ok = !strcmp(lv[depth + 1][j], BAT_TGT[j]);
        } else {
            ok = apply(pi, lv[depth][j], lv[depth + 1][j], -1);
            if (ok && strcmp(lv[depth + 1][j], lv[depth][j])) *changed = 1;
        }
    }
    if (!ok) return 0;
    if (active && depth + 1 < maxd && !*changed) return 0;  /* inert pass */
    return 1;
}

static void dfs(lv_t lv, int depth, int maxd, int *path, int active,
                long long *nodes, int chk) {
    if (g_stop) return;
    if (chk && at_target(lv, depth)) {
        report_candidate(path, depth);
        if (!g_deepmatch) return;
    }
    if (depth == maxd) return;
    for (int pi = 0; pi < CLS.npass; pi++) {
        int changed;
        if (!admit(lv, depth, pi, maxd, active, &changed)) continue;
        path[depth] = pi;
        (*nodes)++;
        if (g_maxnodes > 0 && *nodes > g_maxnodes) { g_stop = 1; g_aborted = 1; return; }
        if ((*nodes & 63) == 0) tick();
        dfs(lv, depth + 1, maxd, path, active, nodes, 1);
        if (g_stop) return;
    }
}

static void run_dfs(int maxd, int active) {
    double t0 = now_s();
    for (int d = 0; d <= maxd; d++) GPW[d] = ipow(CLS.maxrl, d);
    long long total = 0;
    lv_t lv0;
    memcpy(lv0[0], BAT_IN, sizeof BAT_IN);
    if (maxd <= 0 || at_target(lv0, 0)) {
        int path[MAXD];
        if (at_target(lv0, 0)) report_candidate(path, 0);
        lg("nodes explored: %lld, battery-matching pipelines: %lld, elapsed: "
           "%.2f s, completed", 0L, g_found, now_s() - t0);
        return;
    }
#ifdef _OPENMP
#pragma omp parallel reduction(+: total)
#endif
    {
        lv_t *lv = malloc(sizeof(lv_t));
        int *path = malloc(sizeof(int) * MAXD);
        long long nodes = 0;
        memcpy((*lv)[0], BAT_IN, sizeof BAT_IN);
#ifdef _OPENMP
#pragma omp for schedule(dynamic, 1)
#endif
        for (long ab = 0; ab < (long)CLS.npass * CLS.npass; ab++) {
            if (g_stop) continue;
            int a = (int)(ab / CLS.npass), b = (int)(ab % CLS.npass);
            int ch;
            if (maxd == 1) {
                if (!admit(*lv, 0, a, 1, active, &ch)) continue;
                path[0] = a; nodes++;
                if (at_target(*lv, 1)) report_candidate(path, 1);
                continue;
            }
            if (!admit(*lv, 0, a, maxd, active, &ch)) continue;
            path[0] = a;
            if (b == 0) nodes++;          /* level-1 admission: count once */
            int m1 = at_target(*lv, 1);
            if (m1) {
                if (b == 0) report_candidate(path, 1);
                if (!g_deepmatch) continue;
            }
            if (!admit(*lv, 1, b, maxd, active, &ch)) continue;
            path[1] = b; nodes++;
            if (at_target(*lv, 2)) {
                report_candidate(path, 2);
                if (!g_deepmatch) continue;
            }
            if (maxd > 2) dfs(*lv, 2, maxd, path, active, &nodes, 0);
        }
        total += nodes;
        free(lv); free(path);
    }
    g_nodes += total;
    lg("nodes explored (admitted children): %lld", g_nodes);
    lg("battery-matching pipelines: %lld   elapsed: %.2f s   %s",
       g_found, now_s() - t0,
       g_aborted ? "*** ABORTED (cap) -- INCOMPLETE ***" : "completed");
}

/* ------------------------------------------------------- pair enumeration */
typedef struct { char M[MAXTOKL], A0[MAXTOKL]; } pair_t;
static pair_t PAIRS[8192];
static int NPAIRS;

/* tokens {ba,bb,M,A0}; every occurrence of M (resp A0) in every product of
 * 1..ntok tokens must start at an M-token (resp A0-token) */
static int pair_fresh(const char *M, const char *A0, int ntok,
                      char *wit, int witz) {
    const char *toks[4] = {"ba", "bb", M, A0};
    int tl[4] = {2, 2, (int)strlen(M), (int)strlen(A0)};
    int idx[8];
    char T[160];
    for (int k = 1; k <= ntok; k++) {
        for (long v = 0; v < (1L << (2 * k)); v++) {
            int o = 0; long vv = v;
            for (int i = 0; i < k; i++) { idx[i] = (int)(vv & 3); vv >>= 2; }
            for (int i = 0; i < k; i++) {
                memcpy(T + o, toks[idx[i]], (size_t)tl[idx[i]]);
                o += tl[idx[i]];
            }
            T[o] = 0;
            for (int m = 0; m < 2; m++) {
                const char *marker = m ? A0 : M;
                const char *q = T;
                while ((q = strstr(q, marker)) != NULL) {
                    int pos = (int)(q - T), p = 0, okm = 0;
                    for (int i = 0; i < k; i++) {
                        if (pos == p && idx[i] == 2 + m) okm = 1;
                        p += tl[idx[i]];
                    }
                    if (!okm) {
                        if (wit) snprintf(wit, witz, "T=%s marker=%s pos=%d",
                                          T, marker, pos);
                        return 0;
                    }
                    q++;
                }
            }
        }
    }
    return 1;
}

static int is_cell(const char *s) { return !strcmp(s, "ba") || !strcmp(s, "bb"); }

static void enum_pairs(int maxlen) {
    char M[MAXTOKL], A0[MAXTOKL], wit[160];
    NPAIRS = 0;
    for (int lm = 2; lm <= maxlen; lm++)
        for (long vm = 0; vm < (1L << lm); vm++) {
            for (int i = 0; i < lm; i++) M[i] = (vm >> i & 1) ? 'b' : 'a';
            M[lm] = 0;
            if (is_cell(M)) continue;
            for (int la = 2; la <= maxlen; la++)
                for (long va = 0; va < (1L << la); va++) {
                    for (int i = 0; i < la; i++) A0[i] = (va >> i & 1) ? 'b' : 'a';
                    A0[la] = 0;
                    if (is_cell(A0) || !strcmp(A0, M)) continue;
                    if (pair_fresh(M, A0, 4, wit, sizeof wit)) {
                        if (NPAIRS >= 8192) { fprintf(stderr, "too many pairs\n"); exit(3); }
                        strcpy(PAIRS[NPAIRS].M, M);
                        strcpy(PAIRS[NPAIRS].A0, A0);
                        NPAIRS++;
                    }
                }
        }
}

/* ------------------------------------------------------------- selftest */
static void dump_str(FILE *f, const char *s) {
    if (!*s) { fputs("<e>", f); return; }
    for (; *s; s++) fputc(*s, f);
}
static void selftest(void) {
    printf("CLASS %s npass %d maxrl %d\n", CLS.name, CLS.npass, CLS.maxrl);
    for (int pi = 0; pi < CLS.npass; pi++) {
        printf("PASS "); dump_str(stdout, CLS.R[pi]); printf(" ");
        dump_str(stdout, CLS.P[pi]); printf("\n");
    }
    static const char *texts[] = {
        "baabbba", "babbbaa", "babaababaa", "babb", "baa", "baabaaba",
        "", "a", "b", "aa", "ab", "ba", "bb", "aab", "aba", "abb", "baa",
        "bab", "bba", "bbb", "aaa", "abab", "babaab", "bbabaa", "abaab"
    };
    int nt = (int)(sizeof texts / sizeof *texts);
    for (int pi = 0; pi < CLS.npass; pi++)
        for (int t = 0; t < nt; t++) {
            char out[MAXS];
            apply(pi, texts[t], out, -1);
            printf("APPLY "); dump_str(stdout, CLS.R[pi]); printf(" ");
            dump_str(stdout, CLS.P[pi]); printf(" ");
            dump_str(stdout, texts[t]); printf(" ");
            dump_str(stdout, out); printf("\n");
        }
    /* pair table */
    printf("PAIRS %d\n", NPAIRS);
    for (int i = 0; i < NPAIRS; i++)
        printf("PAIR %s %s\n", PAIRS[i].M, PAIRS[i].A0);
    /* batteries + targets for world flavors */
    world_t ws[5];
    world_sanity(&ws[0]); world_crux(&ws[1]); world_trunc(&ws[2]);
    world_pair(&ws[3], "baa", "babba");
    const char *wn[5] = {"sanity", "crux", "trunc", "pair", "pair"};
    int nw = 4;
    if (NPAIRS > 1) { world_pair(&ws[4], PAIRS[1].M, PAIRS[1].A0); nw = 5; }
    for (int i = 0; i < nw; i++) {
        micro_battery(&ws[i], 6);
        printf("BATW %s %s %s n %d\n", wn[i], ws[i].M, ws[i].A0, NB);
        for (int j = 0; j < NB; j++) {
            printf("BAT "); dump_str(stdout, BAT_IN[j]); printf(" ");
            dump_str(stdout, BAT_TGT[j]); printf("\n");
        }
        build_full_battery(&ws[i]);
        printf("FBW %s %s %s n %d\n", wn[i], ws[i].M, ws[i].A0, FB_N);
        for (int j = 0; j < FB_N; j += (FB_N > 400 ? 7 : 1)) {
            printf("FB "); dump_str(stdout, FB_IN[j]); printf(" ");
            dump_str(stdout, FB_TGT[j]); printf("\n");
        }
        /* target-formulation consistency on crux texts:
         * [babba/baa]_1 T == T[:m] . "b" . "abba" . T[m+3:] == tau(T) . "abba" . T[m+3:]
         * with m+1 the leftmost 'aa' position */
        if (ws[i].mode == 'c') {
            for (int j = 0; j < FB_N; j++) {
                char tau[MAXS], want[MAXS], got[MAXS];
                const char *pa = strstr(FB_IN[j], "aa");
                const char *q = strstr(FB_IN[j], "baa");
                if (!pa || !q) continue;
                int n = (int)(pa - FB_IN[j]);
                int m = (int)(q - FB_IN[j]);
                if (n != m + 1) {
                    fprintf(stderr, "AA/BAA ALIGN FAIL %s\n", FB_IN[j]);
                    exit(3);
                }
                memcpy(tau, FB_IN[j], (size_t)n); tau[n] = 0;
                memcpy(want, FB_IN[j], (size_t)(m + 1)); want[m + 1] = 0;
                strcat(want, "abba"); strcat(want, FB_IN[j] + m + 3);
                target(&ws[i], FB_IN[j], got);
                /* both formulations must equal the oracle target, and tau
                 * must be exactly the prefix through the mark's 'b' */
                if (strcmp(want, got) != 0 || (int)strlen(tau) != m + 1) {
                    fprintf(stderr, "TARGET CONSISTENCY FAIL %s\n", FB_IN[j]);
                    exit(3);
                }
            }
        }
    }
}

/* ------------------------------------------------------------------ MITM */
/* W-class only.  depth <= g+f: g-side = first passes applied to the battery
 * tuple (levels 1..g-1 stored deduped per level, level g stored raw), f-side
 * = ALL pipelines of depth <= f (no dedup).  Join: f(mid) == targets exactly.
 * FVAL encoding: -1 identity; p (<npass) single pass; npass + p1*npass + p2
 * a pair. */
typedef struct { char *s[NBMAX]; } sig_t;
static sig_t *MLEV[9];
static long  MLEVN[9];
static int  *MGPIPE[9];
static char MT0[NBMAX][MITMBS], MT[NBMAX][MITMBS];

typedef struct { char *s; } ustr_t;
static ustr_t *UARR; static long UN;
static long *UHT; static long UHTSZ;
static int  *FCNT; static long *FOFF; static int *FVAL; static long FTOT;

static uint64_t hstr(const char *s, size_t n) {
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) { h ^= (unsigned char)s[i]; h *= 1099511628211ULL; }
    return h;
}
static long u_find(const char *key) {
    uint64_t h = hstr(key, strlen(key));
    long i = (long)(h % (uint64_t)UHTSZ);
    while (UHT[i] != -1) {
        if (!strcmp(UARR[UHT[i]].s, key)) return UHT[i];
        i = (i + 1) % UHTSZ;
    }
    return -1;
}

static void mpass_apply(int pi, const char *in, char *out) {
    const char *P = CLS.P[pi], *R = CLS.R[pi];
    const int lp = CLS.Pl[pi], lr = CLS.Rl[pi];
    int i = 0, o = 0, n = (int)strlen(in);
    while (i < n) {
        if (i + lp <= n && !memcmp(in + i, P, (size_t)lp)) {
            memcpy(out + o, R, (size_t)lr); o += lr; i += lp;
        } else out[o++] = in[i++];
    }
    out[o] = 0;
}
static int mpass_apply_ab(int pi, const char *in, char *out, int tgtlen) {
    const char *P = CLS.P[pi], *R = CLS.R[pi];
    const int lp = CLS.Pl[pi], lr = CLS.Rl[pi];
    int i = 0, o = 0, n = (int)strlen(in);
    while (i < n) {
        if (i + lp <= n && !memcmp(in + i, P, (size_t)lp)) {
            if (o + lr > tgtlen) return 0;
            if (o + lr + 2 * (n - i - lp) < tgtlen) return 0;
            memcpy(out + o, R, (size_t)lr); o += lr; i += lp;
        } else {
            if (o + 1 > tgtlen) return 0;
            if (o + 1 + 2 * (n - i - 1) < tgtlen) return 0;
            out[o++] = in[i++];
        }
    }
    out[o] = 0;
    return 1;
}

static void mitm(int g, int f) {
    double t0 = now_s();
    micro_battery(&W_, 4);
    int nb = NB;
    for (int j = 0; j < nb; j++) {
        snprintf(MT0[j], MITMBS, "%s", BAT_IN[j]);
        snprintf(MT[j], MITMBS, "%s", BAT_TGT[j]);
    }
    lg("MITM: class %s, g=%d f=%d, battery %d texts, tlimit %.0fs",
       CLS.name, g, f, nb, g_tlimit);
    for (int j = 0; j < nb; j++) lg("  in %-16s tgt %s", MT0[j], MT[j]);
    /* ---- build levels 1..g (level g raw, others deduped) ---- */
    MLEVN[0] = 1;
    MLEV[0] = malloc(sizeof(sig_t));
    MGPIPE[0] = malloc(sizeof(int));
    for (int j = 0; j < nb; j++) MLEV[0][0].s[j] = strdup(BAT_IN[j]);
    MGPIPE[0][0] = -1;
    for (int lev = 1; lev <= g; lev++) {
        int final = (lev == g);
        long cap = MLEVN[lev - 1] * CLS.npass + 16;
        MLEV[lev] = malloc(sizeof(sig_t) * (size_t)cap);
        if (!MLEV[lev]) { fprintf(stderr, "OOM level %d\n", lev); exit(4); }
        MGPIPE[lev] = malloc(sizeof(int) * (size_t)cap * (size_t)(lev + 1));
        long htsz = 0; long *ht = NULL;
        if (!final) {
            htsz = 1; while (htsz < cap * 2) htsz <<= 1;
            ht = malloc(sizeof(long) * (size_t)htsz);
            for (long i = 0; i < htsz; i++) ht[i] = -1;
        }
        long n = 0;
        for (long s = 0; s < MLEVN[lev - 1] && !g_stop; s++) {
            for (int pi = 0; pi < CLS.npass; pi++) {
                char tmp[NBMAX][MITMBS];
                for (int j = 0; j < nb; j++)
                    mpass_apply(pi, MLEV[lev - 1][s].s[j], tmp[j]);
                if (final) {
                    for (int j = 0; j < nb; j++)
                        MLEV[lev][n].s[j] = strdup(tmp[j]);
                    int *gp = MGPIPE[lev] + n * (lev + 1);
                    for (int i = 0; i < lev - 1; i++)
                        gp[i] = MGPIPE[lev - 1][s * lev + i];
                    gp[lev - 1] = pi;
                    n++;
                } else {
                    uint64_t h = 1469598103934665603ULL;
                    for (int j = 0; j < nb; j++) {
                        h ^= hstr(tmp[j], strlen(tmp[j]));
                        h *= 1099511628211ULL;
                    }
                    long i = (long)(h % (uint64_t)htsz);
                    int dup = 0;
                    while (ht[i] != -1) {
                        sig_t *e = &MLEV[lev][ht[i]];
                        int same = 1;
                        for (int j = 0; j < nb; j++)
                            if (strcmp(e->s[j], tmp[j])) { same = 0; break; }
                        if (same) { dup = 1; break; }
                        i = (i + 1) % htsz;
                    }
                    if (dup) continue;
                    for (int j = 0; j < nb; j++)
                        MLEV[lev][n].s[j] = strdup(tmp[j]);
                    int *gp = MGPIPE[lev] + n * (lev + 1);
                    for (int i = 0; i < lev - 1; i++)
                        gp[i] = MGPIPE[lev - 1][s * lev + i];
                    gp[lev - 1] = pi;
                    long i2 = (long)(h % (uint64_t)htsz);
                    while (ht[i2] != -1) i2 = (i2 + 1) % htsz;
                    ht[i2] = n;
                    n++;
                }
            }
            if ((s & 255) == 255) tick();
        }
        MLEVN[lev] = n;
        if (ht) free(ht);
        lg("  level %d: %ld sigs  (%.1f s)", lev, n, now_s() - t0);
        if (g_stop) { lg("*** MITM ABORTED during level build ***"); return; }
    }
    /* ---- collect distinct first coordinates over level g ---- */
    long raw = MLEVN[g];
    UHTSZ = 1; while (UHTSZ < raw * 2) UHTSZ <<= 1;
    UHT = malloc(sizeof(long) * (size_t)UHTSZ);
    for (long i = 0; i < UHTSZ; i++) UHT[i] = -1;
    UARR = malloc(sizeof(ustr_t) * (size_t)(raw > 0 ? raw : 1));
    UN = 0;
    for (long s = 0; s < raw && !g_stop; s++) {
        const char *m1 = MLEV[g][s].s[0];
        uint64_t h = hstr(m1, strlen(m1));
        long i = (long)(h % (uint64_t)UHTSZ);
        int dup = 0;
        while (UHT[i] != -1) {
            if (!strcmp(UARR[UHT[i]].s, m1)) { dup = 1; break; }
            i = (i + 1) % UHTSZ;
        }
        if (dup) continue;
        UARR[UN].s = strdup(m1);
        UHT[i] = UN; UN++;
        if ((s & 1023) == 1023) tick();
    }
    lg("  distinct first-coordinate strings |U| = %ld  (%.1f s)", UN, now_s() - t0);
    if (g_stop) { lg("*** MITM ABORTED during U build ***"); return; }
    /* ---- F_u = { f depth<=f : f(u) == t1 } ---- */
    int t1l = (int)strlen(MT[0]);
    int nf1 = (f >= 1) ? CLS.npass : 0;
    FCNT = calloc((size_t)(UN > 0 ? UN : 1), sizeof(int));
    FOFF = malloc(sizeof(long) * (size_t)(UN + 1));
    FTOT = 0;
    /* pass 1 of 2: counts (f<=2 assumed: single or pair) */
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 64)
#endif
    for (long u = 0; u < UN; u++) {
        if (g_stop) continue;
        const char *us = UARR[u].s;
        int cnt = 0;
        char v[MITMBS], w[MITMBS];
        if (!strcmp(us, MT[0])) cnt++;                       /* identity */
        for (int p1 = 0; p1 < nf1; p1++) {
            mpass_apply(p1, us, v);
            if (!strcmp(v, MT[0])) cnt++;                     /* single */
            if (f >= 2)
                for (int p2 = 0; p2 < CLS.npass; p2++)
                    if (mpass_apply_ab(p2, v, w, t1l) && !strcmp(w, MT[0])) cnt++;
        }
        FCNT[u] = cnt;
    }
    for (long u = 0; u < UN; u++) { FOFF[u] = FTOT; FTOT += FCNT[u]; }
    FOFF[UN] = FTOT;
    FVAL = malloc(sizeof(int) * (size_t)(FTOT > 0 ? FTOT : 1));
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 64)
#endif
    for (long u = 0; u < UN; u++) {
        if (g_stop) continue;
        const char *us = UARR[u].s;
        int cnt = 0;
        char v[MITMBS], w[MITMBS];
        if (!strcmp(us, MT[0])) FVAL[FOFF[u] + cnt++] = -1;
        for (int p1 = 0; p1 < nf1; p1++) {
            mpass_apply(p1, us, v);
            if (!strcmp(v, MT[0])) FVAL[FOFF[u] + cnt++] = p1;
            if (f >= 2)
                for (int p2 = 0; p2 < CLS.npass; p2++)
                    if (mpass_apply_ab(p2, v, w, t1l) && !strcmp(w, MT[0]))
                        FVAL[FOFF[u] + cnt++] = CLS.npass + p1 * CLS.npass + p2;
        }
    }
    lg("  F-table: %ld entries over %ld u's  (%.1f s)", FTOT, UN, now_s() - t0);
    /* ---- join ---- */
    long tried = 0, hits = 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 64) reduction(+:tried,hits)
#endif
    for (long s = 0; s < raw; s++) {
        if (g_stop) continue;
        sig_t *sg = &MLEV[g][s];
        long u = u_find(sg->s[0]);
        if (u < 0) continue;
        for (long fi = FOFF[u]; fi < FOFF[u + 1]; fi++) {
            int fv = FVAL[fi];
            int ok = 1;
            char cur[NBMAX][MITMBS], tmp[NBMAX][MITMBS];
            for (int j = 1; j < nb; j++) strcpy(cur[j], sg->s[j]);
            if (fv == -1) {
                for (int j = 1; j < nb && ok; j++) ok = !strcmp(cur[j], MT[j]);
            } else if (fv < CLS.npass) {
                for (int j = 1; j < nb && ok; j++)
                    ok = mpass_apply_ab(fv, cur[j], tmp[j], (int)strlen(MT[j]))
                         && !strcmp(tmp[j], MT[j]);
            } else {
                int p1 = (fv - CLS.npass) / CLS.npass;
                int p2 = (fv - CLS.npass) % CLS.npass;
                for (int j = 1; j < nb && ok; j++) {
                    mpass_apply(p1, cur[j], tmp[j]); strcpy(cur[j], tmp[j]);
                    ok = mpass_apply_ab(p2, cur[j], tmp[j], (int)strlen(MT[j]))
                         && !strcmp(tmp[j], MT[j]);
                }
            }
            tried++;
            if (ok) {
                hits++;
                int path[MAXD], d = 0;
                for (int i = 0; i < g; i++) path[d++] = MGPIPE[g][s * (g + 1) + i];
                if (fv == -1) { /* identity: nothing */ }
                else if (fv < CLS.npass) path[d++] = fv;
                else {
                    path[d++] = (fv - CLS.npass) / CLS.npass;
                    path[d++] = (fv - CLS.npass) % CLS.npass;
                }
                report_candidate(path, d);
            }
            if ((fi & 63) == 0) tick();
            if (g_stop) break;
        }
        if ((s & 63) == 0) tick();
    }
    lg("MITM done: %ld (sig,f) pairs tried, %ld full joins, %lld candidates, "
       "%.1f s, %s", tried, hits, g_found, now_s() - t0,
       g_aborted ? "*** ABORTED (cap) -- INCOMPLETE ***" : "completed");
}

/* ------------------------------------------------------------------ main */
static void set_world(const char *s) {
    if (!strcmp(s, "s") || !strcmp(s, "sanity")) world_sanity(&W_);
    else if (!strcmp(s, "c") || !strcmp(s, "crux")) world_crux(&W_);
    else if (!strcmp(s, "t") || !strcmp(s, "trunc")) world_trunc(&W_);
    else { fprintf(stderr, "bad world\n"); exit(2); }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header comment\n"); return 2; }
    g_t0 = now_s();
    const char *mode = argv[1];
    int ntexts = 6, active = 1;
    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "noactive")) active = 0;
        else if (!strcmp(argv[i], "nodeepmatch")) g_deepmatch = 0;
        else if (!strncmp(argv[i], "tlimit=", 7)) g_tlimit = atof(argv[i] + 7);
        else if (!strncmp(argv[i], "maxnodes=", 9)) g_maxnodes = atoll(argv[i] + 9);
        else if (!strncmp(argv[i], "ntexts=", 7)) ntexts = atoi(argv[i] + 7);
        else if (!strcmp(argv[i], "seq")) g_nthreads = -1;
    }
#ifdef _OPENMP
    if (g_nthreads < 0) omp_set_num_threads(1);
    g_nthreads = omp_get_max_threads();
#endif
    if (!strcmp(mode, "pairenum")) {
        int maxlen = (argc > 2) ? atoi(argv[2]) : 6;
        enum_pairs(maxlen);
        lg("# valid (M,A0) pairs with |M|,|A0| <= %d (ntok=4 check): %d",
           maxlen, NPAIRS);
        int n5 = 0;
        for (int i = 0; i < NPAIRS; i++) {
            char wit[160];
            int ok5 = pair_fresh(PAIRS[i].M, PAIRS[i].A0, 5, wit, sizeof wit);
            int ok6 = pair_fresh(PAIRS[i].M, PAIRS[i].A0, 6, wit, sizeof wit);
            if (strlen(PAIRS[i].M) <= 5 && strlen(PAIRS[i].A0) <= 5) n5++;
            lg("PAIR %s %s len %d %d ntok5 %d ntok6 %d",
               PAIRS[i].M, PAIRS[i].A0, (int)strlen(PAIRS[i].M),
               (int)strlen(PAIRS[i].A0), ok5, ok6);
        }
        lg("# pairs with |M|,|A0| <= 5: %d (cross-check vs find_constants)", n5);
        return 0;
    }
    if (!strcmp(mode, "selftest")) {
        cls_build(argc > 2 ? argv[2] : "W");
        enum_pairs(6);
        selftest();
        return 0;
    }
    if (!strcmp(mode, "sanity") || !strcmp(mode, "crux") ||
        !strcmp(mode, "trunc")) {
        if (argc < 4) { fprintf(stderr, "need cls depth\n"); return 2; }
        cls_build(argv[2]);
        int depth = atoi(argv[3]);
        set_world(mode);
        micro_battery(&W_, ntexts);
        build_full_battery(&W_);
        lg("mode %s class %s (%d passes, maxrl %d) depth <= %d  battery %d "
           "texts  full-battery %d  active %d deepmatch %d threads %d",
           mode, CLS.name, CLS.npass, CLS.maxrl, depth, NB, FB_N, active,
           g_deepmatch, g_nthreads);
        for (int j = 0; j < NB; j++) lg("  in %-16s tgt %s", BAT_IN[j], BAT_TGT[j]);
        run_dfs(depth, active);
        return 0;
    }
    if (!strcmp(mode, "pair")) {
        if (argc < 6) { fprintf(stderr, "need M A0 cls depth\n"); return 2; }
        cls_build(argv[4]);
        int depth = atoi(argv[5]);
        world_pair(&W_, argv[2], argv[3]);
        char wit[160];
        if (!pair_fresh(argv[2], argv[3], 4, wit, sizeof wit)) {
            lg("pair (%s,%s) is NOT structurally fresh: %s", argv[2], argv[3], wit);
            return 1;
        }
        micro_battery(&W_, ntexts);
        build_full_battery(&W_);
        snprintf(g_ctx, sizeof g_ctx, "pair");
        lg("mode pair (%s,%s) class %s depth <= %d battery %d texts", argv[2],
           argv[3], CLS.name, depth, NB);
        run_dfs(depth, active);
        return 0;
    }
    if (!strcmp(mode, "pairs")) {
        if (argc < 4) { fprintf(stderr, "need cls depth\n"); return 2; }
        cls_build(argv[2]);
        int depth = atoi(argv[3]);
        int start = 0, end = 1 << 30;
        for (int i = 4; i < argc; i++) {
            if (!strncmp(argv[i], "start=", 6)) start = atoi(argv[i] + 6);
            else if (!strncmp(argv[i], "end=", 4)) end = atoi(argv[i] + 4);
        }
        enum_pairs(6);
        if (end > NPAIRS) end = NPAIRS;
        lg("# pairs: %d; searching worlds (ba|bb|M)* over class %s depth "
           "<= %d, pairs [%d,%d), tlimit %.0f",
           NPAIRS, CLS.name, depth, start, end, g_tlimit);
        for (int i = start; i < end; i++) {
            if (g_stop) {
                lg("STOP at pair index %d (of [%d,%d)) due to %s -- resume "
                   "with start=%d", i, start, end,
                   g_aborted ? "time cap" : "stop", i);
                break;
            }
            double t0 = now_s();
            g_nodes = 0; g_found = 0;
            world_pair(&W_, PAIRS[i].M, PAIRS[i].A0);
            micro_battery(&W_, ntexts);
            build_full_battery(&W_);
            snprintf(g_ctx, sizeof g_ctx, "pair %d/%d (%s,%s)", i, NPAIRS,
                     PAIRS[i].M, PAIRS[i].A0);
            lg("pair %d/%d (%s,%s):", i, NPAIRS, PAIRS[i].M, PAIRS[i].A0);
            run_dfs(depth, active);
            g_found_total += g_found;
            lg("  pair time %.2f s", now_s() - t0);
        }
        lg("pairs loop %s [%d,%d); total battery matches: %lld",
           g_aborted ? "ABORTED (incomplete)" : "completed", start, end,
           g_found_total);
        return 0;
    }
    if (!strcmp(mode, "mitm")) {
        if (argc < 5) { fprintf(stderr, "need world g f\n"); return 2; }
        set_world(argv[2]);
        int g = atoi(argv[3]), f = atoi(argv[4]);
        cls_build("W");
        build_full_battery(&W_);
        snprintf(g_ctx, sizeof g_ctx, "mitm");
        mitm(g, f);
        return 0;
    }
    fprintf(stderr, "bad mode %s\n", mode);
    return 2;
}
