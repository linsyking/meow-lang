/* SEPARABLE HUNT: exhaustive-in-shape falsification of the Separable
 * Rigidity theorem (REPORT.md sec 2, this dir) at S-depth <= 4, on
 * SEPARABLE inputs: w with pairwise-distinct letters disjoint from
 * Gamma = {a,b}.  By letter renaming (any injective map fixing {a,b}),
 * every separable w of length n is isomorphic to the canonical
 * w_n = "cdef..."[:n]; sweeping the canonical input per length is
 * therefore EXHAUSTIVE over all separable inputs of that length.
 *
 * THEOREM PREDICTS, for every swept pipeline and every n >= 2:
 *   (i)   every match window covers whole instances (copy-alignment),
 *         instances stay contiguous full FORWARD copies of w
 *         (labels 0..n-1);
 *   (ii)  prov = (0,1,...,n-1)^M;
 *   (iii) content = v0 w v1 ... w vM with v_j in {a,b}*;
 *   (iv)  prov is never DB, never FDI of length >= 2; content != rev(w).
 * Any hit on (i)-(iv) falsifies the hand proof.  The sweep is the
 * falsification instrument, not the evidence.
 *
 * Pass-free form table (24 forms): value = c[0] w c[1] w ... w c[k] with
 * constant parts in {a,b}*.  Indices are printed in CROSS lines and
 * re-parsed/re-verified by verify_hunt_cross.py against prov.py's lden.
 *
 * Modes (argv[1]):
 *   1 = chain1 (FULL/FULL) + chain2 (P9/FULL) + chain3 (P9/FULL)
 *   2 = chain4 (P6/F12)
 *   3 = deepP3 + deepR3 (P9 inner, F12 outer)
 *   4 = deepP4 + deepR4 (P6 inner, F12 outer)
 *   5 = C-compositions C(chain_a, chain_b), a+b <= 2 (P9/FULL)
 *       and a+b = 3 (P6/F8)
 *   9 = debug: single chain spec from argv (n F1 R1 P1 R2 P2 ...)
 * Pools: FULL = all 24 forms; P9/P6 = reduced pass pools incl. eps
 * (deletion); F12/F8 = reduced scrutinee pools.  CROSS lines carry
 * the simulator's prov (prefix 48, length, weighted checksum) for
 * prov.py re-verification by verify_hunt_cross.py.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 10
#define MAXATOMS 200000
#define MAXINST 800000

typedef struct { char c; int lab, iid; } atom;

static const struct { const char *c[4]; int ncopies; } forms[] = {
    /* value = c[0] w c[1] w c[2] w c[3] with ncopies w's            */
    /* 0*/  {{"",   "",  "",  ""}, 0},   /* eps        */
    /* 1*/  {{"",   "",  "",  ""}, 1},   /* w          */
    /* 2*/  {{"",   "",  "",  ""}, 2},   /* w w        */
    /* 3*/  {{"",   "",  "",  ""}, 3},   /* w w w      */
    /* 4*/  {{"a",  "",  "",  ""}, 1},   /* a w        */
    /* 5*/  {{"",   "a", "",  ""}, 1},   /* w a        */
    /* 6*/  {{"a",  "a", "",  ""}, 1},   /* a w a      */
    /* 7*/  {{"b",  "",  "",  ""}, 1},   /* b w        */
    /* 8*/  {{"",   "b", "",  ""}, 1},   /* w b        */
    /* 9*/  {{"a",  "b", "",  ""}, 1},   /* a w b      */
    /*10*/  {{"b",  "a", "",  ""}, 1},   /* b w a      */
    /*11*/  {{"ab", "",  "",  ""}, 1},   /* ab w       */
    /*12*/  {{"",   "ab", "",  ""}, 1},  /* w ab       */
    /*13*/  {{"a",  "",  "",  ""}, 2},   /* a w w      */
    /*14*/  {{"",   "",  "a", ""}, 2},   /* w w a      */
    /*15*/  {{"a",  "",  "a", ""}, 2},   /* a w w a    */
    /*16*/  {{"",   "a", "",  ""}, 2},   /* w a w      */
    /*17*/  {{"",   "b", "",  ""}, 2},   /* w b w      */
    /*18*/  {{"a",  "b", "a", ""}, 2},   /* a w b w a  */
    /*19*/  {{"a",  "",  "",  ""}, 0},   /* "a"        */
    /*20*/  {{"b",  "",  "",  ""}, 0},   /* "b"        */
    /*21*/  {{"aa", "",  "",  ""}, 0},   /* "aa"       */
    /*22*/  {{"ab", "",  "",  ""}, 0},   /* "ab"       */
    /*23*/  {{"ba", "",  "",  ""}, 0},   /* "ba"       */
};
#define NFORM 24

static const int FULL[24] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,
                             18,19,20,21,22,23};
static const int F12[12] = {0,1,2,4,5,9,13,16,19,20,21,22};
static const int F8[8]   = {1,2,4,5,9,16,19,22};
/* reduced pass pools (R and P slots; eps = deletion included):
 * pi=0 constants, pi=1 one/two-sided, pi=2 glued */
static const int P9[9]   = {0,19,22,1,4,5,2,9,16};
static const int P7[7]   = {0,19,22,1,4,2,9};
static const int P6[6]   = {0,19,1,4,2,9};

static char ws[MAXW + 1];
static int n;
static long sims, defined, undef, capped;
static long cutwin, splitinst, badinst, badprov, badform, dbhits, fdihits,
            revhits, crossn;
static long cross_every = 65536;
static const atom *lastout;
static long lasttn;

static atom *B[10];
static atom *SCR;
static atom *LEFT;    /* composition / deep-value scratch */
static long istart_[MAXINST];
static int icount_[MAXINST];
static int iidmax;

static long build_form(int fi, atom *out, int *iidc)
{
    long L = 0;
    int k = forms[fi].ncopies;
    for (int i = 0; i <= k; i++) {
        for (const char *p = forms[fi].c[i]; *p; p++) {
            out[L].c = *p; out[L].lab = -1; out[L].iid = -1; L++;
        }
        if (i < k) {
            int iid = ++(*iidc);
            for (int j = 0; j < n; j++) {
                out[L].c = ws[j]; out[L].lab = j; out[L].iid = iid; L++;
            }
        }
    }
    return L;
}

static void check_instances(const atom *t, long tn)
{
    for (int i = 0; i <= iidmax; i++) icount_[i] = 0;
    for (long i = 0; i < tn; i++) {
        if (t[i].iid < 0) {
            if (t[i].lab >= 0) { badinst++; return; }
            continue;
        }
        if (icount_[t[i].iid] == 0) istart_[t[i].iid] = i;
        icount_[t[i].iid]++;
    }
    for (int iid = 1; iid <= iidmax; iid++) {
        int c = icount_[iid];
        if (!c) continue;
        long s = istart_[iid];
        if (t[s + c - 1].iid != iid) { splitinst++; return; }
        if (c != n) { badinst++; return; }
        for (int j = 0; j < c; j++)
            if (t[s + j].c != ws[j] || t[s + j].lab != j) {
                badinst++; return;
            }
    }
}

static long pass(const atom *t, long tn, const atom *y, long yn,
                 const atom *p, long pn, atom *out, int *iidc)
{
    long i = 0, L = 0;
    if (pn <= 0) return -1;               /* defensive: empty pattern */
    while (i < tn) {
        int ok = (i + pn <= tn);
        if (ok)
            for (long k = 0; k < pn; k++)
                if (t[i + k].c != p[k].c) { ok = 0; break; }
        if (ok) {
            if (i > 0 && t[i].iid >= 0 && t[i - 1].iid == t[i].iid)
                cutwin++;
            if (i + pn < tn && t[i + pn - 1].iid >= 0 &&
                t[i + pn].iid == t[i + pn - 1].iid)
                cutwin++;
            if (y)
                for (long k = 0; k < yn; k++) {
                    if (y[k].iid < 0) {
                        out[L].c = y[k].c; out[L].lab = -1; out[L].iid = -1;
                    } else {
                        if (k == 0 || y[k].iid != y[k - 1].iid) ++(*iidc);
                        out[L].c = y[k].c; out[L].lab = y[k].lab;
                        out[L].iid = *iidc;
                    }
                    if (++L >= MAXATOMS) return -1;
                }
            i += pn;
        } else {
            out[L] = t[i];
            if (++L >= MAXATOMS) return -1;
            i++;
        }
    }
    return L;
}

/* chain value: fidx = (R,P) per pass in RUN order (pass 0 first);
 * returns final length (*outp), or -1 capped, -2 undefined */
static long run_chain_val(const int *fidx, int npass, int F1, atom **outp,
                          int *iidc)
{
    long tn = build_form(F1, B[0], iidc);
    if (tn > MAXATOMS / 2) { capped++; return -1; }
    iidmax = *iidc;
    check_instances(B[0], tn);
    for (int s = 0; s < npass; s++) {
        int iid2 = *iidc;
        long Rn = build_form(fidx[2 * s], SCR, &iid2);
        long Pn = build_form(fidx[2 * s + 1], SCR + Rn, &iid2);
        if (Pn == 0) { undef++; return -2; }
        long L = pass(B[s], tn, Rn ? SCR : NULL, Rn, SCR + Rn, Pn,
                      B[s + 1], iidc);
        if (L < 0 || *iidc >= MAXINST - 8) { capped++; return -1; }
        iidmax = *iidc;
        tn = L;
        check_instances(B[s + 1], tn);
        if (tn > MAXATOMS / 2) { capped++; return -1; }
    }
    *outp = B[npass];
    return tn;
}

static void final_checks(const atom *t, long tn)
{
    defined++;
    lastout = t; lasttn = tn;
    long pl = 0;
    int blockok = 1;
    for (long i = 0; i < tn; i++) {
        if (t[i].lab < 0) continue;
        if (t[i].lab != (int)(pl % n)) blockok = 0;
        pl++;
    }
    if (pl % n) blockok = 0;
    if (!blockok) badprov++;
    int isfdi = (pl >= 2);
    for (long i = 0; i + 1 < tn && isfdi; i++) {
        if (t[i].lab < 0 || t[i + 1].lab < 0) continue;
        if (t[i].lab <= t[i + 1].lab) isfdi = 0;
    }
    if (isfdi) fdihits++;
    if (pl == n && n >= 2) {
        long k = 0; int isdb = 1;
        for (long i = 0; i < tn; i++) {
            if (t[i].lab < 0) continue;
            if (t[i].lab != (int)(n - 1 - k)) { isdb = 0; break; }
            k++;
        }
        if (isdb) dbhits++;
    }
    {
        long i = 0; int ok = 1;
        while (i < tn && t[i].iid < 0) i++;
        while (i < tn && ok) {
            for (int j = 0; j < n; j++, i++)
                if (i >= tn || t[i].c != ws[j]) { ok = 0; break; }
            while (i < tn && t[i].iid < 0) i++;
        }
        if (!ok) badform++;
        if (tn == n && n >= 2) {
            int isrev = 1;
            for (long k = 0; k < n; k++)
                if (t[k].c != ws[n - 1 - k]) { isrev = 0; break; }
            if (isrev) revhits++;
        }
    }
}

static void set_w(int nn)
{
    n = nn;
    for (int j = 0; j < n; j++) ws[j] = 'c' + j;
    ws[n] = 0;
}

static void emit_cross(const char *kind, const int *spec, int ns)
{
    long pl, k, sum = 0;
    if (defined % cross_every) return;
    printf("CROSS %s %d", kind, n);
    for (int i = 0; i < ns; i++) printf(" %d", spec[i]);
    printf(" |");
    pl = 0;
    for (k = 0; k < lasttn; k++) {
        if (lastout[k].lab < 0) continue;
        sum += (long)lastout[k].lab * (pl + 1);
        if (pl < 48) printf(" %d", lastout[k].lab);
        pl++;
    }
    printf(" # %ld %ld\n", pl, sum);
    crossn++;
}

static void sweep_chain(int d, const int *pp, int npp, const int *ff,
                       int nff, int lo, int hi)
{
    int fidx[8], spec[12];
    long total = 1;
    for (int i = 0; i < 2 * d; i++) total *= npp;
    for (long code = 0; code < total; code++) {
        long c = code;
        for (int i = 0; i < 2 * d; i++) { fidx[i] = pp[c % npp]; c /= npp; }
        for (int F1 = 0; F1 < nff; F1++)
            for (int nn = lo; nn <= hi; nn++) {
                set_w(nn);
                int iidc = 0;
                atom *out;
                long L = run_chain_val(fidx, d, ff[F1], &out, &iidc);
                if (L < 0) continue;
                sims++;
                final_checks(out, L);
                spec[0] = ff[F1];
                for (int i = 0; i < 2 * d; i++) spec[1 + i] = fidx[i];
                emit_cross("chain", spec, 1 + 2 * d);
            }
    }
}

/* deep slot = chain of d-1 passes; final pass [R/P]F with P or R deep */
static void sweep_deep(int d, char which, const int *pp, int npp,
                       const int *ff, int nff, int lo, int hi)
{
    static const int innerF[4] = {1, 4, 9, 16};
    int ninner = (d >= 4) ? 2 : 4;
    int fidx[8], spec[12];
    long total = 1;
    for (int i = 0; i < 2 * (d - 1); i++) total *= npp;
    for (long code = 0; code < total; code++) {
        long c = code;
        for (int i = 0; i < 2 * (d - 1); i++) { fidx[i] = pp[c % npp];
                                                c /= npp; }
        for (int ii = 0; ii < ninner; ii++)
            for (int other = 0; other < npp; other++)
                for (int F1 = 0; F1 < nff; F1++)
                    for (int nn = lo; nn <= hi; nn++) {
                        set_w(nn);
                        int iidc = 0;
                        atom *dv;
                        long dn = run_chain_val(fidx, d - 1, innerF[ii],
                                                 &dv, &iidc);
                        if (dn < 0) continue;
                        if (which == 'P' && dn == 0) { undef++; continue; }
                        atom *deep = LEFT;
                        memcpy(deep, dv, dn * sizeof(atom));
                        int iid3 = iidc;
                        long L;
                        if (which == 'P') {
                            long Rn = build_form(pp[other], SCR, &iid3);
                            memcpy(SCR + Rn, deep, dn * sizeof(atom));
                            long Fn = build_form(ff[F1], B[d + 3], &iid3);
                            iidmax = iid3;
                            L = pass(B[d + 3], Fn, Rn ? SCR : NULL, Rn,
                                     SCR + Rn, dn, B[d + 4], &iid3);
                        } else {
                            memcpy(SCR, deep, dn * sizeof(atom));
                            long Pn = build_form(pp[other], SCR + dn,
                                                 &iid3);
                            long Fn = build_form(ff[F1], B[d + 3], &iid3);
                            iidmax = iid3;
                            L = pass(B[d + 3], Fn, SCR, dn, SCR + dn, Pn,
                                     B[d + 4], &iid3);
                        }
                        if (L < 0 || iid3 >= MAXINST - 8) { capped++;
                            continue; }
                        iidmax = iid3;
                        sims++;
                        final_checks(B[d + 4], L);
                        spec[0] = ff[F1]; spec[1] = innerF[ii];
                        spec[2] = pp[other];
                        for (int i = 0; i < 2 * (d - 1); i++)
                            spec[3 + i] = fidx[i];
                        emit_cross(which == 'P' ? "deepp" : "deepr",
                                   spec, 3 + 2 * (d - 1));
                    }
    }
}

static void sweep_C(int amax, const int *pp, int npp, const int *ff,
                    int nff, int lo, int hi)
{
    int fidx[8], gidx[8];
    for (int a = 1; a <= amax - 1; a++)
        for (int b = 1; b <= amax - a; b++) {
            long ta = 1, tb = 1;
            for (int i = 0; i < 2 * a; i++) ta *= npp;
            for (int i = 0; i < 2 * b; i++) tb *= npp;
            for (long ca = 0; ca < ta; ca++) {
                long c = ca;
                for (int i = 0; i < 2 * a; i++) { fidx[i] = pp[c % npp];
                                                  c /= npp; }
                for (long cb = 0; cb < tb; cb++) {
                    long c2 = cb;
                    for (int i = 0; i < 2 * b; i++) { gidx[i] = pp[c2 % npp];
                                                      c2 /= npp; }
                    for (int F1 = 0; F1 < nff; F1++)
                        for (int F2 = 0; F2 < nff; F2++)
                            for (int nn = lo; nn <= hi; nn++) {
                                set_w(nn);
                                int iidc = 0;
                                atom *o1;
                                long L1 = run_chain_val(fidx, a, ff[F1],
                                                        &o1, &iidc);
                                if (L1 < 0) continue;
                                atom *left = LEFT;
                                memcpy(left, o1, L1 * sizeof(atom));
                                long L2 = run_chain_val(gidx, b, ff[F2],
                                                        &o1, &iidc);
                                if (L2 < 0) continue;
                                if (L1 + L2 >= MAXATOMS / 2) {
                                    capped++; continue; }
                                memcpy(left + L1, o1, L2 * sizeof(atom));
                                iidmax = iidc;
                                check_instances(left, L1 + L2);
                                sims++;
                                final_checks(left, L1 + L2);
                                {
                                    int spec[24], m = 0;
                                    spec[m++] = ff[F1];
                                    spec[m++] = ff[F2];
                                    spec[m++] = a; spec[m++] = b;
                                    for (int i = 0; i < 2 * a; i++)
                                        spec[m++] = fidx[i];
                                    for (int i = 0; i < 2 * b; i++)
                                        spec[m++] = gidx[i];
                                    emit_cross("ccomp", spec, m);
                                }
                            }
                }
            }
        }
}

int main(int argc, char **argv)
{
    int mode = (argc > 1) ? atoi(argv[1]) : 1;
    SCR = malloc(sizeof(atom) * MAXATOMS);
    LEFT = malloc(sizeof(atom) * MAXATOMS);
    for (int i = 0; i < 10; i++) B[i] = malloc(sizeof(atom) * MAXATOMS);
    if (!SCR || !LEFT || !B[0]) { fprintf(stderr, "oom\n"); return 2; }

    switch (mode) {
    case 1:
        sweep_chain(1, FULL, NFORM, FULL, NFORM, 2, 10);
        printf("[chain1 done] sims %ld\n", sims);
        sweep_chain(2, P9, 9, FULL, NFORM, 2, 8);
        printf("[chain2 done] sims %ld\n", sims);
        sweep_chain(3, P9, 9, FULL, NFORM, 2, 6);
        printf("[chain3 done] sims %ld\n", sims);
        break;
    case 2:
        sweep_chain(4, P6, 6, F12, 12, 2, 4);
        printf("[chain4 done] sims %ld\n", sims);
        break;
    case 3:
        sweep_deep(3, 'P', P9, 9, F12, 12, 2, 4);
        printf("[deepP3 done] sims %ld\n", sims);
        sweep_deep(3, 'R', P9, 9, F12, 12, 2, 4);
        printf("[deepR3 done] sims %ld\n", sims);
        break;
    case 4:
        sweep_deep(4, 'P', P6, 6, F12, 12, 2, 3);
        printf("[deepP4 done] sims %ld\n", sims);
        sweep_deep(4, 'R', P6, 6, F12, 12, 2, 3);
        printf("[deepR4 done] sims %ld\n", sims);
        break;
    case 5:
        sweep_C(2, P9, 9, FULL, NFORM, 2, 6);
        printf("[C(a+b<=2) done] sims %ld\n", sims);
        sweep_C(3, P6, 6, F8, 8, 2, 3);
        printf("[C(a+b<=3) done] sims %ld\n", sims);
        break;
    case 9: {
        /* debug: chain spec from argv: n F1 R1 P1 R2 P2 ... */
        int fidx[8], m = 0;
        n = atoi(argv[2]);
        for (int j = 0; j < n; j++) ws[j] = 'c' + j;
        ws[n] = 0;
        int F1 = atoi(argv[3]);
        for (int a = 4; a < argc && m < 8; a++) fidx[m++] = atoi(argv[a]);
        int npass = m / 2;
        int iidc = 0;
        atom *out;
        long L = run_chain_val(fidx, npass, F1, &out, &iidc);
        if (L < 0) { printf("L=%ld (capped/undef)\n", L); return 0; }
        printf("len=%ld prov:", L);
        for (long i = 0; i < L; i++)
            if (out[i].lab >= 0) printf(" %d", out[i].lab);
        printf("\ncontent: ");
        for (long i = 0; i < L; i++) putchar(out[i].c);
        printf("\n");
        return 0;
    }
    default:
        fprintf(stderr, "bad mode\n"); return 2;
    }
    printf("\n=== SEPARABLE HUNT (mode %d) SUMMARY ===\n", mode);
    printf("pipelines evaluated : %ld (undef %ld, capped %ld)\n",
           sims, undef, capped);
    printf("cut windows (instances) : %ld\n", cutwin);
    printf("split/bad instances     : %ld / %ld\n", splitinst, badinst);
    printf("bad prov block form     : %ld\n", badprov);
    printf("bad content form        : %ld\n", badform);
    printf("DB hits (n>=2)          : %ld\n", dbhits);
    printf("FDI hits (len>=2)      : %ld\n", fdihits);
    printf("rev hits                : %ld\n", revhits);
    long bad = cutwin + splitinst + badinst + badprov + badform +
               dbhits + fdihits + revhits;
    printf("TOTAL VIOLATIONS: %ld -> %s\n", bad,
           bad == 0 ? "SEPARABLE RIGIDITY CONFIRMED ON THIS DOMAIN"
                    : "FALSIFIED");
    return bad == 0 ? 0 : 1;
}
