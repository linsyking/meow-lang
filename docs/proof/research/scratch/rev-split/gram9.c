/* rev-split ROUND 9 -- FINAL: mask BOOLEAN closure (complements) +
 * modulus 6, ord_7(3) = 6 (charter: coordinator round-9 message).
 * Family D(k;3).  Round 8's engine + all its grammars, plus:
 *
 *   (1) MASK COMPLEMENTS (mneg): round 8 implemented single-residue
 *       masks (j == r mod T); the formalism's Ind predicates are
 *       closed under BOOLEANS (AIS-CLOSURE), and the p = 7 case needs
 *       the COMPLEMENT class.  Drec gains mneg: j is in the index set
 *       iff mmod==0, or ((j mod mmod)==mres) XOR mneg.
 *
 *   (2) tile7 = [b/'aaaaaaa']X: remnant Lambda_j = 3^j mod 7, PERIOD 6
 *       (ord_7(3) = 6; cycle 1,3,2,6,4,5).  Two-color profile:
 *       OF j=0..k-1: [a=Lambda_j; b=1+floor(3^{j+1}/7)]; a=Lambda_k.
 *
 *   (3) mod7 = [b/'bab']tile7: the pattern 'bab' (c_1 = 1) fires
 *       exactly at the a-runs with Lambda_j = 1, i.e. 3^j = 1 mod 7,
 *       i.e. j = 0 mod 6: FIRED SET = {j : 6 | j} cap [1..k-1] --
 *       period 6 = ord_7(3), TWO full periods at k = 13 (fires at
 *       j = 6 and j = 12).  The SURVIVING family is the COMPLEMENT
 *       class j = 0 (mod 6): ONE masked OF with mneg=1, order-
 *       preserving (single family over increasing j -- unlike a
 *       class-by-class split, which would scramble the profile
 *       order).  The b-forms branch on j mod 6 (periodic coefficient):
 *       merged (two bite-adjusted b-runs + insert) before j = 1 mod 6
 *       (j >= 7 automatically inside [2..k-1]), plain otherwise; the
 *       tail branches on k mod 6 (merged iff k = 1 mod 6).  SINGLE
 *       cell: the tree structure is k-uniform; the k mod 6 dependence
 *       lives in the periodic-coefficient forms (the other face of
 *       the formalism's per-cell x periodic-forms decomposition --
 *       mod2 demonstrates the per-cell face, mod7 the forms face).
 *       8 directives.  Grammar:
 *         a=1; b=1; a=3;
 *         OF j in [2..k-1], j !== 0 (mod 6): [b=bform(j); a=Lambda_j];
 *         b=tailb(k); a=Lambda_k
 *
 * Machine checks CONFIRM hand derivations; they do not replace them.
 * Every log's first line is the full invocation.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP      (1 << 21)
#define MAXD     12
#define NBUF     (3 * MAXD + 4)
#define NCONST   15
#define MAXRUNS  (1 << 20)

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aaa", "abb", "bab", "abba", "aaa",
     "aaabaaab", "aaaa", "aaaaaaa"};

static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci) { N[nn].t=0; N[nn].a=ci; return nn++; }
static int nv(void)   { N[nn].t=1; return nn++; }
static int nc(int a,int b){ N[nn].t=2; N[nn].a=a; N[nn].b=b; return nn++; }
static int ns(int r,int p,int f){ N[nn].t=3; N[nn].a=r; N[nn].b=p; N[nn].c=f; return nn++; }

static int eval(int e,int s,const char*w,int wl){
    Node*n=&N[e]; if(s>=MAXD) return -2; char*o=buf[s];
    if(n->t==0){int l=strlen(CONSTS[n->a]);memcpy(o,CONSTS[n->a],l);return l;}
    if(n->t==1){memcpy(o,w,wl);return wl;}
    if(n->t==2){int l1=eval(n->a,s+1,w,wl);int l2=eval(n->b,s+2,w,wl);
        if(l1<0)return l1; if(l2<0)return l2; if(l1+l2>CAP)return -2;
        memcpy(o,buf[s+1],l1); memcpy(o+l1,buf[s+2],l2); return l1+l2;}
    int lf=eval(n->c,s+1,w,wl), lp=eval(n->b,s+2,w,wl), lr=eval(n->a,s+3,w,wl);
    if(lf<0)return lf; if(lp<0)return lp; if(lr<0)return lr; if(lp==0)return -1;
    const char*T=buf[s+1],*P=buf[s+2],*A=buf[s+3];
    int tl=lf,pl=lp,al=lr,m=pl,i=0,ol=0;
    while(i<tl){ if(i+m<=tl&&memcmp(T+i,P,m)==0){ if(ol+al>CAP)return -2;
        memcpy(o+ol,A,al);ol+=al;i+=m;} else { if(ol+1>CAP)return -2; o[ol++]=T[i++];}}
    return ol;
}
static int runs_of(const char*s,int l,long long*out,long maxr){
    long n=0; long long cur=0;
    for(long i=0;i<=(long)l;i++){
        if(i<(long)l&&s[i]=='a') cur++;
        else { if(n<maxr) out[n]=cur; n++; cur=0; }
    }
    return (int)n;
}
/* ROUND 8: two-color run profile: maximal-run alternation
 * [a_0, b_0, a_1, b_1, ..., a_m]; every b_i >= 1; interior a_i >= 1;
 * a_0, a_m >= 0.  Consecutive b's are ONE b-run -- the zero a-runs
 * of the a-run-only view are absorbed into b-run VALUES. */
static int profile2(const char*s,int l,long long*out,int maxr){
    int n=0; long i=0; long long cur=0;
    while(i<(long)l && s[i]=='a'){cur++;i++;}
    if(n>=maxr) return -1; out[n++]=cur;
    while(i<(long)l){
        cur=0; while(i<(long)l && s[i]=='b'){cur++;i++;}
        if(n>=maxr) return -1; out[n++]=cur;
        cur=0; while(i<(long)l && s[i]=='a'){cur++;i++;}
        if(n>=maxr) return -1; out[n++]=cur;
    }
    return n;
}
/* weave b=1 separators into an a-run sequence (round-7 grammars:
 * their texts have all b-runs = 1 -- SELF-CHECKED in mode_gram) */
static int weave1(const long long*g,int n,long long*out){
    int m=0;
    for(int i=0;i<n;i++){ out[m++]=g[i]; if(i<n-1) out[m++]=1; }
    return m;
}
static long long pw(int B,int e){ long long r=1; for(int i=0;i<e;i++) r*=B; return r; }
static void mkwk(char*w,int*wl,int k,int B){
    *wl=0;
    for(int t=0;t<=k;t++){
        long long len = t?pw(B,t):1;
        for(long long q=0;q<len;q++) w[(*wl)++]='a';
        if(t<k) w[(*wl)++]='b';
    }
}
static long long checks, fails;
static void ck(const char*what,long long pred,long long act,const char*det){
    checks++;
    if(pred!=act){ fails++;
        if(fails<=20) printf("  FAIL %s: pred %lld act %lld [%s]\n",
                             what,pred,act,det?det:""); }
}
static void ck_eq_seq(const char*tag,int k,const long long*a,int na,
                      const long long*b,int nb){
    checks++;
    if(na!=nb||memcmp(a,b,(na<nb?na:nb)*sizeof(long long))){
        fails++;
        printf("  FAIL %s k=%d: grammar %d runs vs eval %d runs\n",
               tag,k,na,nb);
        int m = na<nb?na:nb;
        for(int i=0;i<m;i++) if(a[i]!=b[i]){
            printf("    first diff at run %d: grammar %lld eval %lld\n",
                   i,a[i],b[i]); break; }
    }
}

/* ---------- battery construction (round 7 + the two new) ---------- */
typedef struct { int e; const char*name; } Ent;
static int build_battery(Ent*Es){
    int n=0; nn=0; int X=nv();
    int mrg   = ns(nk(0), nk(2), X);
    int halv  = ns(nk(1), nk(3), X);
    int third = ns(nk(1), nk(7), X);
    int dbl   = ns(nk(3), nk(1), X);
    int shv   = ns(nk(2), nk(4), X);
    int drp   = ns(nk(0), nc(nk(1),nk(2)), X);
    int Rl    = nc(mrg, nk(2));
    int Elek  = ns(Rl, nk(2), X);
    int Eprod = ns(mrg, nk(3), X);
    int patL = nc(nk(2), nc(mrg, nk(1)));
    int Dlast= ns(nk(0), patL, nc(nc(X,mrg),nk(1)));
    int patF = nc(nc(nk(1), mrg), nk(2));
    int Dfirst=ns(nk(0), patF, nc(nc(nk(1),mrg),X));
    int Elast = ns(nk(0), nk(2), halv);
    int mrgbmrg = nc(nc(mrg,nk(2)),mrg);
    int Ecbox = ns(nk(2), nc(Elast,nk(2)), mrgbmrg);
    int Esmm  = ns(nk(0), nc(nk(2),mrg), Ecbox);
    int Eh2   = ns(nk(1), nk(3), Esmm);
    int DblM  = ns(nk(0), nk(2), dbl);
    int X1=nv(), X2=nv();
    int decb  = ns(X1, nk(2), X2);
    int thresh= ns(nk(2), nk(12), decb);   /* [b/'aaabaaab']decb */
    int tile4 = ns(nk(2), nk(13), X);     /* [b/'aaaa']X        */
    int mod2  = ns(nk(2), nk(9), tile4);   /* [b/'bab']tile4     */
    int tile7 = ns(nk(2), nk(14), X);     /* [b/'aaaaaaa']X      */
    int mod7  = ns(nk(2), nk(9), tile7);   /* [b/'bab']tile7     */
    Es[n].e=mrg;    Es[n++].name="mrg";
    Es[n].e=halv;   Es[n++].name="half";
    Es[n].e=third;  Es[n++].name="third";
    Es[n].e=dbl;    Es[n++].name="dbl";
    Es[n].e=shv;    Es[n++].name="shave";
    Es[n].e=drp;    Es[n++].name="dropab";
    Es[n].e=Elek;   Es[n++].name="Eleak";
    Es[n].e=Eprod;  Es[n++].name="Eprod";
    Es[n].e=Dlast;  Es[n++].name="dlast";
    Es[n].e=Dfirst; Es[n++].name="dfirst";
    Es[n].e=Elast;  Es[n++].name="Elast";
    Es[n].e=Ecbox;  Es[n++].name="Ecbox";
    Es[n].e=Esmm;   Es[n++].name="Esmm";
    Es[n].e=Eh2;    Es[n++].name="Eh2";
    Es[n].e=DblM;   Es[n++].name="dblmerge";
    Es[n].e=decb;   Es[n++].name="decb";
    Es[n].e=thresh; Es[n++].name="thresh";
    Es[n].e=tile4;  Es[n++].name="tile4";
    Es[n].e=mod2;   Es[n++].name="mod2";
    Es[n].e=tile7;  Es[n++].name="tile7";
    Es[n].e=mod7;   Es[n++].name="mod7";
    return n;
}

/* ---------- the formalism: directives + forms ---------- */
typedef struct Drec Drec;
struct Drec {
    int kind;          /* 0 = T, 1 = F, 2 = OF */
    int fid;            /* form id (T, F) */
    int la, lb, ha, hb; /* index set [la*k+lb .. ha*k+hb] (F, OF) */
    const Drec *body; int nbody;   /* OF body */
    int mmod, mres;    /* ROUND 8 periodic mask: j in the index set
                          iff mmod==0 or j mod mmod == mres */
    int mneg;          /* ROUND 9 complement: iff mmod>0, negate the
                          residue test (Boolean closure of Ind) */
};
/* forms: f(k, j); j = nearest enclosing family index, 0 if none */
static long long f_S      (int k,int j){ (void)j; return (pw(3,k+1)-1)/2; }
static long long f_3jpo1_2(int k,int j){ (void)k; return (pw(3,j)+1)/2; }
static long long f_3jm1  (int k,int j){ (void)k; return j? pw(3,j-1):1; }
static long long f_2_3j   (int k,int j){ (void)k; return 2*pw(3,j); }
static long long f_3jm1c (int k,int j){ (void)k; return pw(3,j)-1; }
static long long f_Sp3j  (int k,int j){ return (pw(3,k+1)-1)/2+pw(3,j); }
static long long f_3k    (int k,int j){ (void)j; return pw(3,k); }
static long long f_1     (int k,int j){ (void)k;(void)j; return 1; }
static long long f_Eprod (int k,int j){ return 1+((pw(3,j)-1)/2)*((pw(3,k+1)-1)/2); }
static long long f_3j    (int k,int j){ (void)k; return pw(3,j); }
static long long f_glue  (int k,int j){ (void)j; return pw(3,k-1)+pw(3,k); }
static long long f_Elast (int k,int j){ (void)j; return ((pw(3,k+1)-1)/2+k+1)/2; }
static long long f_Ecbox1(int k,int j){ (void)j; return ((pw(3,k+1)-1)/2-k-1)/2; }
static long long f_2S    (int k,int j){ (void)j; return 2*((pw(3,k+1)-1)/2); }
static long long f_Eh2   (int k,int j){ (void)j;
    long long L=((pw(3,k+1)-1)/2-k-1)/2; return L/2+(L&1); }
static long long f_decbJ (int k,int j){ return pw(3,k)+pw(3,j+1)+1; }
static long long f_2_3k  (int k,int j){ (void)j; return 2*pw(3,k); }
static long long f_Smk   (int k,int j){ (void)j; return (pw(3,k+1)-1)/2-k; }
static long long f_df1   (int k,int j){ (void)k;(void)j; return 1+3; }
static long long f_3k_p1 (int k,int j){ (void)j; return pw(3,k)+1; }
static long long f_3k_3cj_m2(int k,int j){ return pw(3,k)+pw(3,j+1)-2; }
/* ---- ROUND 8 forms ---- */
static long long f_c3     (int k,int j){ (void)k;(void)j; return 3; }
static long long f_Lam    (int k,int j){ (void)k; return 1+2*(j&1); }
static long long f_LamK   (int k,int j){ (void)j; return 1+2*(k&1); }
static long long f_b4nxt  (int k,int j){ (void)k;
    return 1+(pw(3,j+1)-(1+2*((j+1)&1)))/4; }
static long long f_m3     (int k,int j){ (void)k;
    return (pw(3,j-1)-(1+2*((j-1)&1)))/4 + 1 + (pw(3,j)-(1+2*(j&1)))/4; }
static long long f_bK     (int k,int j){ (void)j;
    return 1+(pw(3,k)-(1+2*(k&1)))/4; }
/* ---- ROUND 9 forms: modulus 7, ord_7(3) = 6 ---- */
static long long f_Lam7   (int k,int j){ (void)k; return pw(3,j)%7; }
static long long f_Lam7K  (int k,int j){ (void)j; return pw(3,k)%7; }
static long long f_b7nxt  (int k,int j){ (void)k;
    return 1+(pw(3,j+1)-pw(3,j+1)%7)/7; }
static long long f_b7n    (int k,int j){ (void)k;
    return 1+(pw(3,j)-pw(3,j)%7)/7; }
static long long f_m7     (int k,int j){ (void)k;
    return (pw(3,j-1)-pw(3,j-1)%7)/7 + 1 + (pw(3,j)-pw(3,j)%7)/7; }
static long long f_bf7    (int k,int j){ (void)k;
    return (j%6==1)? f_m7(k,j) : f_b7n(k,j); }
static long long f_tb7    (int k,int j){ (void)j;
    return (k%6==1)?
        ((pw(3,k-1)-pw(3,k-1)%7)/7 + 1 + (pw(3,k)-pw(3,k)%7)/7)
      : (1+(pw(3,k)-pw(3,k)%7)/7); }
static long long (*FORM[])(int,int) = {
    f_S, f_3jpo1_2, f_3jm1, f_2_3j, f_3jm1c, f_Sp3j, f_3k, f_1,
    f_Eprod, f_3j, f_glue, f_Elast, f_Ecbox1, f_2S, f_Eh2, f_decbJ,
    f_2_3k, f_Smk, f_df1, f_3k_p1, f_3k_3cj_m2,
    f_c3, f_Lam, f_LamK, f_b4nxt, f_m3, f_bK,
    f_Lam7, f_Lam7K, f_b7nxt, f_b7n, f_m7, f_bf7, f_tb7 };
enum { F_S=0, F_3JPO1_2, F_3JM1, F_2_3J, F_3JM1C, F_SP3J, F_3K, F_1,
       F_EPROD, F_3J, F_GLUE, F_ELAST, F_ECBOX1, F_2S, F_EH2, F_DECBJ,
       F_2_3K, F_SMK, F_DF1, F_3K_P1, F_3K_3CJ_M2,
       F_C3, F_LAM, F_LAMK, F_B4NXT, F_M3, F_BK,
       F_LAM7, F_LAM7K, F_B7NXT, F_B7N, F_M7, F_BF7, F_TB7 };
#define NT (sizeof FORM/sizeof FORM[0])

static long long *EV; static int EVN;
static void emitv(long long x){ if(EVN<MAXRUNS) EV[EVN++]=x; }
/* expand with ambient index `amb': the nearest enclosing family's
 * current index (0 at top level).  T sees amb; F's own loop index
 * shadows amb; OF passes its c down as the new ambient.  ROUND 8:
 * both F and OF honor the periodic mask (mmod, mres). */
static void expand2(const Drec*d,int nd,int k,int amb){
    for(int i=0;i<nd;i++){
        const Drec*D=&d[i];
        if(D->kind==0) emitv(FORM[D->fid](k,amb));
        else if(D->kind==1){
            int lo=D->la*k+D->lb, hi=D->ha*k+D->hb;
            for(int j=lo;j<=hi;j++){
                int in = !D->mmod || ((((j%D->mmod)==D->mres)?1:0)^D->mneg);
                if(!in) continue;
                emitv(FORM[D->fid](k,j));
            }
        } else {
            int lo=D->la*k+D->lb, hi=D->ha*k+D->hb;
            for(int c=lo;c<=hi;c++){
                int in = !D->mmod || ((((c%D->mmod)==D->mres)?1:0)^D->mneg);
                if(!in) continue;
                expand2(D->body,D->nbody,k,c);
            }
        }
    }
}
static void expand(const Drec*d,int nd,int k){ expand2(d,nd,k,0); }
static int dir_count(const Drec*d,int nd){
    int s=0;
    for(int i=0;i<nd;i++)
        s += 1 + (d[i].kind==2 ? dir_count(d[i].body,d[i].nbody) : 0);
    return s;
}
/* set helpers: [la*k+lb .. ha*k+hb] */
#define SETZ            0,0,0,0
#define SET_FULL        0,0,1,0
#define SET_TO_KM1      0,0,1,-1
#define SET_1_TO_KM1    0,1,1,-1
#define SET_1_TO_K      0,1,1,0
#define SET_0_TO_KM2    0,0,1,-2

/* ---------- the 17 round-7 grammars (UNCHANGED directives) ---------- */
/* mrg = [eps/'b']X: single run S */
static const Drec G_mrg[] = {
    {0, F_S, 0,0,0,0, 0,0},
};
/* half = [a/'aa']X: runs (3^j+1)/2, j=0..k */
static const Drec G_half[] = {
    {1, F_3JPO1_2, SET_FULL, 0,0},
};
/* third = [a/'aaa']X: run0 remnant 1; run j>=1: 3^{j-1} merged
 * insertions, remnant 3^j mod 3 = 0 */
static const Drec G_third[] = {
    {0, F_1,   0,0,0,0, 0,0},
    {1, F_3JM1, SET_1_TO_K, 0,0},
};
/* dbl = ['aa'/'a']X: runs 2*3^j */
static const Drec G_dbl[] = {
    {1, F_2_3J, SET_FULL, 0,0},
};
/* shave = [b/'ab']X: run j loses its last a (window with the
 * following b), j<k; last run unshaved */
static const Drec G_shave[] = {
    {1, F_3JM1C, SET_TO_KM1, 0,0},
    {0, F_3K,     0,0,0,0, 0,0},
};
/* dropab = [eps/'ab']X: each window consumes one a AND ITS b, so
 * the separators are eaten too and all material merges: ONE run,
 * value S-k. */
static const Drec G_dropab[] = {
    {0, F_SMK, 0,0,0,0, 0,0},
};
/* Eleak = [(mrg.b)/'b']X: separator j -> a^S b: run j -> S+3^j,
 * j<k; last run 3^k */
static const Drec G_Eleak[] = {
    {1, F_SP3J, SET_TO_KM1, 0,0},
    {0, F_3K,    0,0,0,0, 0,0},
};
/* Eprod = [mrg/'aa']X: remnant 1, then run j = 1+floor(3^j/2)*S */
static const Drec G_Eprod[] = {
    {0, F_1,    0,0,0,0, 0,0},
    {1, F_EPROD, SET_1_TO_K, 0,0},
};
/* dlast = [eps/(b.mrg.a)](X.mrg.a): runs 3^0..3^{k-2}, glue
 * 3^{k-1}+3^k */
static const Drec G_dlast[] = {
    {1, F_3J,   SET_0_TO_KM2, 0,0},
    {0, F_GLUE, 0,0,0,0, 0,0},
};
/* dfirst = [eps/(a.mrg.b)](a.mrg.X): [1+3, 3^2..3^k] (seam merge) */
static const Drec G_dfirst[] = {
    {0, F_DF1, 0,0,0,0, 0,0},
    {1, F_3J,  0,2,1,0, 0,0},
};
/* Elast = [eps/'b'][a/'aa']X: (S+k+1)/2 */
static const Drec G_Elast[] = {
    {0, F_ELAST, 0,0,0,0, 0,0},
};
/* Ecbox = [b/(Elast.b)](mrg.b.mrg): a^{(S-k-1)/2} b a^S */
static const Drec G_Ecbox[] = {
    {0, F_ECBOX1, 0,0,0,0, 0,0},
    {0, F_S,      0,0,0,0, 0,0},
};
/* Esmm = [eps/(b.mrg)]Ecbox = a^{(S-k-1)/2} */
static const Drec G_Esmm[] = {
    {0, F_ECBOX1, 0,0,0,0, 0,0},
};
/* Eh2 = [a/'aa']Esmm: ceil(L/2) with L=(S-k-1)/2 */
static const Drec G_Eh2[] = {
    {0, F_EH2, 0,0,0,0, 0,0},
};
/* dblmerge = [eps/'b']['aa'/'a']X: 2S */
static const Drec G_dblmerge[] = {
    {0, F_2S, 0,0,0,0, 0,0},
};
/* decb = [X/'b']X: T(2); OF over copies c=0..k-2 of
 * [F(3^j, j=1..k-1); T(3^k+3^{c+1}+1)]; F(3^j, 1..k-1); T(2*3^k). */
static const Drec G_decb_body[] = {
    {1, F_3J,    SET_1_TO_KM1, 0,0},
    {0, F_DECBJ, 0,0,0,0, 0,0},
};

/* thresh = [b/'aaabaaab']decb: the multi-b pattern (c_0=3, c_1=3,
 * c_2=0) fires at (sep0, sep1) of copy c iff the junction before
 * copy c has >= 3 a's: copy 0's head is 2 (NOT fired), copies
 * c >= 1 fire.  9 directives. */
static const Drec G_thresh_body0[] = {
    {1, F_3J,    0,1,1,-1, 0,0},
    {0, F_3K_P1, 0,0,0,0, 0,0},
};
static const Drec G_thresh_body1[] = {
    {1, F_3J,      0,2,1,-1, 0,0},
    {0, F_3K_3CJ_M2, 0,0,0,0, 0,0},
};
static const Drec G_thresh[] = {
    {0, F_2_3J, 0,0,0,0, 0,0},
    {2, 0, 0,0,0,0, G_thresh_body0, 2},
    {2, 0, 0,1,1,-2, G_thresh_body1, 2},
    {1, F_3J,   0,2,1,-1, 0,0},
    {0, F_2_3K, 0,0,0,0, 0,0},
};

/* ---------- ROUND 8 grammars: the periodic mask ---------- */
/* tile4 = [b/'aaaa']X: two-color profile:
 *   OF j=0..k-1: [a = Lambda_j; b = 1+floor(3^{j+1}/4)]; a = Lambda_k
 *   Lambda_j = 3^j mod 4 (period 2 in j).  3 directives, 2k+1 entries. */
static const Drec G_tile4_body[] = {
    {0, F_LAM,   0,0,0,0, 0,0},   /* a-run Lambda_j   */
    {0, F_B4NXT, 0,0,0,0, 0,0},   /* b-run after it   */
};
static const Drec G_tile4[] = {
    {2, 0, 0,0,1,-1, G_tile4_body, 2},
    {0, F_LAMK, 0,0,0,0, 0,0},     /* final a-run Lambda_k */
};
/* mod2 = [b/'bab']tile4: fired set = {even j in [2..k-1]} (the
 * residue class where Lambda_j = 1); surviving a-runs = j=0 plus the
 * ODD residue class; the b-run before each surviving odd j >= 3 is
 * the merge of the two bite-adjusted b-runs around the deleted
 * even j-1 window plus the inserted 'b'.  TWO CELLS (k mod 2):
 *   k odd:  [a=1; b=1; a=3; OF j odd in [3..k]: [b=merged(j); a=3]]
 *   k even: [a=1; b=1; a=3; OF j odd in [3..k-1]: [b=merged(j); a=3];
 *           b=1+floor(3^k/4); a=Lambda_k=1]
 * The OF's index set carries the PERIODIC MASK (mod 2, residue 1):
 * genuinely periodic, not an interval. */
static const Drec G_mod2_body[] = {
    {0, F_M3, 0,0,0,0, 0,0},       /* merged b-run before odd j */
    {0, F_C3, 0,0,0,0, 0,0},       /* a-run Lambda_j = 3 (odd j) */
};
static const Drec G_mod2o[] = {    /* k odd cell */
    {0, F_1, 0,0,0,0, 0,0},        /* a-run j=0: Lambda_0 = 1 */
    {0, F_1, 0,0,0,0, 0,0},        /* b-run between j=0 and j=1: 1 */
    {0, F_C3,0,0,0,0, 0,0},        /* a-run j=1: 3 */
    {2, 0, 0,3,1,0, G_mod2_body, 2, 2,1},   /* OF odd j=3..k */
};
static const Drec G_mod2e[] = {    /* k even cell */
    {0, F_1, 0,0,0,0, 0,0},
    {0, F_1, 0,0,0,0, 0,0},
    {0, F_C3,0,0,0,0, 0,0},
    {2, 0, 0,3,1,-1, G_mod2_body, 2, 2,1},  /* OF odd j=3..k-1 */
    {0, F_BK, 0,0,0,0, 0,0},       /* final b-run 1+floor(3^k/4), untouched */
    {0, F_1, 0,0,0,0, 0,0},        /* final a-run Lambda_k = 1 */
};

/* ---------- ROUND 9 grammars: modulus 6, complement mask ---------- */
/* tile7 = [b/'aaaaaaa']X: two-color profile:
 *   OF j=0..k-1: [a = Lambda_j (= 3^j mod 7, period 6);
 *                 b = 1+floor(3^{j+1}/4... /7)]; a = Lambda_k. */
static const Drec G_tile7_body[] = {
    {0, F_LAM7,  0,0,0,0, 0,0},    /* a-run Lambda_j          */
    {0, F_B7NXT, 0,0,0,0, 0,0},    /* b-run after it          */
};
static const Drec G_tile7[] = {
    {2, 0, 0,0,1,-1, G_tile7_body, 2},
    {0, F_LAM7K, 0,0,0,0, 0,0},    /* final a-run Lambda_k    */
};
/* mod7 = [b/'bab']tile7: fired set = {j : 6 | j} in [1..k-1] (period
 * ord_7(3) = 6); surviving family = the COMPLEMENT class, one
 * order-preserving masked OF with mneg = 1.  b-forms branch on
 * j mod 6 (periodic coefficient): merged before j = 1 mod 6 (the
 * class after each deleted j-1 = 0 mod 6), plain otherwise; the tail
 * branches on k mod 6.  SINGLE cell (structure k-uniform). */
static const Drec G_mod7_body[] = {
    {0, F_BF7,  0,0,0,0, 0,0},     /* b-run before a-run j     */
    {0, F_LAM7, 0,0,0,0, 0,0},     /* a-run Lambda_j            */
};
static const Drec G_mod7[] = {
    {0, F_1,    0,0,0,0, 0,0},     /* a-run j=0: Lambda_0 = 1   */
    {0, F_1,    0,0,0,0, 0,0},     /* b-run(0->1) = 1+floor(3/7) = 1 */
    {0, F_C3,   0,0,0,0, 0,0},     /* a-run j=1: Lambda_1 = 3   */
    {2, 0, 0,2,1,-1, G_mod7_body, 2, 6,0,1},  /* OF j in [2..k-1],
                                     j =/= 0 (mod 6): complement mask */
    {0, F_TB7,  0,0,0,0, 0,0},     /* tail b (merged iff k=1 mod 6) */
    {0, F_LAM7K,0,0,0,0, 0,0},     /* tail a Lambda_k             */
};

typedef struct { const char*name; const Drec*d; int nd;
                 const Drec*d2; int nd2;  /* k-even cell, if cellk */
                 int cellk;   /* 1: two cells by k parity */
                 int sep1;    /* 1: round-7 grammar: a-runs only, all
                                 b-runs are 1 (self-checked) */
               } Gram;
static Gram GRAMS[32];
static int build_grams(void){
    int n=0;
    static Drec decb_all[6];
    decb_all[0].kind=0; decb_all[0].fid=F_2_3J;   /* f_2_3j(k,0) = 2 */
    decb_all[0].la=decb_all[0].lb=decb_all[0].ha=decb_all[0].hb=0;
    decb_all[0].body=0; decb_all[0].nbody=0;
    decb_all[0].mmod=0; decb_all[0].mres=0;
    decb_all[1].kind=2; decb_all[1].fid=0;
    decb_all[1].la=0; decb_all[1].lb=0; decb_all[1].ha=1; decb_all[1].hb=-2;
    decb_all[1].body=G_decb_body; decb_all[1].nbody=2;
    decb_all[1].mmod=0; decb_all[1].mres=0;
    decb_all[2].kind=1; decb_all[2].fid=F_3J;
    decb_all[2].la=0; decb_all[2].lb=1; decb_all[2].ha=1; decb_all[2].hb=-1;
    decb_all[2].body=0; decb_all[2].nbody=0;
    decb_all[2].mmod=0; decb_all[2].mres=0;
    decb_all[3].kind=0; decb_all[3].fid=F_2_3K;
    decb_all[3].la=decb_all[3].lb=decb_all[3].ha=decb_all[3].hb=0;
    decb_all[3].body=0; decb_all[3].nbody=0;
    decb_all[3].mmod=0; decb_all[3].mres=0;
    #define REG(nm,D,ND) do{ GRAMS[n].name=nm; GRAMS[n].d=D; GRAMS[n].nd=ND; \
        GRAMS[n].d2=0; GRAMS[n].nd2=0; GRAMS[n].cellk=0; GRAMS[n].sep1=1; n++; }while(0)
    REG("mrg",      G_mrg,      1);
    REG("half",     G_half,     1);
    REG("third",    G_third,    2);
    REG("dbl",      G_dbl,      1);
    REG("shave",    G_shave,    2);
    REG("dropab",   G_dropab,   1);
    REG("Eleak",    G_Eleak,    2);
    REG("Eprod",    G_Eprod,    2);
    REG("dlast",    G_dlast,    2);
    REG("dfirst",   G_dfirst,   2);
    REG("Elast",    G_Elast,    1);
    REG("Ecbox",    G_Ecbox,    2);
    REG("Esmm",     G_Esmm,     1);
    REG("Eh2",      G_Eh2,      1);
    REG("dblmerge", G_dblmerge, 1);
    REG("decb",     decb_all,   4);
    REG("thresh",   G_thresh,   5);
    #undef REG
    GRAMS[n].name="tile4"; GRAMS[n].d=G_tile4; GRAMS[n].nd=2;
    GRAMS[n].d2=0; GRAMS[n].nd2=0; GRAMS[n].cellk=0; GRAMS[n].sep1=0; n++;
    GRAMS[n].name="mod2"; GRAMS[n].d=G_mod2o; GRAMS[n].nd=4;
    GRAMS[n].d2=G_mod2e; GRAMS[n].nd2=6; GRAMS[n].cellk=1; GRAMS[n].sep1=0; n++;
    GRAMS[n].name="tile7"; GRAMS[n].d=G_tile7; GRAMS[n].nd=2;
    GRAMS[n].d2=0; GRAMS[n].nd2=0; GRAMS[n].cellk=0; GRAMS[n].sep1=0; n++;
    GRAMS[n].name="mod7"; GRAMS[n].d=G_mod7; GRAMS[n].nd=6;
    GRAMS[n].d2=0; GRAMS[n].nd2=0; GRAMS[n].cellk=0; GRAMS[n].sep1=0; n++;
    return n;
}

static void mode_gram(int kforce){
    printf("=== [gram] ROUND 9: two-color profiles, periodic masks,"
           " complement masks (mod 6) ===\n");
    Ent Es[32]; int nE=build_battery(Es);
    int nG=build_grams();
    static char w[CAP];
    static long long rv[MAXRUNS];    /* extracted from text */
    static long long ev[MAXRUNS];    /* grammar expansion  */
    static long long wv[2*MAXRUNS];  /* sep1 weave         */
    EV = ev;
    int totbad=0;
    for(int g=0; g<nG; g++){
        int e=-1;
        for(int i=0;i<nE;i++) if(!strcmp(Es[i].name,GRAMS[g].name)) e=i;
        if(e<0){ printf("  %s: NO BATTERY ENTRY\n",GRAMS[g].name); continue; }
        int kcap=13;
        if(!strcmp(GRAMS[g].name,"Ecbox")||!strcmp(GRAMS[g].name,"Esmm")
           ||!strcmp(GRAMS[g].name,"Eh2")) kcap=8;
        if(!strcmp(GRAMS[g].name,"tile4")||!strcmp(GRAMS[g].name,"mod2")) kcap=12;
        if(!strcmp(GRAMS[g].name,"tile7")||!strcmp(GRAMS[g].name,"mod7")) kcap=13;
        int kmax=3;
        for(int k=3;k<=kcap;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            kmax=k;
        }
        if(kforce>0) kmax=kforce<kmax?kforce:kmax;
        int bad=0, explen=0;
        for(int k=3;k<=kmax;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            const Drec*dd=GRAMS[g].d; int dnd=GRAMS[g].nd;
            if(GRAMS[g].cellk && !(k&1)){ dd=GRAMS[g].d2; dnd=GRAMS[g].nd2; }
            if(GRAMS[g].sep1){
                /* (i) round-7 a-run mode: regression vs round 7 */
                int nr=runs_of(buf[0],l,rv,MAXRUNS);
                EVN=0; expand(dd,dnd,k);
                ck_eq_seq(GRAMS[g].name,k,EV,EVN,rv,nr);
                if(EVN!=nr) bad++;
                /* (ii) two-color mode: weave b=1, self-check the flag */
                int np=profile2(buf[0],l,rv,MAXRUNS);
                int allb1=1;
                for(int i=1;i<np;i+=2) if(rv[i]!=1) allb1=0;
                ck("sep1-b-runs-all-1",1,allb1,GRAMS[g].name);
                int nw=weave1(EV,EVN,wv);
                ck_eq_seq("2c",k,wv,nw,rv,np);
                if(nw!=np) bad++;
                explen=nw;
            } else {
                /* two-color grammar: expansion IS the profile */
                int np=profile2(buf[0],l,rv,MAXRUNS);
                EVN=0; expand(dd,dnd,k);
                ck_eq_seq(GRAMS[g].name,k,EV,EVN,rv,np);
                if(EVN!=np) bad++;
                explen=EVN;
                if(!strcmp(GRAMS[g].name,"mod2")){
                    /* a-runs surviving = (EVN+1)/2; tile4 had k+1:
                     * the difference is the fired set size */
                    long long fired=(k+1)-((EVN+1)/2);
                    ck("mod2-fired-count-even-j",(k-1)/2,fired,
                       "even j in [2..k-1]");
                }
                if(!strcmp(GRAMS[g].name,"mod7")){
                    /* tile7 had k+1 a-runs; fired = multiples of 6 in
                     * [1..k-1] = floor((k-1)/6) -- at k=13: TWO full
                     * periods of the mask (j=6 and j=12) */
                    long long fired=(k+1)-((EVN+1)/2);
                    ck("mod7-fired-count-6div",(k-1)/6,fired,
                       "j = 0 mod 6 in [1..k-1]");
                }
                if(k==kmax){
                    printf("    %s k=%d profile head:",GRAMS[g].name,k);
                    for(int i=0;i<np&&i<13;i++) printf(" %lld",rv[i]);
                    printf("%s\n",np>13?" ...":"");
                    if(!strcmp(GRAMS[g].name,"tile4")){
                        int nr=runs_of(buf[0],l,rv,MAXRUNS);
                        printf("    tile4 k=%d: two-color profile %d entries"
                               " vs a-run-only view %d entries"
                               " (exponential: the round-7 view cannot be"
                               " pinned by a V-fixed grammar)\n",k,np,nr);
                    }
                }
            }
        }
        int nd1=dir_count(GRAMS[g].d,GRAMS[g].nd);
        int nd2=GRAMS[g].cellk?dir_count(GRAMS[g].d2,GRAMS[g].nd2):-1;
        printf("  %-10s: %2d directives%s, k=3..%d, expansion %d entries at "
               "k=%d%s\n",GRAMS[g].name,nd1,
               GRAMS[g].cellk?" (both cells k-independent)":"",
               kmax,explen,kmax,bad?"  <-- MISMATCH":"");
        if(GRAMS[g].cellk)
            printf("    mod2 cells: k-odd %d directives, k-even %d directives"
                   " (per-cell selection by k mod 2)\n",nd1,nd2);
        totbad+=bad;
    }
    ck("grammars-all-exact",0,totbad,"hand grammar expansions");
    printf("  total: %d expressions (%d round-7 regression + tile4 + mod2"
           " + tile7 + mod7), %d with mismatches\n",nG,17,totbad);
}

/* ---------- [meas]: the INV3 measure form on the same footing ---- */
/* Hand EPT closed forms of the a-count and b-count, per cell.
 * The residue-class geometric sums are the EPT step made explicit:
 *   tile4: v_a = #(even j in [0..k]) + 3*#(odd j in [1..k])
 *          v_b = k + (sum_{j=1..k} 3^j - sum_{j=1..k} Lambda_j)/4
 *   mod2 (k=2m+1): v_a = 1+3(m+1);  v_b = 1 + 9(9^m-1)/8
 *   mod2 (k=2m):   v_a = 2+3m;      v_b = 1 + 9(9^{m-1}-1)/8
 *                                          + 1 + (3^k-1)/4
 *   decb:   v_a = (k+1)S;  v_b = k^2
 *   thresh: v_a = (k+1)S - 6(k-1);  v_b = k^2 - (k-1)   (k-1 firings) */
static void meas_closed(const char*name,int k,long long*va,long long*vb){
    long long S=(pw(3,k+1)-1)/2;
    *va=*vb=-1;
    if(!strcmp(name,"decb")){ *va=(long long)(k+1)*S; *vb=(long long)k*k; }
    else if(!strcmp(name,"thresh")){
        *va=(long long)(k+1)*S-6*(k-1); *vb=(long long)k*k-(k-1); }
    else if(!strcmp(name,"tile4")){
        int o=(k+1)/2;                     /* odd j in [1..k] */
        int e=k/2;                         /* even j in [1..k] */
        *va=(long long)(k+1-o)+3*o;
        *vb=k+((pw(3,k+1)-3)/2-(3*o+e))/4;
    } else if(!strcmp(name,"mod2")){
        int o=(k+1)/2;                     /* odd j in [1..k] */
        if(k&1){ int m=(k-1)/2;
            *va=1+3*(long long)(m+1);
            *vb=1+9*((pw(9,m)-1)/8);
        } else { int m=k/2;
            *va=2+3*(long long)m;
            *vb=1+9*((pw(9,m-1)-1)/8)+1+(pw(3,k)-1)/4;
        }
    }
}
static void mode_meas(void){
    printf("=== [meas] INV3 measure form: closed forms vs grammar sums "
           "vs text counts ===\n");
    Ent Es[32]; int nE=build_battery(Es);
    int nG=build_grams();
    static char w[CAP];
    static long long ev[MAXRUNS];
    static long long wv[2*MAXRUNS];
    EV=ev;
    const char*NAMES[]={"decb","thresh","tile4","mod2"};
    for(int q=0;q<4;q++){
        const char*nm=NAMES[q];
        int e=-1,g=-1;
        for(int i=0;i<nE;i++) if(!strcmp(Es[i].name,nm)) e=i;
        for(int i=0;i<nG;i++) if(!strcmp(GRAMS[i].name,nm)) g=i;
        if(e<0||g<0){ printf("  %s: MISSING\n",nm); continue; }
        int kcap=!strcmp(nm,"tile4")||!strcmp(nm,"mod2")?12:13;
        int kmax=3;
        for(int k=3;k<=kcap;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            kmax=k;
        }
        int bad=0;
        for(int k=3;k<=kmax;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            /* text counts */
            long long ta=0,tb=0;
            for(int i=0;i<l;i++){ if(buf[0][i]=='a') ta++; else tb++; }
            /* closed forms (per cell) */
            long long va,vb; meas_closed(nm,k,&va,&vb);
            /* grammar sums: expand, weave if sep1, sum by parity */
            const Drec*dd=GRAMS[g].d; int dnd=GRAMS[g].nd;
            if(GRAMS[g].cellk && !(k&1)){ dd=GRAMS[g].d2; dnd=GRAMS[g].nd2; }
            EVN=0; expand(dd,dnd,k);
            int nw=EVN;
            if(GRAMS[g].sep1){ nw=weave1(EV,EVN,wv); }
            else { for(int i=0;i<EVN;i++) wv[i]=EV[i]; }
            long long ga=0,gb=0;
            for(int i=0;i<nw;i+=2) ga+=wv[i];
            for(int i=1;i<nw;i+=2) gb+=wv[i];
            char det[64]; snprintf(det,sizeof det,"%s k=%d",nm,k);
            ck("meas-a-closed-vs-text",va,ta,det);
            ck("meas-b-closed-vs-text",vb,tb,det);
            ck("meas-a-grammar-vs-text",ga,ta,det);
            ck("meas-b-grammar-vs-text",gb,tb,det);
            if(va!=ta||vb!=tb||ga!=ta||gb!=tb) bad++;
        }
        printf("  %-8s: closed forms (per cell) == grammar sums == text "
               "counts, k=3..%d%s\n",nm,kmax,bad?"  <-- MISMATCH":"");
    }
}

int main(int argc,char**argv){
    clock_t t0=clock();
    const char*mode = argc>1?argv[1]:"gram";
    int kforce = argc>2?atoi(argv[2]):0;
    printf("INVOCATION:");
    for(int i=0;i<argc;i++) printf(" %s",argv[i]);
    printf("   [mode=%s kforce=%d]\n",mode,kforce);
    if(!strcmp(mode,"gram")) mode_gram(kforce);
    else if(!strcmp(mode,"meas")) mode_meas();
    else printf("unknown mode %s (gram|meas)\n",mode);
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
