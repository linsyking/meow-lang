/* rev-split ROUND 7 -- INV4 TO LINE-BY-LINE: machine confirmation.
 * (charter CHARTER_inv4.md).  Family D(k;3).
 *
 * The round-7 formalism, EXECUTABLE: a pinned profile grammar is a
 * V-fixed DIRECTIVE TREE.  Directives:
 *   T(fid)          emit one run with value FORM[fid](k, j)
 *   F(fid, [a..b])  emit |[a..b]| runs, j = a..b (affine bounds in k)
 *   OF(body, [a..b]) instantiate the directive list `body' for each
 *                    outer index c = a..b; forms inside the body see
 *                    the NEAREST enclosing family index (shadowing),
 *                    so a T inside an OF sees the outer index c.
 * Directive count = tree size: V-FIXED, k-independent by construction.
 * Expansion length = Theta(k^{nesting depth}) -- the reconciliation:
 * decb = 6 directives, Theta(k^2) runs.  Replication scales
 * expansion, never grammar size.
 *
 * [gram] mode: for each battery expression, the hand-written grammar
 * (the round-7 derivations, from round-5 verified closed forms) is
 * expanded and compared EXACTLY (values AND length) with the
 * evaluator's run sequence at k = 3..kmax.  Machine checks CONFIRM
 * hand derivations; they do not replace them.
 *
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
#define NCONST   13
#define MAXRUNS  (1 << 20)

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aaa", "abb", "bab", "abba", "aaa",
     "aaabaaab"};

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
        if(na==nb){
            for(int i=0;i<na;i++) if(a[i]!=b[i]){
                printf("    first diff at run %d: grammar %lld eval %lld\n",
                       i,a[i],b[i]); break; }
        } else {
            int m = na<nb?na:nb;
            for(int i=0;i<m;i++) if(a[i]!=b[i]){
                printf("    first diff at run %d: grammar %lld eval %lld\n",
                       i,a[i],b[i]); break; }
        }
    }
}

/* ---------- battery construction (identical to round 6) ---------- */
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
    return n;
}

/* ---------- the round-7 formalism: directives + forms ---------- */
typedef struct Drec Drec;
struct Drec {
    int kind;          /* 0 = T, 1 = F, 2 = OF */
    int fid;            /* form id (T, F) */
    int la, lb, ha, hb; /* index set [la*k+lb .. ha*k+hb] (F, OF) */
    const Drec *body; int nbody;   /* OF body */
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
static long long (*FORM[])(int,int) = {
    f_S, f_3jpo1_2, f_3jm1, f_2_3j, f_3jm1c, f_Sp3j, f_3k, f_1,
    f_Eprod, f_3j, f_glue, f_Elast, f_Ecbox1, f_2S, f_Eh2, f_decbJ,
    f_2_3k, f_Smk, f_df1, f_3k_p1, f_3k_3cj_m2 };
enum { F_S=0, F_3JPO1_2, F_3JM1, F_2_3J, F_3JM1C, F_SP3J, F_3K, F_1,
       F_EPROD, F_3J, F_GLUE, F_ELAST, F_ECBOX1, F_2S, F_EH2, F_DECBJ,
       F_2_3K, F_SMK, F_DF1, F_3K_P1, F_3K_3CJ_M2 };
#define NT (sizeof FORM/sizeof FORM[0])

static long long *EV; static int EVN;
static void emitv(long long x){ if(EVN<MAXRUNS) EV[EVN++]=x; }
/* expand with ambient index `amb': the nearest enclosing family's
 * current index (0 at top level).  T sees amb; F's own loop index
 * shadows amb; OF passes its c down as the new ambient. */
static void expand2(const Drec*d,int nd,int k,int amb){
    for(int i=0;i<nd;i++){
        const Drec*D=&d[i];
        if(D->kind==0) emitv(FORM[D->fid](k,amb));
        else if(D->kind==1){
            int lo=D->la*k+D->lb, hi=D->ha*k+D->hb;
            for(int j=lo;j<=hi;j++) emitv(FORM[D->fid](k,j));
        } else {
            int lo=D->la*k+D->lb, hi=D->ha*k+D->hb;
            for(int c=lo;c<=hi;c++) expand2(D->body,D->nbody,k,c);
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

/* ---------- the 16 hand grammars (round-7 derivations) ---------- */
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
 * value S-k.  (Round-5 verified form; my first round-7 grammar
 * wrongly kept the separators -- the machine caught it.) */
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
 * 3^{k-1}+3^k (last separator + S+1 trailing a's removed) */
static const Drec G_dlast[] = {
    {1, F_3J,   SET_0_TO_KM2, 0,0},
    {0, F_GLUE, 0,0,0,0, 0,0},
};
/* dfirst = [eps/(a.mrg.b)](a.mrg.X): window a^{S+1}b at the head;
 * leftover head a^1 SEAM-MERGES with run 1 (a^3): [1+3, 3^2..3^k]
 * (my first grammar forgot the seam merge -- the machine caught it) */
static const Drec G_dfirst[] = {
    {0, F_DF1, 0,0,0,0, 0,0},
    {1, F_3J,  0,2,1,0, 0,0},
};
/* Elast = [eps/'b'][a/'aa']X: half's runs merge: (S+k+1)/2 */
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
 * [F(3^j, j=1..k-1); T(3^k+3^{c+1}+1)]; F(3^j, 1..k-1); T(2*3^k).
 * The junction is the round-7 corrected formula: copy c's tail
 * (3^k) + site run c+1 (3^{c+1}) + copy c+1's head (1); the head
 * entry 2 = site 0 + copy 0's head; the final 2*3^k = copy (k-1)'s
 * tail + final site run.  6 directives, Theta(k^2) expansion. */
static const Drec G_decb_body[] = {
    {1, F_3J,    SET_1_TO_KM1, 0,0},
    {0, F_DECBJ, 0,0,0,0, 0,0},
};

/* thresh = [b/'aaabaaab']decb: the multi-b pattern (c_0=3, c_1=3,
 * c_2=0) fires at (sep0, sep1) of copy c iff the junction before
 * copy c has >= 3 a's: copy 0's head is 2 (NOT fired), copies
 * c >= 1 fire (junction 3^k+3^c+1).  This exercises the S-i
 * production concretely: interior families MASKED (copy c's
 * interior loses its j=1 run exactly when c >= 1 -- realized by
 * the SPLIT device: two OFs), junction forms BITE-ADJUSTED (every
 * junction after copy c is bitten by copy c+1's window: -3), and
 * the unbitten head boundary case.  9 directives.
 * Window at copy c: [last 3 a's of the junction before copy c]
 * + sep0 + [the j=1 run, 3 a's] + sep1  ->  'b'. */
static const Drec G_thresh_body0[] = {
    {1, F_3J,    0,1,1,-1, 0,0},      /* interior [1..k-1] (copy 0) */
    {0, F_3K_P1, 0,0,0,0, 0,0},      /* junction after copy 0, bitten */
};
static const Drec G_thresh_body1[] = {
    {1, F_3J,      0,2,1,-1, 0,0},   /* interior [2..k-1] (masked) */
    {0, F_3K_3CJ_M2, 0,0,0,0, 0,0}, /* junction after copy c, bitten */
};
static const Drec G_thresh[] = {
    {0, F_2_3J, 0,0,0,0, 0,0},                     /* T(2): head, NOT bitten */
    {2, 0, 0,0,0,0, G_thresh_body0, 2},             /* OF c=0 */
    {2, 0, 0,1,1,-2, G_thresh_body1, 2},            /* OF c=1..k-2 */
    {1, F_3J,   0,2,1,-1, 0,0},                    /* copy k-1 interior [2..k-1] */
    {0, F_2_3K, 0,0,0,0, 0,0},                     /* final 2*3^k, NOT bitten */
};

typedef struct { const char*name; const Drec*d; int nd; } Gram;
static Gram GRAMS[32];
static int build_grams(void){
    int n=0;
    static Drec decb_all[6];
    decb_all[0].kind=0; decb_all[0].fid=F_2_3J;
    decb_all[0].la=decb_all[0].lb=decb_all[0].ha=decb_all[0].hb=0;
    decb_all[0].body=0; decb_all[0].nbody=0;
    /* T(2) = 2*3^0: use a tiny dedicated entry via F_2_3J with j=0 */
    decb_all[0].fid = F_2_3J;             /* f_2_3j(k,0) = 2 */
    decb_all[1].kind=2; decb_all[1].fid=0;
    decb_all[1].la=0; decb_all[1].lb=0; decb_all[1].ha=1; decb_all[1].hb=-2;
    decb_all[1].body=G_decb_body; decb_all[1].nbody=2;
    decb_all[2].kind=1; decb_all[2].fid=F_3J;
    decb_all[2].la=0; decb_all[2].lb=1; decb_all[2].ha=1; decb_all[2].hb=-1;
    decb_all[2].body=0; decb_all[2].nbody=0;
    decb_all[3].kind=0; decb_all[3].fid=F_2_3K;
    decb_all[3].la=decb_all[3].lb=decb_all[3].ha=decb_all[3].hb=0;
    decb_all[3].body=0; decb_all[3].nbody=0;
    GRAMS[n].name="mrg";      GRAMS[n].d=G_mrg;      GRAMS[n++].nd=1;
    GRAMS[n].name="half";    GRAMS[n].d=G_half;     GRAMS[n++].nd=1;
    GRAMS[n].name="third";   GRAMS[n].d=G_third;    GRAMS[n++].nd=2;
    GRAMS[n].name="dbl";     GRAMS[n].d=G_dbl;      GRAMS[n++].nd=1;
    GRAMS[n].name="shave";   GRAMS[n].d=G_shave;    GRAMS[n++].nd=2;
    GRAMS[n].name="dropab";  GRAMS[n].d=G_dropab;   GRAMS[n++].nd=1;
    GRAMS[n].name="Eleak";   GRAMS[n].d=G_Eleak;    GRAMS[n++].nd=2;
    GRAMS[n].name="Eprod";   GRAMS[n].d=G_Eprod;    GRAMS[n++].nd=2;
    GRAMS[n].name="dlast";   GRAMS[n].d=G_dlast;    GRAMS[n++].nd=2;
    GRAMS[n].name="dfirst";  GRAMS[n].d=G_dfirst;   GRAMS[n++].nd=2;
    GRAMS[n].name="Elast";   GRAMS[n].d=G_Elast;    GRAMS[n++].nd=1;
    GRAMS[n].name="Ecbox";   GRAMS[n].d=G_Ecbox;    GRAMS[n++].nd=2;
    GRAMS[n].name="Esmm";    GRAMS[n].d=G_Esmm;     GRAMS[n++].nd=1;
    GRAMS[n].name="Eh2";     GRAMS[n].d=G_Eh2;      GRAMS[n++].nd=1;
    GRAMS[n].name="dblmerge";GRAMS[n].d=G_dblmerge; GRAMS[n++].nd=1;
    GRAMS[n].name="decb";    GRAMS[n].d=decb_all;   GRAMS[n++].nd=4;
    GRAMS[n].name="thresh";  GRAMS[n].d=G_thresh;   GRAMS[n++].nd=5;
    return n;
}

static void mode_gram(int kforce){
    printf("=== [gram] INV4 line-by-line: hand grammars vs evaluator ===\n");
    Ent Es[32]; int nE=build_battery(Es);
    int nG=build_grams();
    static char w[CAP];
    static long long rv[MAXRUNS];
    EV = rv;
    int totbad=0;
    for(int g=0; g<nG; g++){
        /* find the battery entry with this name (same order) */
        int e=-1;
        for(int i=0;i<nE;i++) if(!strcmp(Es[i].name,GRAMS[g].name)) e=i;
        if(e<0){ printf("  %s: NO BATTERY ENTRY\n",GRAMS[g].name); continue; }
        int kcap=13;
        if(!strcmp(GRAMS[g].name,"Ecbox")||!strcmp(GRAMS[g].name,"Esmm")
           ||!strcmp(GRAMS[g].name,"Eh2")) kcap=8;
        int kmax=3;
        for(int k=3;k<=kcap;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            kmax=k;
        }
        if(kforce>0) kmax=kforce<kmax?kforce:kmax;
        int ndir=dir_count(GRAMS[g].d,GRAMS[g].nd);
        int bad=0, explen=0;
        for(int k=3;k<=kmax;k++){
            int wl; mkwk(w,&wl,k,3);
            int l=eval(Es[e].e,0,w,wl);
            if(l<0) break;
            int nr=runs_of(buf[0],l,rv,MAXRUNS);
            EVN=0;
            expand(GRAMS[g].d,GRAMS[g].nd,k);
            ck_eq_seq(GRAMS[g].name,k,EV,EVN,rv,nr);
            if(EVN!=nr) bad++;
            explen=EVN;
        }
        printf("  %-10s: %2d directives, k=3..%d, expansion %d runs at "
               "k=%d%s\n",GRAMS[g].name,ndir,kmax,explen,kmax,
               bad?"  <-- MISMATCH":"");
        totbad+=bad;
    }
    ck("grammars-all-exact",0,totbad,"hand grammar expansions");
    printf("  total: %d expressions, %d with mismatches; directive "
           "counts are k-independent by construction\n",nG,totbad);
}

int main(int argc,char**argv){
    clock_t t0=clock();
    const char*mode = argc>1?argv[1]:"gram";
    int kforce = argc>2?atoi(argv[2]):0;
    printf("INVOCATION:");
    for(int i=0;i<argc;i++) printf(" %s",argv[i]);
    printf("   [mode=%s kforce=%d]\n",mode,kforce);
    if(!strcmp(mode,"gram")) mode_gram(kforce);
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
