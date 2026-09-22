/* rev-split ROUND 3 -- THE TELESCOPE AT VARYING k (charter
 * CHARTER_varying_k.md).  Machine battery for the four theory items:
 *
 *  [SD]  Site-Distinctness: on scrutinees whose POSITIVE runs are
 *        pairwise distinct, a pattern with >= 2 b's and at least one
 *        POSITIVE interior run fires at most once.  Controls: 'bb'-type
 *        (no positive interior) and q<=1 patterns fire many times.
 *  [OPS] k-ADAPTIVE ROOM: D_last = [e/(b.mrg.a)](X.mrg.a) drops the
 *        LAST separator (merges last two runs) for EVERY k; D_first
 *        = [e/(a.mrg.b)](a.mrg.X) drops the FIRST; the junction
 *        shave [e/ab] and the halver [a/aa] act at all sites.
 *        Verified against closed forms, k = 1..8, incl. zero runs.
 *  [CEN] CENSUS SPREAD: the halver's a-count at FIXED (S_a, k) takes
 *        Theta(k) distinct values (the parity census), so totals are
 *        NOT functions of (S_a, k) -- the multivariate telescope
 *        degenerates to the residue-vector level.
 *  [FP]  FINAL-PASS CONSTRAINT: if the output is rev(w) (distinct
 *        positive runs) and the top pass fired t >= 2 times, R(w) has
 *        <= 1 b.  Checks: (a) any pass firing t>=2 with a multi-b,
 *        positive-interior R emits a string with a REPEATED interior
 *        profile (two disjoint copies) -- never rev on such w;
 *        (b) Lane C's k=2 engine: top pass fires exactly t=1.
 *
 * Falsify/verify only; every run < 60 s.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP      (1 << 16)
#define MAXD     24
#define NBUF     (3 * MAXD + 4)
#define NCONST   12

static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};

static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci) { N[nn].t=0; N[nn].a=ci; return nn++; }
static int nv(void)   { N[nn].t=1; return nn++; }
static int nc(int a,int b) { N[nn].t=2; N[nn].a=a; N[nn].b=b; return nn++; }
static int ns(int r,int p,int f) { N[nn].t=3; N[nn].a=r; N[nn].b=p; N[nn].c=f; return nn++; }

static uint64_t rs;
static uint32_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (uint32_t)(rs>>32); }
static int ri(int n){ return (int)(rnd()%(uint64_t)n); }

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

/* greedy window count of pat in txt (leftmost, non-overlapping) */
static int wincount(const char*T,int tl,const char*P,int pl){
    int m=pl,i=0,c=0;
    while(i<tl){ if(i+m<=tl&&memcmp(T+i,P,m)==0){c++;i+=m;} else i++; }
    return c;
}
/* occurrences (possibly overlapping) of sub in s */
static int occ(const char*s,int sl,const char*sub,int subl){
    int c=0;
    for(int i=0;i+subl<=sl;i++) if(!memcmp(s+i,sub,subl)) c++;
    return c;
}
static void mkw(char*w,int*wl,const int*r,int k){
    *wl=0;
    for(int t=0;t<=k;t++){
        for(int q=0;q<r[t];q++) w[(*wl)++]='a';
        if(t<k) w[(*wl)++]='b';
    }
}
static int runs_of(const char*s,int l,int*out,int maxr){
    int n=0,cur=0;
    for(int i=0;i<=l;i++){
        if(i<l&&s[i]=='a') cur++;
        else { if(n<maxr) out[n]=cur; n++; cur=0; }
    }
    return n;   /* includes outer runs; zeros allowed */
}
static int distinct_pos(const int*r,int n){
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++)
        if(r[i]>0 && r[i]==r[j]) return 0;
    return 1;
}
static void rev(char*o,const char*s,int l){ for(int i=0;i<l;i++) o[i]=s[l-1-i]; o[l]=0; }

static long long checks, fails;
static void ck(const char*what,long long pred,long long act,
               const char*detail){
    checks++;
    if(pred!=act){ fails++;
        if(fails<=15) printf("  FAIL %s: pred %lld act %lld  [%s]\n",
                             what,pred,act,detail?detail:"");
    }
}

/* ---------- [SD] site distinctness ---------- */
static void mode_sd(uint64_t seed,int trials){
    printf("=== [SD] site distinctness on distinct-run inputs ===\n");
    rs=seed;
    nn=0; int X=nv();
    int MERGE = ns(nk(0), nk(2), X);
    int DBL   = ns(nk(3), nk(1), X);            /* [aa/a]X: runs doubled */
    int SHV   = ns(nk(4), nk(2), X);            /* [ab/b]X: runs+1 */
    /* patterns: constants + COMPUTED multi-b ones with positive
     * interiors: 'ab'X (q=k+1), 'b''a'X (q=k+1), DBL (q=k), SHV (q=k) */
    int PATC = nc(nk(4), X);
    int PATD = nc(nk(2), nc(nk(1), X));
    int pats[10]={nk(9),nk(10),nk(7),nk(8),nk(4),nk(11),
                  PATC,PATD,DBL,SHV};
    int nviol=0, nmany=0, nq2=0, nctrl=0;
    for(int t=0;t<trials;t++){
        int k=2+ri(6);
        int r[16];
        for(int i=0;i<=k;i++) r[i]=1+ri(29);
        /* force pairwise distinct positive runs */
        for(int i=0;i<=k;i++) for(int j=0;j<i;j++)
            if(r[i]==r[j]) r[i]+=1+ri(3);
        char w[512]; int wl; mkw(w,&wl,r,k);
        /* scrutinee: X, DBL, SHV, MERGE, or C(X,X) (negative ctl) */
        int scr[5]; scr[0]=X; scr[1]=DBL; scr[2]=SHV;
        scr[3]=MERGE; scr[4]=nc(X,X);
        int sc = scr[ri(5)];
        int lf=eval(sc,0,w,wl); if(lf<0) continue;
        char F[CAP]; memcpy(F,buf[0],lf);
        int fr[64]; int fn=runs_of(F,lf,fr,64);
        int dist=distinct_pos(fr,fn);
        int pi=pats[ri(10)];
        int lp=eval(pi,0,w,wl); if(lp<0) continue;
        char P[2048]; memcpy(P,buf[0],lp);
        int pb=0; for(int i=0;i<lp;i++) pb+=(P[i]=='b');
        /* posint: some a-run strictly inside P (b-bounded) with len>=1 */
        int posint=0;
        { int i=0;
          while(i<lp){
            if(P[i]=='a'){ int st=i; while(i<lp&&P[i]=='a') i++;
                if(st>0&&i<lp&&i-st>=1) posint=1;
            } else i++;
          }
        }
        int c=wincount(F,lf,P,lp);
        char det[160];
        if(pb>=2&&posint){
            nq2++;
            if(dist){ if(c>1){nviol++;
                snprintf(det,sizeof det,"k=%d pat=%.12s c=%d",k,P,c);
                ck("SD",1,c<=1?1:0,det);} }
            /* if !dist (e.g. C(X,X)) lemma silent: no check */
        } else {
            nctrl++;
            if(c>1) nmany++;
        }
    }
    printf("  q>=2 positive-interior patterns on distinct scrutinees: "
           "%d cases, violations %d\n",nq2,nviol);
    printf("  controls (q<=1 or zero-interior): %d cases, %d fired >1\n",
           nctrl,nmany);
    ck("SD-total",0,nviol,"");
}

/* ---------- [OPS] k-adaptive room ---------- */
static void mode_ops(void){
    printf("=== [OPS] k-adaptive separator ops, closed forms ===\n");
    nn=0; int X=nv();
    int MERGE = ns(nk(0), nk(2), X);                 /* a^{S_a} */
    int patL  = nc(nk(2), nc(MERGE, nk(1)));        /* b . mrg . a */
    int scrL  = nc(nc(X, MERGE), nk(1));            /* X . mrg . a */
    int Dlast = ns(nk(0), patL, scrL);              /* drop LAST sep */
    int patF  = nc(nc(nk(1), MERGE), nk(2));         /* a . mrg . b */
    int scrF  = nc(nc(nk(1), MERGE), X);            /* a . mrg . X */
    int Dfirst= ns(nk(0), patF, scrF);              /* drop FIRST sep */
    int SHAVE = ns(nk(2), nk(4), X);                /* [b/ab]X: shave */
    int DROPAB= ns(nk(0), nk(4), X);                /* [e/ab]X: merge-shave */
    int HALF  = ns(nk(1), nk(3), X);                /* [a/aa]X */

    for(int k=1;k<=8;k++){
        /* grid over runs 0..3 (with at least one b): all vectors */
        int R[9]; long long tot=0;
        int nx=1; for(int t=0;t<=k;t++) nx*=4;
        for(int v=0;v<nx;v++){
            int vv=v; int Sa=0;
            for(int t=0;t<=k;t++){ R[t]=vv%4; vv/=4; Sa+=R[t]; }
            char w[256]; int wl; mkw(w,&wl,R,k);
            char det[64]; snprintf(det,sizeof det,"k=%d",k);

            /* Dlast = a^{r0} b ... b a^{r_{k-1}+r_k} (k>=1) */
            int l=eval(Dlast,0,w,wl); if(l<0) continue;
            {   char pred[512]; int pl=0;
                for(int t=0;t<k;t++){
                    for(int q=0;q<(t<k-1?R[t]:R[t]);q++) pred[pl++]='a';
                    if(t<k-1) pred[pl++]='b';
                }
                /* rebuild properly: runs r_0..r_{k-2} then merged
                   r_{k-1}+r_k, separators between, k-1 of them */
                pl=0;
                for(int t=0;t<=k-1;t++){
                    int len = (t==k-1)? R[k-1]+R[k] : R[t];
                    for(int q=0;q<len;q++) pred[pl++]='a';
                    if(t<k-1) pred[pl++]='b';
                }
                ck("Dlast", (long long)pl==l &&
                    !memcmp(pred,buf[0],pl), 1, det);
                (void)0;
            }
            /* Dfirst = a^{r0+r1} b a^{r2} ... a^{rk} */
            l=eval(Dfirst,0,w,wl); if(l<0) continue;
            {   char pred[512]; int pl=0;
                int len0 = R[0]+R[1];
                for(int q=0;q<len0;q++) pred[pl++]='a';
                for(int t=1;t<k;t++){ pred[pl++]='b';
                    for(int q=0;q<R[t+1];q++) pred[pl++]='a'; }
                ck("Dfirst", (long long)pl==l &&
                    !memcmp(pred,buf[0],pl), 1, det);
            }
            /* SHAVE [b/ab]: skeleton-preserving, one a off each
             * pre-b run that has one to give */
            l=eval(SHAVE,0,w,wl); if(l<0) continue;
            {   char pred[512]; int pl=0;
                for(int t=0;t<=k;t++){
                    int len = (t<k && R[t]>0)? R[t]-1 : R[t];
                    for(int q=0;q<len;q++) pred[pl++]='a';
                    if(t<k) pred[pl++]='b';
                }
                ck("SHAVE", (long long)pl==l &&
                    !memcmp(pred,buf[0],pl), 1, det);
            }
            /* DROPAB [e/ab]: fires at each junction t<k with r_t>=1,
             * consuming one a AND that separator; b's survive exactly
             * at zero-run junctions */
            l=eval(DROPAB,0,w,wl); if(l<0) continue;
            {   char pred[512]; int pl=0;
                for(int t=0;t<=k;t++){
                    int len = (t<k && R[t]>0)? R[t]-1 : R[t];
                    for(int q=0;q<len;q++) pred[pl++]='a';
                    if(t<k && R[t]==0) pred[pl++]='b';
                }
                ck("DROPAB", (long long)pl==l &&
                    !memcmp(pred,buf[0],pl), 1, det);
            }
            /* HALF [a/aa]: ceil-halve each run */
            l=eval(HALF,0,w,wl); if(l<0) continue;
            {   char pred[512]; int pl=0;
                for(int t=0;t<=k;t++){
                    int len=(R[t]+1)/2;
                    for(int q=0;q<len;q++) pred[pl++]='a';
                    if(t<k) pred[pl++]='b';
                }
                ck("HALF", (long long)pl==l &&
                    !memcmp(pred,buf[0],pl), 1, det);
            }
            tot++;
        }
        printf("  k=%d: %lld vectors checked\n",k,tot);
    }
}

/* ---------- [CEN] census spread ---------- */
static int HALF_E, CEN_K, CEN_SA;
static int seen[64];              /* distinct N values (offset) */
static int cen_fails;
static void comp_rec(int t,int rem,int*parts){
    if(t==CEN_K){
        parts[t]=rem;
        char w[256]; int wl; mkw(w,&wl,parts,CEN_K);
        int l=eval(HALF_E,0,w,wl);
        if(l<0) return;
        int c=0; for(int q=0;q<l;q++) c+=(buf[0][q]=='a');
        int nu=0; for(int q=0;q<=CEN_K;q++) nu+=(parts[q]&1);
        /* closed form: N = (S_a + #odd)/2, N's parity class fixed */
        if(2*c != CEN_SA+nu){ cen_fails++; }
        seen[c]=1;
        return;
    }
    for(int x=0;x<=rem;x++){ parts[t]=x; comp_rec(t+1,rem-x,parts); }
}
static void mode_census(void){
    printf("=== [CEN] halver census spread at fixed (S_a,k) ===\n");
    nn=0; int X=nv();
    int MERGE = ns(nk(0), nk(2), X);
    HALF_E = ns(nk(1), nk(3), X);
    (void)MERGE;
    for(int k=1;k<=7;k++){
        CEN_K=k;
        CEN_SA = 2*(k+1)+3;               /* odd, >= k+1 */
        int parts[9];
        for(int i=0;i<64;i++) seen[i]=0;
        cen_fails=0;
        comp_rec(0,CEN_SA,parts);
        int dv=0; for(int i=0;i<64;i++) dv+=seen[i];
        /* expected distinct values: nu in [0,k+1], nu = S_a mod 2 */
        int exp=0; for(int nu=0;nu<=k+1;nu++) if(nu%2==CEN_SA%2) exp++;
        printf("  k=%d S_a=%d: halver takes %d distinct a-counts "
               "(expected %d by parity census)\n",k,CEN_SA,dv,exp);
        ck("CEN-closedform",0,cen_fails,"N=(Sa+#odd)/2");
        ck("CEN-spread",exp,dv,"#values = parity count");
    }
}

/* ---------- [FP] final-pass constraint ---------- */
static void mode_fp(uint64_t seed,int trials){
    printf("=== [FP] final-pass constraint ===\n");
    rs=seed;
    nn=0; int X=nv();
    int MERGE = ns(nk(0), nk(2), X);
    /* (a) forced multi-firing with multi-b positive-interior R:
     *     F = [b/a]X = b^{S_a+k}, pattern 'bb' fires t>=2 times,
     *     R = C(MERGE,X) = a^{S_a} w  (k b's, positive interiors).
     *     Output contains w's exact profile t times: a repeated
     *     interior profile -- never rev on distinct positive runs. */
    int BA = ns(nk(2), nk(1), X);                   /* [b/a]X = b^{S_a+k} */
    int Rbig = nc(MERGE, X);                         /* a^{S_a} w */
    int TOP  = ns(Rbig, nk(6), BA);                 /* [Rbig/'bb']BA */
    int nrep=0, nchk=0;
    for(int t=0;t<trials;t++){
        int k=1+ri(6);
        int r[16];
        for(int i=0;i<=k;i++) r[i]=1+ri(8);
        for(int i=0;i<=k;i++) for(int j=0;j<i;j++)
            if(r[i]==r[j]) r[i]+=1+ri(3);
        char w[512]; int wl; mkw(w,&wl,r,k);
        char rw[512]; rev(rw,w,wl);
        /* direct t: greedy 'bb' windows on F's own text */
        int lf=eval(BA,0,w,wl); if(lf<0) continue;
        char F[CAP]; memcpy(F,buf[0],lf);
        int tF=wincount(F,lf,"bb",2);
        int l=eval(TOP,0,w,wl); if(l<0) continue;
        if(tF>=2){
            nchk++;
            int neq = !(l==(int)strlen(rw)) || memcmp(buf[0],rw,l);
            ck("FP-notrev",1,neq?1:0,"multi-b R multi-fire");
            /* repeated interior: X's profile (k b's, distinct runs)
             * occurs >= 2 times in output */
            int occw = occ(buf[0],l,w,wl);
            ck("FP-repeated-profile",1,occw>=2?1:0,"X twice");
            nrep += (occw>=2);
        }
    }
    printf("  multi-b multi-fire cases: %d (all != rev, %d with X twice)\n",
           nchk,nrep);
    /* (b) Lane C engine top pass fires t=1 (k=2) */
    {
        int patP1 = nc(nk(2), nc(MERGE, nk(1)));
        int scrP1 = nc(nc(X, MERGE), nk(1));
        int E_P1 = ns(nk(0), patP1, scrP1);
        int patP2 = nc(nc(nk(1), MERGE), nk(2));
        int scrP2 = nc(nc(nk(1), MERGE), X);
        int E_P2 = ns(nk(0), patP2, scrP2);
        int box = nc(nc(MERGE, nk(2)), MERGE);
        int Cc = ns(nk(2), E_P2, box);
        int Bb = ns(nk(2), E_P1, box);
        int T2 = nc(nc(Cc, nk(1)), Bb);
        int patF = nc(nc(nk(1), MERGE), nk(2));
        int Erev = ns(nk(2), patF, T2);
        int tok=0,tt1=0,tne=0;
        for(int i=0;i<=6;i++)for(int j=0;j<=6;j++)for(int kk=0;kk<=6;kk++){
            char w[64]; int wl;
            int r[3]={i,j,kk}; mkw(w,&wl,r,2);
            char rw[64]; rev(rw,w,wl);
            int l=eval(Erev,0,w,wl); if(l<0) continue;
            if(!(l==(int)strlen(rw) && !memcmp(buf[0],rw,l))) continue;
            tok++;
            /* direct t: greedy windows of patF in T2's text */
            int lt=eval(T2,0,w,wl); if(lt<0) continue;
            char Tt[CAP]; memcpy(Tt,buf[0],lt);
            int lp=eval(patF,0,w,wl); if(lp<0) continue;
            char Pt[64]; memcpy(Pt,buf[0],lp);
            int tw=wincount(Tt,lt,Pt,lp);
            if(tw==1) tt1++; else tne++;
        }
        printf("  Lane C engine (k=2): %d correct reversals, top pass "
               "t=1 on %d, t!=1 on %d\n",tok,tt1,tne);
        ck("FP-lanec",0,tne,"");
    }
}

/* ---------- [SB] separation budget (merge-free regime) ----------
 * Labeled evaluator: every a-character carries the index of the input
 * run it traces to (-1 for constants).  merge-free := every maximal
 * a-run of every value has at most ONE distinct input label.
 * Phi'(V) = # distinct pairs (i,i+1) with a separation whose left
 * run has label i+1 and right run label i  (reversed separation).
 * THEOREM (hand): merge-free  =>  Phi'(V) <= 2*#S + 2*#C.
 * Machine check: random expressions, random distinct-run inputs. */
#define SBCAP 8192
static char  sb_s[NBUF][SBCAP];
static int   sb_l[NBUF][SBCAP];
static int   mf[4000];            /* per-node merge-free flag */

static int evalL(int e,int s,const char*w,int wl,const int*rlab){
    Node*n=&N[e]; if(s>=MAXD) return -2;
    char*o=sb_s[s]; int*ol=sb_l[s];
    if(n->t==0){int l=strlen(CONSTS[n->a]);memcpy(o,CONSTS[n->a],l);
        for(int i=0;i<l;i++)ol[i]=-1; return l;}
    if(n->t==1){memcpy(o,w,wl);for(int i=0;i<wl;i++)ol[i]=rlab[i];return wl;}
    if(n->t==2){int l1=evalL(n->a,s+1,w,wl,rlab);
        int l2=evalL(n->b,s+2,w,wl,rlab);
        if(l1<0)return l1; if(l2<0)return l2; if(l1+l2>SBCAP)return -2;
        memcpy(o,sb_s[s+1],l1); memcpy(o+l1,sb_s[s+2],l2);
        memcpy(ol,sb_l[s+1],l1*sizeof(int));
        memcpy(ol+l1,sb_l[s+2],l2*sizeof(int));
        return l1+l2;}
    int lf=evalL(n->c,s+1,w,wl,rlab), lp=evalL(n->b,s+2,w,wl,rlab),
        lr=evalL(n->a,s+3,w,wl,rlab);
    if(lf<0)return lf; if(lp<0)return lp; if(lr<0)return lr;
    if(lp==0)return -1;
    const char*T=sb_s[s+1],*P=sb_s[s+2],*A=sb_s[s+3];
    const int*TL=sb_l[s+1],*AL=sb_l[s+3];
    int tl=lf,pl=lp,al=lr,m=pl,i=0,oln=0;
    while(i<tl){
        if(i+m<=tl&&memcmp(T+i,P,m)==0){
            if(oln+al>SBCAP)return -2;
            memcpy(o+oln,A,al); memcpy(ol+oln,AL,al*sizeof(int));
            oln+=al; i+=m;
        } else { if(oln+1>SBCAP)return -2;
            o[oln]=T[i]; ol[oln]=TL[i]; oln++; i++; }
    }
    return oln;
}

/* per-node merge-free flag: scan a value's runs for 2+ input labels */
static int run_mf(const char*s,const int*lab,int l){
    int i=0, seen=-2;
    while(i<=l){
        if(i<l&&s[i]=='a'){
            if(lab[i]>=0){
                if(seen>=0&&seen!=lab[i]) return 0;
                seen=lab[i];
            }
            i++;
        } else { seen=-2; i++; }
    }
    return 1;
}
/* Phi' from string+labels; pairs array size >= k+2 */
static int phi_prime(const char*s,const int*lab,int l,int k,
                    unsigned char*pairset){
    for(int i=0;i<k+2;i++) pairset[i]=0;
    for(int p=0;p<l;p++){
        if(s[p]!='b') continue;
        int a=p-1,b=p+1;
        if(a<0||s[a]!='a') continue;
        if(b>=l||s[b]!='a') continue;
        while(a>=0&&s[a]=='a')a--;
        while(b<l&&s[b]=='a')b++;
        for(int u=p-1;u>a;u--){ if(lab[u]<0) continue;
            for(int v=p+1;v<b;v++){ if(lab[v]<0) continue;
                if(lab[v]==lab[u]-1) pairset[lab[v]]=1; } }
    }
    int c=0; for(int i=0;i<k+2;i++) c+=pairset[i];
    return c;
}
static int gen_expr(int d){
    if(d<=0){ return ri(2)? nv() : nk(ri(7)); }
    int t=ri(12);
    if(t<2) return nv();
    if(t<4) return nk(ri(7));
    if(t<8) return nc(gen_expr(d-1),gen_expr(d-1));
    return ns(gen_expr(d-1),gen_expr(d-1),gen_expr(d-1));
}
static void count_nodes(int e,int*ns_,int*nc_){
    Node*n=&N[e];
    if(n->t==3){(*ns_)++;count_nodes(n->a,ns_,nc_);
        count_nodes(n->b,ns_,nc_);count_nodes(n->c,ns_,nc_);}
    else if(n->t==2){(*nc_)++;count_nodes(n->a,ns_,nc_);
        count_nodes(n->b,ns_,nc_);}
}
static void mode_sb(uint64_t seed,int trials){
    printf("=== [SB] separation budget, merge-free regime ===\n");
    rs=seed;
    long long nmf=0, okmf=0, polluted=0;
    unsigned char pairset[64];
    for(int t=0;t<trials;t++){
        nn=0;
        int E=gen_expr(3+ri(2));
        int k=1+ri(5);
        int r[8]; int rlab[256];
        for(int i=0;i<=k;i++) r[i]=1+ri(3);
        for(int i=0;i<=k;i++) for(int j=0;j<i;j++)
            if(r[i]==r[j]) r[i]+=1+ri(2);
        char w[256]; int wl; mkw(w,&wl,r,k);
        { int pos=0;
          for(int i=0;i<=k;i++){ for(int q=0;q<r[i];q++) rlab[pos++]=i;
              if(i<k) rlab[pos++]= -1; } }
        int l=evalL(E,0,w,wl,rlab);
        if(l<0) continue;
        /* sanity on first trial: Phi'(rev(w)) = k exactly */
        if(t==0){
            char rw[256]; int rlabr[256];
            for(int i=0;i<wl;i++){ rw[i]=w[wl-1-i]; rlabr[i]=rlab[wl-1-i]; }
            ck("SB-rev-phi",k,phi_prime(rw,rlabr,wl,k,pairset),"Phi'(rev)=k");
        }
        /* merge-free := EVERY subtree value's runs have <= 1 distinct
         * input label; re-evaluate each subtree into slot 0 */
        int mfok=1;
        int stack[256],sp=0; stack[sp++]=E;
        while(sp>0 && mfok){
            int e=stack[--sp];
            Node*n=&N[e];
            if(n->t==2){stack[sp++]=n->a;stack[sp++]=n->b;}
            else if(n->t==3){stack[sp++]=n->a;stack[sp++]=n->b;
                stack[sp++]=n->c;}
            else continue;
            int ll=evalL(e,0,w,wl,rlab);
            if(ll<0) continue;
            if(!run_mf(sb_s[0],sb_l[0],ll)) mfok=0;
        }
        l=evalL(E,0,w,wl,rlab); if(l<0) continue;
        int phi=phi_prime(sb_s[0],sb_l[0],l,k,pairset);
        int nS=0,nC=0; count_nodes(E,&nS,&nC);
        int budget=2*nS+2*nC;
        if(mfok){ nmf++;
            if(phi<=budget) okmf++;
            else ck("SB-budget",(long long)budget,(long long)phi,
                   "merge-free violation");
        } else if(phi>budget) polluted++;
    }
    printf("  merge-free derivations: %lld, budget held: %lld; "
           "mergey with Phi'>budget: %lld\n",nmf,okmf,polluted);
    /* pollution witness: E_poll = [(merge.b)/'aa']merge.
     * One pass: pattern 'aa' on merge = a^{S_a}; each firing inserts
     * R = a^{S_a} b.  Every junction separation sits between merged
     * runs carrying ALL labels -> every pair (i,i+1) reversed:
     * Phi' = k >> budget = 2*2+2*1 = 6.  Documents that the budget
     * theorem NEEDS merge-freeness. */
    {
        nn=0; int X=nv();
        int MG1 = ns(nk(0), nk(2), X);   /* two separate merges: the
            budget counts the UNFOLDED tree (#S=3, #C=1, budget 8) */
        int MG2 = ns(nk(0), nk(2), X);
        int Rp = nc(MG1, nk(2));
        int Ep = ns(Rp, nk(3), MG2);
        for(int k=9;k<=10;k++){
            int r[16]; int rlab[512];
            for(int i=0;i<=k;i++) r[i]=1+i;
            char w[512]; int wl; mkw(w,&wl,r,k);
            { int pos=0;
              for(int i=0;i<=k;i++){ for(int q=0;q<r[i];q++)
                  rlab[pos++]=i; if(i<k) rlab[pos++]=-1; } }
            int l=evalL(Ep,0,w,wl,rlab);
            if(l<0){ ck("POLLUT-eval",1,0,"overflow"); continue; }
            int phi=phi_prime(sb_s[0],sb_l[0],l,k,pairset);
            int nS=0,nC=0; count_nodes(Ep,&nS,&nC);
            int budget=2*nS+2*nC;
            printf("  POLLUTION WITNESS k=%d: Phi'=%d budget=%d "
                   "(merge-free would cap at budget)\n",k,phi,budget);
            ck("POLLUT-phi",k,phi,"Phi'(E_poll)=k");
            ck("POLLUT-over",1,phi>budget?1:0,"witness exceeds budget");
        }
    }
}

int main(int argc,char**argv){
    clock_t t0=clock();
    const char*m = argc>1?argv[1]:"all";
    uint64_t seed = argc>2?strtoull(argv[2],0,10):314159ULL;
    int tr = argc>3?atoi(argv[3]):400;
    if(!strcmp(m,"sd")) mode_sd(seed,tr);
    else if(!strcmp(m,"ops")) mode_ops();
    else if(!strcmp(m,"census")) mode_census();
    else if(!strcmp(m,"fp")) mode_fp(seed,tr);
    else if(!strcmp(m,"sb")) mode_sb(seed,tr);
    else {
        mode_sd(seed,tr);
        mode_ops();
        mode_census();
        mode_fp(seed,tr);
        mode_sb(seed,tr);
    }
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
