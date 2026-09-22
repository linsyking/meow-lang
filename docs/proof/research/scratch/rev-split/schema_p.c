/* rev-split ROUND 2 -- Schema P residual-table battery.
 *
 * Entries under test (charter):
 *   (i)  computed replacements at anchored sites (b-skeleton),
 *   (ii) nested computed patterns on periodic regions (U^g, g const),
 *   (iii) T5 explosive tilings + their nestings (T5 on T5 on T5).
 * Plus: the P4 degree-separation specimen (CH2 -- a singular run that
 * is a PRODUCT S*(i+j-2)/2+1, not affine + S-typed), the degree
 * collapse under computed-modulus division (CH9), and the
 * jitter-pinning case (CH10, modulus S+1 on S*m+1 runs).
 *
 * Method: every chain's output (or count, via the exact per-pass
 * accounting M_out = M_F + c_w*(M_R - M_P), N_out likewise -- proved
 * in round 1) is compared against a HAND-DERIVED closed form or a
 * HAND-DERIVED transformer RULE applied to the measured previous
 * pass.  The machine only falsifies.  Caps 1<<16.  All runs < 60 s.
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

static void mkw2(char *w, int *wl, int i, int j, int k){
    *wl=0;
    for(int t=0;t<i;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<j;t++)w[(*wl)++]='a'; w[(*wl)++]='b';
    for(int t=0;t<k;t++)w[(*wl)++]='a';
}
static int cnt(const char*s,int l,char c){int x=0;for(int t=0;t<l;t++)x+=(s[t]==c);return x;}

/* ---- run iterator: maximal runs of letter c ---- */
typedef struct { int start, len; } Run;
static int runs_of(const char *s, int l, char c, Run *out, int maxr){
    int n=0, i=0;
    while(i<l && n<maxr){
        if(s[i]==c){ int st=i; while(i<l && s[i]==c) i++;
            out[n].start=st; out[n].len=i-st; n++; }
        else i++;
    }
    return n;
}

/* ============ mode t5: crafted chains ============ */

static int failures, checks;

static void expect_str(const char*name,int i,int j,int k,
                       const char*pred,int pl,const char*act,int al){
    checks++;
    if(pl!=al || memcmp(pred,act,pl)!=0){
        failures++;
        if(failures<=12){
            printf("  FAIL %s (%d,%d,%d): pred len %d act len %d\n",
                   name,i,j,k,pl,al);
            int lim=pl<al?pl:al, d=-1;
            for(int t=0;t<lim;t++) if(pred[t]!=act[t]){d=t;break;}
            if(d<0 && pl!=al) d=lim;
            if(d>=0){
                printf("    first diff at %d: pred ...", d);
                for(int t=d-4>=0?d-4:0; t<d+8 && t<pl; t++) putchar(pred[t]);
                printf(" / act ...");
                for(int t=d-4>=0?d-4:0; t<d+8 && t<al; t++) putchar(act[t]);
                putchar('\n');
            }
        }
    }
}
static void expect_int(const char*name,int i,int j,int k,long long pred,long long act){
    checks++;
    if(pred!=act){
        failures++;
        if(failures<=12)
            printf("  FAIL %s (%d,%d,%d): pred %lld act %lld\n",name,i,j,k,pred,act);
    }
}

/* CH2 rule: pattern 'bb', replacement merge=a^S, applied to text1.
 * Per maximal b-run of length L: emit a^(S*floor(L/2)) then b^(L%2);
 * everything else copied.  (T5's transformer rule, letter b.) */
static int rule_t5_bb(const char *t1, int l1, int S, char *out){
    Run R[512]; int nr = runs_of(t1, l1, 'b', R, 512);
    int pos = 0, rr = 0, ol = 0, i = 0;
    while(i < l1){
        if(rr < nr && R[rr].start == i){
            int L = R[rr].len;
            long long m = L/2;
            for(long long q=0;q<m;q++){ for(int u=0;u<S;u++) out[ol++]='a'; if(ol>CAP) return -1;}
            for(int u=0;u<L%2;u++) out[ol++]='b';
            i += L; rr++;
        } else { out[ol++]=t1[i++]; }
        if(ol>CAP) return -1;
    }
    return ol;
}

/* CH9 rule: pattern merge=a^S, replacement 'a', applied to text2.
 * Per maximal a-run of length L: fires f=floor(L/S); emit
 * 'a'^(f + L - f*S) (each fire emits one 'a'; leftover L-fS a's);
 * b-runs copied.  (Computed-modulus tiling, the telescope step.) */
static int rule_div_S(const char *t2, int l2, int S, char *out){
    Run R[512]; int nr = runs_of(t2, l2, 'a', R, 512);
    int rr=0, ol=0, i=0;
    while(i < l2){
        if(rr < nr && R[rr].start == i){
            int L = R[rr].len; long long f = L/S;
            long long emit = f + (L - f*(long long)S);
            for(long long q=0;q<emit;q++){ out[ol++]='a'; if(ol>CAP) return -1; }
            i += L; rr++;
        } else out[ol++]=t2[i++];
        if(ol>CAP) return -1;
    }
    return ol;
}

static void mode_t5(void){
    printf("=== mode t5: crafted chains vs hand-derived forms ===\n");
    /* --- build expressions (fresh node space) --- */
    nn=0; int X=nv();
    int MERGE = ns(nk(0), nk(2), X);                  /* [e/b]X = a^S      */
    int BA    = ns(nk(2), nk(1), X);                  /* [b/a]X = b^(S+2)  */
    int BBAA  = ns(nk(6), nk(3), X);                  /* [bb/aa]X          */
    int MRGB  = nc(MERGE, nk(2));                     /* a^S b             */
    int BBAMRG= ns(nk(6), nk(1), MERGE);              /* [bb/a]merge=b^2S  */
    int AAMRG = ns(nk(3), nk(1), MERGE);              /* [aa/a]merge=a^2S  */
    int PASB  = nc(nc(nk(2), MERGE), nk(2));          /* b a^S b           */
    int PAS   = nc(MERGE, nk(2));                     /* a^S b             */
    int PASAPA= nc(nc(MERGE, nk(2)), MERGE);          /* a^S b a^S         */
    int R2P2  = nc(MRGB, MRGB);                       /* (a^S b)^2         */
    int R2P3  = nc(nc(MRGB, MRGB), MRGB);             /* (a^S b)^3         */
    int SP1   = nc(MERGE, nk(1));                     /* a^(S+1)           */

    int CH1  = ns(MERGE, nk(6), BA);                  /* [mrg/bb][b/a]X    */
    int CH2  = ns(MERGE, nk(6), BBAA);                /* P4 specimen       */
    int CH3a = ns(BBAMRG, nk(2), X);
    int CH3b = ns(BBAMRG, nk(6), CH3a);
    int CH3  = ns(MERGE, nk(6), CH3b);                /* T5^3              */
    int T2B  = ns(MRGB, nk(6), BA);                    /* (a^S b)^m b^lam   */
    int CH4  = ns(nk(1), PASB,  T2B);
    int CH5  = ns(nk(1), PAS,   T2B);
    int CH6  = ns(nk(1), PASAPA,T2B);
    int CH7  = ns(nk(1), R2P2,  T2B);
    int CH8  = ns(nk(1), R2P3,  T2B);
    int CH9  = ns(nk(1), MERGE, CH2);                  /* degree collapse   */
    int CH10 = ns(nk(1), SP1,   CH2);                  /* jitter pinning    */

    /* CH1: out = a^(S*floor((S+2)/2)) b^((S+2)%2) */
    {
        int bad=0;
        for(int i=1;i<=6;i++)for(int j=1;j<=6;j++)for(int k=1;k<=6;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            int l=eval(CH1,0,w,wl); if(l<0){continue;}
            char pred[CAP]; long long m=(S+2)/2; int pl=0;
            for(long long q=0;q<m*S;q++) pred[pl++]='a';
            for(int q=0;q<(S+2)%2;q++) pred[pl++]='b';
            expect_str("CH1",i,j,k,pred,pl,buf[0],l);
        }
        printf("CH1 [merge/bb].[b/a]X quadratic exhibit: done\n");
    }
    /* CH1ctl: deliberately WRONG formula (ceil) -- must FAIL (control) */
    {
        int saved=failures; failures=0; int f0=0;
        for(int i=1;i<=4;i++)for(int j=1;j<=4;j++)for(int k=1;k<=4;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            int l=eval(CH1,0,w,wl); if(l<0) continue;
            char pred[CAP]; long long m=(S+2+1)/2; int pl=0;
            for(long long q=0;q<m*S;q++) pred[pl++]='a';
            for(int q=0;q<(S+2)%2;q++) pred[pl++]='b';
            int ok=(pl==l)&&memcmp(pred,buf[0],pl)==0; if(!ok) f0=1;
        }
        printf("CH1ctl wrong-formula control: %s\n", f0?"FLAGGED (harness works)":"NO FLAG (BAD)");
        failures=saved;
    }
    /* CH2: rule-based T5 on the measured pass-1 text; also explicit
     * verification of the P4-refuting run S*(i+j-2)/2+1 on odd cells.
     * (Evaluate text1 first, COPY it out of buf[0], then evaluate CH2.) */
    {
        for(int i=1;i<=8;i++)for(int j=1;j<=8;j++)for(int k=1;k<=8;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            int l1=eval(BBAA,0,w,wl); if(l1<0) continue;
            char t1[CAP]; memcpy(t1, buf[0], l1);
            int l2=eval(CH2,0,w,wl); if(l2<0) continue;
            char pred[CAP];
            int pl=rule_t5_bb(t1, l1, S, pred);
            if(pl<0) continue;
            expect_str("CH2",i,j,k,pred,pl,buf[0],l2);
            /* P4 specimen: on the all-odd cell, first a-run must be
             * exactly S*(i+j-2)/2 + 1 (a PRODUCT, not affine+S-typed) */
            if((i%2)&&(j%2)&&(k%2)){
                int a=0; while(a<l2 && buf[0][a]=='a') a++;
                long long f1 = (long long)S*(i+j-2)/2 + 1;
                p4_check:
                if(a>0){ expect_int("CH2-run1(P4)",i,j,k,f1,a); }
            }
        }
        printf("CH2 [merge/bb].[bb/aa]X rule + P4 run specimen: done\n");
    }
    /* CH3: closed form a^(S + 2*S^3) for ALL (i,j,k) */
    {
        for(int i=1;i<=6;i++)for(int j=1;j<=6;j++)for(int k=1;k<=6;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            long long tot=(long long)S+2*(long long)S*S*S;
            if(tot>CAP) continue;
            int l=eval(CH3,0,w,wl); if(l<0) continue;
            char pred[CAP]; int pl=0;
            for(long long q=0;q<tot;q++) pred[pl++]='a';
            expect_str("CH3",i,j,k,pred,pl,buf[0],l);
        }
        printf("CH3 T5^3 explosive nesting a^(S+2S^3): done\n");
    }
    /* CH4-CH8: count formulas via the exact accounting.
     *   c_w = (M_F - M_out)/(M_P - M_R)   (M_R=0 here, R='a')
     * text2 = (a^S b)^m b^lam, m=(S+2)/2, lam=(S+2)%2, B = m+lam b's.
     *   CH4 P=b a^S b : fires at b_1,b_3,...  c_w = ceil(m/2)
     *   CH5 P=a^S b   : fires at every copy   c_w = m
     *   CH6 P=a^S b a^S: pairs (1,2),(3,4)..  c_w = floor(m/2)
     *   CH7 P=(a^S b)^2                 :      c_w = floor(m/2)
     *   CH8 P=(a^S b)^3                 :      c_w = floor(m/3)
     */
    {
        struct { int e; const char*nm; int MP, NP; } cs[]={
            {0,"CH4",2,0},{0,"CH5",1,0},{0,"CH6",1,0},{0,"CH7",2,0},{0,"CH8",3,0}};
        cs[0].e=CH4; cs[0].NP=0; cs[1].e=CH5; cs[1].NP=0; cs[2].e=CH6; cs[2].NP=0;
        cs[3].e=CH7; cs[3].NP=0; cs[4].e=CH8; cs[4].NP=0;
        /* N_P computed per point (S-dependent); set NP=-1 to mean "S*" */
        for(int c=0;c<5;c++){
            for(int i=1;i<=6;i++)for(int j=1;j<=6;j++)for(int k=1;k<=6;k++){
                char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
                int lt=eval(T2B,0,w,wl); if(lt<0) continue;
                char t2[CAP]; memcpy(t2,buf[0],lt);
                int MF=cnt(t2,lt,'b'), NF=cnt(t2,lt,'a');
                int lo=eval(cs[c].e,0,w,wl); if(lo<0) continue;
                int MO=cnt(buf[0],lo,'b'), NO=cnt(buf[0],lo,'a');
                long long cw = (long long)(MF-MO); /* = c_w*(M_P - 0) */
                int m=(S+2)/2;
                long long pred;
                switch(c){
                    case 0: pred=m/2; break;   /* pairs t=1,3,..,m-1 */
                    case 1: pred=m; break;
                    case 2: pred=m/2; break;
                    case 3: pred=m/2; break;
                    case 4: pred=m/3; break;
                    default: pred=-1;
                }
                /* verify c_w = (MF-MO)/MP via divisibility, then totals */
                int MP=cs[c].MP;
                if(MP==0){ printf("  BAD MP\n"); return; }
                if(cw % MP){ expect_int(cs[c].nm,i,j,k,-1,cw); continue; }
                cw/=MP;
                expect_int(cs[c].nm,i,j,k,pred,cw);
                /* N_P: CH4: b a^S b -> S+? no: N_P=S ; CH5: a^S b -> S;
                 * CH6: a^S b a^S -> 2S ; CH7: 2S ; CH8: 3S */
                long long NP = (c==0||c==1)?S:(c==2?2*S:(c==3?2*S:3*S));
                long long pNO=(long long)NF + cw*(1 - NP);
                expect_int(cs[c].nm,i,j,k,pNO,NO);
            }
        }
        printf("CH4-CH8 anchored/U^g count formulas: done\n");
    }
    /* CH9: rule-based computed-modulus division on measured CH2 text */
    {
        for(int i=1;i<=8;i++)for(int j=1;j<=8;j++)for(int k=1;k<=8;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            int l2=eval(CH2,0,w,wl); if(l2<0) continue;
            char t2[CAP]; memcpy(t2,buf[0],l2);
            int l9=eval(CH9,0,w,wl); if(l9<0) continue;
            char pred[CAP];
            int pl=rule_div_S(t2, l2, S, pred);
            if(pl<0) continue;
            expect_str("CH9",i,j,k,pred,pl,buf[0],l9);
        }
        printf("CH9 [a/merge].CH2 degree collapse: done\n");
    }
    /* CH10: modulus S+1 on runs of the form S*m+1 (jitter pinning).
     * Rule per a-run of CH2-text: m=(L-1)/S if L==S*m+1 else floor(L/(S+1));
     * c = (m==0?0 : m==1?1 : m-1) -- the -1 jitter is PINNED by the
     * comparison m>=2, itself pinned on cells. Verify via accounting. */
    {
        for(int i=1;i<=8;i++)for(int j=1;j<=8;j++)for(int k=1;k<=8;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k); int S=i+j+k;
            int l2=eval(CH2,0,w,wl); if(l2<0) continue;
            char t2[CAP]; memcpy(t2,buf[0],l2);
            int NF=cnt(t2,l2,'a'), MF=cnt(t2,l2,'b');
            int lo=eval(CH10,0,w,wl); if(lo<0) continue;
            int NO=cnt(buf[0],lo,'a'), MO=cnt(buf[0],lo,'b');
            /* M unchanged (both a-free pattern/replacement): sanity */
            if(MO!=MF){ expect_int("CH10-M",i,j,k,MF,MO); continue; }
            long long cw=(long long)(NF-NO);  /* = c_w*((S+1)-1) = c_w*S */
            if(S==0) continue;
            if(cw % S){ expect_int("CH10",i,j,k,-1,cw); continue; }
            cw/=S;
            /* predicted: sum over a-runs of rule */
            Run Rr[512]; int nr=runs_of(t2,l2,'a',Rr,512); long long pc=0;
            for(int q=0;q<nr;q++){
                int L=Rr[q].len; long long m,c;
                if(L>=1 && (L-1)%S==0) m=(L-1)/S; else m=-1;
                if(m==0) c=0; else if(m==1) c=1;
                else if(m>1) c=m-1; else c=L/(S+1);
                pc+=c;
            }
            expect_int("CH10",i,j,k,pc,cw);
        }
        printf("CH10 modulus-(S+1) jitter pinning: done\n");
    }
    printf("mode t5: %d checks, %d failures\n",checks,failures);
}

/* ============ mode cells: random chains, within-cell test ============ */

static int POOL[12], npool;

static int gen(int depth){
    if(depth<=0) return ri(2)?nk(ri(NCONST)):nv();
    int r=ri(100);
    if(r<8) return nk(ri(NCONST));
    if(r<12) return nv();
    if(r<30){int a=gen(depth-1);int b=gen(depth-1);return nc(a,b);}
    /* S-node, biased to the residual strata */
    int rr,pp,ff;
    int q=ri(100);
    if(q<35) rr=POOL[ri(npool)]; else rr=gen(depth-1);
    q=ri(100);
    if(q<50) pp=nk(ri(NCONST));
    else if(q<75) pp=POOL[ri(npool)];
    else pp=gen(depth-1);
    q=ri(100);
    if(q<25) ff=POOL[ri(npool)]; else ff=gen(depth-1);
    return ns(rr,pp,ff);
}

#define NR 8
static int Nv[NR+1][NR+1][NR+1], Mv[NR+1][NR+1][NR+1], Dv[NR+1][NR+1][NR+1];

static int cutdiff(int i,int j,int k,int i2,int j2,int k2){
    int S=i+j+k, S2=i2+j2+k2; if(S!=S2) return 0;
    if((i>=j)!=(i2>=j2)) return 1;
    if((i>=k)!=(i2>=k2)) return 1;
    if((j>=k)!=(j2>=k2)) return 1;
    if((2*i>=S)!=(2*i2>=S2)) return 1;
    if((2*j>=S)!=(2*j2>=S2)) return 1;
    if((2*k>=S)!=(2*k2>=S2)) return 1;
    if((3*i>=S)!=(3*i2>=S2)) return 1;
    if((3*j>=S)!=(3*j2>=S2)) return 1;
    if((3*k>=S)!=(3*k2>=S2)) return 1;
    if((i>=2*j)!=(i2>=2*j2)) return 1;
    if((j>=2*i)!=(j2>=2*i2)) return 1;
    if((i>=2*k)!=(i2>=2*k2)) return 1;
    if((k>=2*i)!=(k2>=2*i2)) return 1;
    if((j>=2*k)!=(j2>=2*k2)) return 1;
    if((k>=2*j)!=(k2>=2*j2)) return 1;
    if((4*i>=S)!=(4*i2>=S2)) return 1;
    if((4*j>=S)!=(4*j2>=S2)) return 1;
    if((4*k>=S)!=(4*k2>=S2)) return 1;
    if((i>=S/2+1)!=(i2>=S2/2+1)) return 1;
    /* coincidence EQUALITY cuts (run polynomials meeting) */
    if((j==k)!=(j2==k2)) return 1;
    if((i==k)!=(i2==k2)) return 1;
    if((i==j)!=(i2==j2)) return 1;
    if((2*i==S)!=(2*i2==S2)) return 1;
    if((2*j==S)!=(2*j2==S2)) return 1;
    if((2*k==S)!=(2*k2==S2)) return 1;
    if((i+j==k)!=(i2+j2==k2)) return 1;
    if((i+k==j)!=(i2+k2==j2)) return 1;
    if((j+k==i)!=(j2+k2==i2)) return 1;
    if((3*i==S)!=(3*i2==S2)) return 1;
    if((3*j==S)!=(3*j2==S2)) return 1;
    if((3*k==S)!=(3*k2==S2)) return 1;
    if((i==2*j)!=(i2==2*j2)) return 1;
    if((i==2*k)!=(i2==2*k2)) return 1;
    if((k==2*j)!=(k2==2*j2)) return 1;
    if((j==2*i)!=(j2==2*i2)) return 1;
    if((k==2*i)!=(k2==2*i2)) return 1;
    if((j==2*k)!=(j2==2*k2)) return 1;
    /* small thresholds (junction availability) */
    if((i>=2)!=(i2>=2)) return 1;
    if((j>=2)!=(j2>=2)) return 1;
    if((k>=2)!=(k2>=2)) return 1;
    if((i>=3)!=(i2>=3)) return 1;
    if((j>=3)!=(j2>=3)) return 1;
    if((k>=3)!=(k2>=3)) return 1;
    return 0;
}

static void mode_cells(uint64_t seed, int nexpr){
    printf("=== mode cells: random chains, within-(S,residue) equality ===\n");
    rs=seed;
    long long tot_cells=0, viol_m1=0, viol_all=0, unexplained=0;
    int ncomputed=0;
    for(int t=0;t<nexpr;t++){
        nn=0; int X=nv();
        int MERGE = ns(nk(0), nk(2), X);
        int BA    = ns(nk(2), nk(1), X);
        int MRGB  = nc(MERGE, nk(2));
        int BBAMRG= ns(nk(6), nk(1), MERGE);
        int AAMRG = ns(nk(3), nk(1), MERGE);
        POOL[0]=X; POOL[1]=MERGE; POOL[2]=BA; POOL[3]=MRGB;
        POOL[4]=BBAMRG; POOL[5]=AAMRG; POOL[6]=nc(X,X); POOL[7]=nc(MERGE,MERGE);
        POOL[8]=ns(nk(1),nk(3),X); POOL[9]=ns(nk(2),nk(4),X);
        POOL[10]=ns(nk(0),nk(4),X); POOL[11]=ns(nk(1),nk(1),X);
        npool=12;
        int e=gen(4);
        int nd=0;
        for(int i=1;i<=NR;i++)for(int j=1;j<=NR;j++)for(int k=1;k<=NR;k++){
            char w[64]; int wl; mkw2(w,&wl,i,j,k);
            int l=eval(e,0,w,wl);
            if(l<0){ Dv[i][j][k]=0; continue; }
            Dv[i][j][k]=1; Nv[i][j][k]=cnt(buf[0],l,'a'); Mv[i][j][k]=cnt(buf[0],l,'b');
            nd++;
        }
        if(nd<50) continue;
        ncomputed++;
        /* within-cell equality for m in 1,2,3,4,6 */
        for(int m=1;m<=6;m++){
            if(m==5) continue;
            for(int S=3;S<=3*NR;S++){
                for(int a=0;a<m;a++)for(int b=0;b<m;b++){
                    int f=-1,fN=-1, fi=0,fj=0,fk=0, cnt2=0;
                    for(int i=1;i<=NR;i++)for(int j=1;j<=NR;j++){
                        int k=S-i-j; if(k<1||k>NR) continue;
                        if(i%m!=a||j%m!=b) continue;
                        if(!Dv[i][j][k]) continue;
                        cnt2++;
                        if(f<0){f=Nv[i][j][k]; fi=i;fj=j;fk=k;}
                        else if(Nv[i][j][k]!=f){
                            if(m==1) viol_m1++;
                            else {
                                viol_all++;
                                if(unexplained<8 && !cutdiff(fi,fj,fk,i,j,k)){
                                    unexplained++;
                                    printf("  UNEXPL m=%d S=%d r=(%d,%d): (%d,%d,%d)N=%d vs (%d,%d,%d)N=%d\n",
                                           m,S,a,b,fi,fj,fk,f,i,j,k,Nv[i][j][k]);
                                } else if(unexplained<8 && viol_all<=3 && m>1){
                                    printf("  (cut-explained) m=%d S=%d: (%d,%d,%d) vs (%d,%d,%d)\n",
                                           m,S,fi,fj,fk,i,j,k);
                                }
                            }
                            /* keep first value; count one violation per cell */
                            fN=1; (void)fN;
                        }
                    }
                    if(cnt2>=2) tot_cells++;
                }
            }
        }
    }
    printf("mode cells: %d exprs computed; cells tested %lld; viol(m=1) %lld; viol(m>1) %lld; unexplained %lld\n",
           ncomputed,tot_cells,viol_m1,viol_all,unexplained);
}

int main(int argc,char**argv){
    clock_t t0=clock();
    const char*mode = argc>1?argv[1]:"t5";
    if(!strcmp(mode,"t5")) mode_t5();
    else if(!strcmp(mode,"cells")){
        uint64_t seed = argc>2?strtoull(argv[2],0,10):777111ULL;
        int nx = argc>3?atoi(argv[3]):1000;
        mode_cells(seed,nx);
    } else printf("modes: t5 | cells [seed nexpr]\n");
    printf("elapsed %.1fs\n",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
