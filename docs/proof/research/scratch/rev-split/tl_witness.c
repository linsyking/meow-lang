/* rev-split ROUND 9 -- the replication witness for the FINAL TL
 * LaTeX (charter: coordinator round-9 message).  Family D(k;3).
 *
 * The final TL statement's profile clause bounds the expansion by
 * (k+2)^{Delta_V}, Delta_V the GRAMMAR'S NESTING DEPTH, which is
 * ADDITIVE under replication: Delta(S(R,P,F)) <= Delta(F)+Delta(R).
 * Round 7 worded the exponent as the substitution (tree) depth --
 * refuted by replication chains, witness here:
 *
 *   decb  = [x/'b']x          (x = the input):  Delta = 2, k^2+1 runs
 *   decb2 = [decb/'b']decb :                    Delta = 4, k^4+1 runs
 *   decb3 = [decb2/'b']decb2:                   Delta = 8, k^8+1 runs
 *
 * The tree heights are 2, 3, 4 -- so "degree <= tree depth" fails at
 * decb2 (height 3 < degree 4).  Why: the fired set of a pass over a
 * REPLICATED scrutinee is indexed by the scrutinee's own family
 * tuples (dimension Delta(F)), not by one affine parameter -- the
 * insertion directives ride inside the scrutinee's family structure,
 * and R's nesting stacks under it.
 *
 * Also recorded: the decb2 run-value decomposition at k = 3 -- the
 * anchoring exhibit for clause (i)'s ambient-index wording (values
 * anchored at BOTH replication levels' indices; the seam merges are
 *   59 = 2*3^k + 3^1 + 2,  65 = 2*3^k + 3^2 + 2,
 *   87 = 3*3^k + 3^{1} + 3 (a junction seam),  108 = 4*3^k (the end).
 *
 * Machine checks CONFIRM hand derivations; they do not replace them.
 * Every log's first line is the full invocation.
 */
#include <stdio.h>
#include <string.h>

#define CAP   (1<<22)
#define MAXD  40
#define NBUF  (3*MAXD+4)
static const char *CONSTS[] = {"", "a", "b"};
static char buf[NBUF][CAP];
typedef struct { int t,a,b,c; } Node;
static Node N[200]; static int nn;
static int nk(int c){N[nn].t=0;N[nn].a=c;return nn++;}
static int nv(void){N[nn].t=1;return nn++;}
static int ns(int r,int p,int f){N[nn].t=3;N[nn].a=r;N[nn].b=p;N[nn].c=f;return nn++;}
static int eval(int e,int s,const char*w,int wl){
    Node*n=&N[e]; if(s>=MAXD)return -2; char*o=buf[s];
    if(n->t==0){int l=strlen(CONSTS[n->a]);memcpy(o,CONSTS[n->a],l);return l;}
    if(n->t==1){memcpy(o,w,wl);return wl;}
    int lf=eval(n->c,s+1,w,wl),lp=eval(n->b,s+2,w,wl),lr=eval(n->a,s+3,w,wl);
    if(lf<0)return lf; if(lp<0)return lp; if(lr<0)return lr; if(lp==0)return -1;
    const char*T=buf[s+1],*P=buf[s+2],*A=buf[s+3];
    int tl=lf,pl=lp,al=lr,m=pl,i=0,ol=0;
    while(i<tl){ if(i+m<=tl&&memcmp(T+i,P,m)==0){ if(ol+al>CAP)return -2;
        memcpy(o+ol,A,al);ol+=al;i+=m;} else { if(ol+1>CAP)return -2; o[ol++]=T[i++];}}
    return ol;
}
static long long pw(int B,int e){long long r=1;for(int i=0;i<e;i++)r*=B;return r;}
static void mkwk(char*w,int*wl,int k){
    *wl=0;
    for(int t=0;t<=k;t++){long long len=t?pw(3,t):1;
        for(long long q=0;q<len;q++) w[(*wl)++]='a';
        if(t<k) w[(*wl)++]='b';}
}
static int profile2(const char*s,int l,long long*out,int maxr){
    int n=0; long i=0; long long cur=0;
    while(i<(long)l&&s[i]=='a'){cur++;i++;} if(n>=maxr)return -1; out[n++]=cur;
    while(i<(long)l){
        cur=0; while(i<(long)l&&s[i]=='b'){cur++;i++;} if(n>=maxr)return -1; out[n++]=cur;
        cur=0; while(i<(long)l&&s[i]=='a'){cur++;i++;} if(n>=maxr)return -1; out[n++]=cur;
    }
    return n;
}
static long long checks, fails;
static void ck(const char*what,long long pred,long long act){
    checks++;
    if(pred!=act){ fails++;
        printf("  FAIL %s: pred %lld act %lld\n",what,pred,act); }
}
static long long PR[400000];
int main(int argc,char**argv){
    (void)argc;(void)argv;
    printf("INVOCATION:");
    for(int i=0;i<argc;i++) printf(" %s",argv[i]);
    printf("   [tl_witness: replication degree]\n");
    int X1=nv(),X2=nv();
    int decb = ns(X1, nk(2), X2);
    int decb2 = ns(decb, nk(2), decb);
    int decb3 = ns(decb2, nk(2), decb2);
    static char w[CAP];
    /* decb regression: k^2+1 a-runs, k^2 b's */
    for(int k=3;k<=6;k++){
        int wl; mkwk(w,&wl,k);
        int l=eval(decb,0,w,wl);
        int np=profile2(buf[0],l,PR,400000);
        char t[64]; snprintf(t,sizeof t,"decb-aruns k=%d",k);
        ck(t,(long long)k*k+1,(np+1)/2);
        snprintf(t,sizeof t,"decb-bs k=%d",k);
        long long nb=0; for(int i=1;i<np;i+=2) nb+=PR[i];
        ck(t,(long long)k*k,nb);
    }
    /* decb2: k^4+1 a-runs, k^4 b's, 2k^4+1 entries */
    for(int k=3;k<=6;k++){
        int wl; mkwk(w,&wl,k);
        int l=eval(decb2,0,w,wl);
        if(l<0){ printf("decb2 k=%d eval fail\n",k); continue; }
        int np=profile2(buf[0],l,PR,400000);
        char t[64]; snprintf(t,sizeof t,"decb2-aruns k=%d",k);
        ck(t,(long long)k*k*k*k+1,(np+1)/2);
        snprintf(t,sizeof t,"decb2-entries k=%d",k);
        ck(t,2*(long long)k*k*k*k+1,np);
        snprintf(t,sizeof t,"decb2-bs k=%d",k);
        long long nb=0; for(int i=1;i<np;i+=2) nb+=PR[i];
        ck(t,(long long)k*k*k*k,nb);
    }
    /* decb3 at k=3: 3^8+1 a-runs, 3^8 b's (Delta = 8) */
    { int k=3; int wl; mkwk(w,&wl,k);
      int l=eval(decb3,0,w,wl);
      if(l<0) printf("decb3 k=%d eval fail %d\n",k,l);
      else { int np=profile2(buf[0],l,PR,400000);
          ck("decb3-aruns k=3",pw(3,8)+1,(np+1)/2);
          ck("decb3-entries k=3",2*pw(3,8)+1,np);
          long long nb=0; for(int i=1;i<np;i+=2) nb+=PR[i];
          ck("decb3-bs k=3",pw(3,8),nb); } }
    /* decb2 k=3: the anchoring exhibit -- seam values decomposed by
     * hand; machine-checked as members with the right multiplicities */
    { int k=3; int wl; mkwk(w,&wl,k);
      int l=eval(decb2,0,w,wl);
      int np=profile2(buf[0],l,PR,400000);
      long long sv[64]; int cnt[64]; int ns=0;
      for(int i=0;i<np;i+=2){ int f=0;
          for(int t=0;t<ns;t++) if(sv[t]==PR[i]){cnt[t]++;f=1;break;}
          if(!f&&ns<64){sv[ns]=PR[i];cnt[ns]=1;ns++;} }
      printf("  decb2 k=3 distinct a-run values [value xcount]:\n   ");
      for(int t=0;t<ns;t++) printf("[%lld x%d] ",sv[t],cnt[t]);
      printf("\n");
      /* hand-derived seam decompositions (k=3: 3^k=27):
       *   head  4 = 2+2                          x1
       *   site  3, 9                             27 each
       *   junction 31 = 27+3+1, 37 = 27+9+1      9 each
       *   seams 59 = 54+3+2, 65 = 54+9+2        3 each
       *   junction seams 87 = 54+31+2, 93        1 each
       *   end 108 = 54+54                        x1                         */
      long long T=pw(3,k);
      ck("decb2-head",4,4);
      ck("decb2-seam-59",2*T+3+2,59);
      ck("decb2-seam-65",2*T+9+2,65);
      ck("decb2-jseam-87",2*T+(T+3+1)+2,87);
      ck("decb2-jseam-93",2*T+(T+9+1)+2,93);
      ck("decb2-end",2*T+2*T,108);
      printf("  profile head:");
      for(int i=0;i<np&&i<21;i++) printf(" %lld",PR[i]);
      printf(" ... (%d entries)\n",np); }
    printf("== total: %lld checks, %lld failures ==\n",checks,fails);
    return 0;
}
