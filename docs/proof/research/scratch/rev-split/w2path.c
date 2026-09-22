#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define CAP (1<<16)
#define MAXD 24
#define NBUF (3*MAXD+4)
#define NCONST 12
static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};
static char buf[NBUF][CAP];
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci){N[nn].t=0;N[nn].a=ci;return nn++;}
static int nv(void){N[nn].t=1;return nn++;}
static int nc(int a,int b){N[nn].t=2;N[nn].a=a;N[nn].b=b;return nn++;}
static int ns(int r,int p,int f){N[nn].t=3;N[nn].a=r;N[nn].b=p;N[nn].c=f;return nn++;}
static uint64_t rs;
static uint32_t rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return (uint32_t)(rs>>32);}
static int ri(int n){return (int)(rnd()%(uint64_t)n);}
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
static int gen(int depth){
    if(depth<=0) return ri(2)?nk(ri(NCONST)):nv();
    int r=ri(100);
    if(r<15) return nk(ri(NCONST));
    if(r<25) return nv();
    if(r<55){int a=gen(depth-1);int b=gen(depth-1);return nc(a,b);}
    int rr=gen(depth-1),pp=gen(depth-1),ff=gen(depth-1);
    return ns(rr,pp,ff);
}
static int g2(int e,int i,int j,int k){
    char w[192]; int wl=0;
    for(int t=0;t<i;t++)w[wl++]='a'; w[wl++]='b';
    for(int t=0;t<j;t++)w[wl++]='a'; w[wl++]='b';
    for(int t=0;t<k;t++)w[wl++]='a';
    int l=eval(e,0,w,wl); if(l<0) return -1000000;
    int c=0; for(int t=0;t<l;t++)c+=(buf[0][t]=='a'); return c;
}
int main(int argc,char**argv){
    long target=atol(argv[1]);
    rs=24681357ULL;
    int e=-1;
    for(long t=0;t<=target;t++){
        nn=0; int X=nv(); e=gen(4);
    }
    /* path test: slice S=27, fix k, walk i; and slice S=27 fix j walk i */
    for(int S=21;S<=27;S+=6){
        printf("slice S=%d, k=1, i=1..S-2 (j=S-1-i):\n  ",S);
        for(int i=1;i<=S-2;i++){
            int g=g2(e,i,S-1-i,1);
            printf("%4d",g);
        }
        printf("\n  ramp? (strictly increasing would be split-like)\n");
        int inc=1, nd=0, prev=-1;
        for(int i=1;i<=S-2;i++){
            int g=g2(e,i,S-1-i,1);
            if(g==-1000000) continue;
            nd++;
            if(prev>=0 && g<=prev) inc=0;
            prev=g;
        }
        printf("  distinct values on path: ");
        prev=-999999; { int cnt=0;
        for(int i=1;i<=S-2;i++){int g=g2(e,i,S-1-i,1); if(g==-1000000)continue;
            int d=0; /* recompute set */ d=0;
            for(int i2=1;i2<i;i2++){int h=g2(e,i2,S-1-i2,1); if(h==g){d=1;break;}}
            if(!d)cnt++;}
        printf("%d ; strictly-increasing: %s\n",cnt,inc?"YES (VIOLATION)":"no"); }
    }
    /* also a fixed-j walk on a bigger slice for more resolution */
    int S=33;
    printf("slice S=%d, k=2, i=1..S-3:\n  ",S);
    for(int i=1;i<=S-3;i++) printf("%4d",g2(e,i,S-2-i,2));
    printf("\n");
    return 0;
}
