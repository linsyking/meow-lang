#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define CAP (1<<16)
#define MAXD 24
#define NBUF (3*MAXD+4)
#define NCONST 12
static char buf[NBUF][CAP];
static const char *CONSTS[NCONST] =
    {"", "a", "b", "aa", "ab", "ba", "bb", "aab", "abb", "bab", "abba", "aaa"};
typedef struct { int t, a, b, c; } Node;
static Node N[4000]; static int nn;
static int nk(int ci) { N[nn].t=0; N[nn].a=ci; return nn++; }
static int nv(void)   { N[nn].t=1; return nn++; }
static int nc(int a, int b) { N[nn].t=2; N[nn].a=a; N[nn].b=b; return nn++; }
static int ns(int r, int p, int f) { N[nn].t=3; N[nn].a=r; N[nn].b=p; N[nn].c=f; return nn++; }
static uint64_t rs;
static uint32_t rnd(void) { rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (uint32_t)(rs>>32); }
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }
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
    if(depth<=0) return ri(2) ? nk(ri(NCONST)) : nv();
    int r=ri(100);
    if(r<15) return nk(ri(NCONST));
    if(r<25) return nv();
    if(r<55){int a=gen(depth-1);int b=gen(depth-1);return nc(a,b);}
    int rr=gen(depth-1),pp=gen(depth-1),ff=gen(depth-1);
    return ns(rr,pp,ff);
}
static void ppn(int e){
    Node*n=&N[e];
    if(n->t==0){printf("\"%s\"",CONSTS[n->a]);return;}
    if(n->t==1){printf("X");return;}
    if(n->t==2){printf("C(");ppn(n->a);printf(",");ppn(n->b);printf(")");return;}
    printf("S(");ppn(n->a);printf(",");ppn(n->b);printf(",");ppn(n->c);printf(")");
}
int main(){
    rs=424242424242ULL;
    for(int t=0;t<=455;t++){
        nn=0; int X=nv(); int e=gen(4);
        int i0a=12+ri(30), j0a=12+ri(30), i0b=12+ri(30), j0b=12+ri(30);
        if(t==455){
            printf("expr idx 455: "); ppn(e); printf("\n"); printf("bases: (%d,%d) (%d,%d)\n", i0a,j0a,i0b,j0b);
            /* fine grid around (35,12): a-content table */
            printf("g(i,j) for i=30..40, j=8..16:\n");
            printf("     ");
            for(int j=8;j<=16;j++) printf("%6d",j);
            printf("\n");
            for(int i=30;i<=40;i++){
                printf("%3d: ",i);
                for(int j=8;j<=16;j++){
                    char w[128]; int wl=0;
                    for(int z=0;z<i;z++)w[wl++]='a'; w[wl++]='b';
                    for(int z=0;z<j;z++)w[wl++]='a';
                    int l=eval(e,0,w,wl);
                    if(l<0) printf("%6s","-");
                    else { int c=0; for(int z=0;z<l;z++)c+=(buf[0][z]=='a'); printf("%6d",c); }
                }
                printf("\n");
            }
            /* anti-diagonal traces S=44..50: values along each */
            for(int S=44;S<=50;S+=2){
                printf("S=%2d:",S);
                for(int i=2;i<S-1;i++){
                    char w[128]; int wl=0;
                    for(int z=0;z<i;z++)w[wl++]='a'; w[wl++]='b';
                    for(int z=0;z<S-i;z++)w[wl++]='a';
                    int l=eval(e,0,w,wl);
                    if(l<0){printf(" -");continue;}
                    int c=0; for(int z=0;z<l;z++)c+=(buf[0][z]=='a');
                    printf(" %d",c);
                }
                printf("\n");
            }
        }
    }
    return 0;
}
