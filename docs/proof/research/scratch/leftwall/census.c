/* census.c -- leftwall round 1: census over constant-pattern pipelines.
 *
 * All censuses share the pass space: pattern B, replacement A over {a,b},
 * lengths bounded per mode; pipelines = fixed-depth compositions applied
 * in list order (expression [Rk/Pk]...[R1/P1]X, rightmost first).
 *
 * Modes:
 *   ai <depth> <maxlen>   -- does any pipeline compute a^i on W_2 = {a^i b a^j b a^k}? (i,j,k>=1)
 *   pb <depth> <maxlen>   -- ... compute P_b (longest b-free prefix) on all binary strings <= 9?
 *   tau <depth> <maxlen>  -- ... compute tau (truncate at leftmost aa) on all marked texts?
 *   par <depth> <maxlen>  -- parity wall: does any pipeline compute the leading gap's TOKEN-PARITY
 *                              on marked texts u.baa.v (u in {ba,bb}*), i.e. g(u) factors through
 *                              |u| mod 2 AND separates the two classes?
 *   slope <depth> <maxlen>-- equal-slope phenomenon (toll core): on W_2, is the a-count constant
 *                              on (same S, same (i,j,k) mod M) classes for some small M?
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXA 3
#define MAXB 3
#define BUFC 8192

static char AS[64][MAXA+2], BS[64][MAXB+2]; static int nAS, nBS;
static int PAT[MAXA*MAXB*4+8], cur_depth;

/* one pass: replace B by A, greedy leftmost, no rescan */
static int apply_pass(char *dst, const char *src, const char *A, const char *B){
    int la=strlen(A), lb=strlen(B), lc=strlen(src), op=0, p=0;
    if(lb==0) return -1;
    while(p<lc){
        if(p+lb<=lc && !memcmp(src+p,B,lb)){ if(op+la>=BUFC) return -1; memcpy(dst+op,A,la); op+=la; p+=lb; }
        else { if(op+1>=BUFC) return -1; dst[op++]=src[p++]; }
    }
    dst[op]=0; return op;
}

static char buf1[BUFC], buf2[BUFC], buf3[BUFC];
static long long evaluated=0;

/* apply pipeline PASS[0..d) to in; returns pointer to static result or NULL on overflow */
static const char *run_pipe(const char *in, int d){
    char *cur = buf1, *nxt = buf2;
    strncpy(cur,in,BUFC-1); cur[BUFC-1]=0;
    for(int t=0;t<d;t++){
        const char *A = AS[PAT[t]/nBS], *B = BS[PAT[t]%nBS];
        if(apply_pass(nxt,cur,A,B)<0) return NULL;
        char *tmp=cur; cur=nxt; nxt=tmp;
    }
    return cur;
}

/* ---------------- battery: a^i on W_2 ---------------- */
static const int AIP[][3] = {
 {1,1,1},{2,1,1},{1,2,1},{1,1,2},{3,1,1},{1,3,1},{1,1,3},{2,2,1},{2,1,2},{1,2,2},
 {4,1,1},{1,4,1},{1,1,4},{3,2,1},{2,3,1},{1,2,3},{3,1,2},{2,1,3},{1,3,2},{2,2,2},
 {5,3,2},{3,5,2},{2,3,5},{5,2,3},{3,2,5},{2,5,3},{6,4,3},{4,6,3},{3,4,6},{6,3,4},
 {4,3,6},{3,6,4},{8,3,2},{3,8,2},{2,3,8},{8,2,3},{3,2,8},{2,8,3},{7,5,3},{5,7,3},
 {3,5,7},{7,3,5},{5,3,7},{3,7,5},{6,6,2},{6,2,6},{2,6,6},{9,4,3},{4,9,3},{3,4,9}};
static int NAIP = sizeof(AIP)/sizeof(AIP[0]);

static void mk_w2(int i,int j,int k,char *s){
    int p=0;
    for(int t=0;t<i;t++) s[p++]='a'; s[p++]='b';
    for(int t=0;t<j;t++) s[p++]='a'; s[p++]='b';
    for(int t=0;t<k;t++) s[p++]='a'; s[p]=0;
}

static int check_ai(const char *r, int idx){
    int i=AIP[idx][0], j=AIP[idx][1], k=AIP[idx][2];
    (void)j;(void)k;
    return r && (int)strlen(r)==i && (i==0 || (r[0]=='a' && !strchr(r,'b')));
}

/* positive control: a^{i+j+k} (the merge) IS computable (e.g. [eps/b]) */
static int check_as(const char *r, int idx){
    int i=AIP[idx][0], j=AIP[idx][1], k=AIP[idx][2];
    return r && (int)strlen(r)==i+j+k && (i+j+k==0 || (r[0]=='a' && !strchr(r,'b')));
}
static void census_pos(int depth){
    long long total=0, pass_all=0; int idx[8];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        char s[128]; int ok=1;
        for(int b=0;b<NAIP && ok;b++){
            mk_w2(AIP[b][0],AIP[b][1],AIP[b][2],s);
            evaluated++;
            if(!check_as(run_pipe(s,depth), b)) ok=0;
        }
        if(ok){ pass_all++;
            printf("  ++ a^S witness:");
            for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
            printf("\n");
        }
    }
    printf("[census pos d=%d] pipelines=%lld evals=%lld witnesses=%lld\n", depth,total,evaluated,pass_all);
}

/* ---------------- battery: P_b ---------------- */
static char **pbs; static int npbs; static char **pbw;
static void pb_battery(void){
    int cap = 1024+600; pbs = malloc(sizeof(char*)*cap); pbw = malloc(sizeof(char*)*cap); npbs=0;
    for(int L=0; L<=8; L++)
        for(int m=0;m<(1<<L);m++){
            char *s=malloc(L+2);
            for(int i=0;i<L;i++) s[i]= (m>>(L-1-i))&1?'b':'a';
            s[L]=0; pbs[npbs]=s;
            char *w=malloc(L+2); const char *q=strchr(s,'b');
            if(!q) strcpy(w,s); else { memcpy(w,s,q-s); w[q-s]=0; }
            pbw[npbs++]=w;
            if(npbs>=cap){fprintf(stderr,"pb battery ovf\n");exit(1);}
        }
}

/* ---------------- battery: tau on marked texts ---------------- */
static char **tbs; static char **tbw; static int ntbs;
static void tau_battery(int maxtok){
    int cap = 4000; tbs=malloc(sizeof(char*)*cap); tbw=malloc(sizeof(char*)*cap); ntbs=0;
    // enumerate products of {ba,bb,baa} up to maxtok tokens, BFS order
    tbs[ntbs]=strdup(""); tbw[ntbs]=strdup(""); ntbs++;
    int lvl_start=0, lvl_end=1;
    for(int t=0;t<maxtok;t++){
        for(int i=lvl_start;i<lvl_end;i++){
            const char *toks[3]={"ba","bb","baa"};
            for(int j=0;j<3;j++){
                char *s=malloc(strlen(tbs[i])+4); strcpy(s,tbs[i]); strcat(s,toks[j]);
                const char *q=strstr(s,"aa");
                char *w=malloc(strlen(s)+1);
                if(!q) strcpy(w,s); else { memcpy(w,s,q-s); w[q-s]=0; }
                tbs[ntbs]=s; tbw[ntbs]=w; ntbs++;
                if(ntbs>=cap){fprintf(stderr,"tau battery ovf\n");exit(1);}
            }
        }
        lvl_start=lvl_end; lvl_end=ntbs;
    }
}


static void census_ai(int depth){
    long long total=0, pass_all=0;
    int idx[8];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++)
    for(idx[3]=0; idx[3]<(depth>3?nAS*nBS:1); idx[3]++)
    for(idx[4]=0; idx[4]<(depth>4?nAS*nBS:1); idx[4]++)
    for(idx[5]=0; idx[5]<(depth>5?nAS*nBS:1); idx[5]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        char s[128]; int ok=1;
        for(int b=0;b<NAIP && ok;b++){
            mk_w2(AIP[b][0],AIP[b][1],AIP[b][2],s);
            evaluated++;
            if(!check_ai(run_pipe(s,depth), b)) ok=0;
        }
        if(ok){ pass_all++;
            printf("  !! a^i ON W_2 CANDIDATE:");
            for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
            printf("\n");
        }
    }
    printf("[census ai d=%d] pipelines=%lld evals=%lld candidates=%lld\n", depth,total,evaluated,pass_all);
}

static void census_pb(int depth){
    pb_battery();
    long long total=0, pass_all=0; int idx[8];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++)
    for(idx[3]=0; idx[3]<(depth>3?nAS*nBS:1); idx[3]++)
    for(idx[4]=0; idx[4]<(depth>4?nAS*nBS:1); idx[4]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        int ok=1;
        for(int b=0;b<npbs && ok;b++){
            evaluated++;
            const char *r=run_pipe(pbs[b],depth);
            if(!r || strcmp(r,pbw[b])) ok=0;
        }
        if(ok){ pass_all++;
            printf("  !! P_b CANDIDATE:");
            for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
            printf("\n");
        }
    }
    printf("[census pb d=%d] pipelines=%lld evals=%lld candidates=%lld\n", depth,total,evaluated,pass_all);
}

static void census_tau(int depth){
    tau_battery(4);
    long long total=0, pass_all=0; int idx[8];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++)
    for(idx[3]=0; idx[3]<(depth>3?nAS*nBS:1); idx[3]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        int ok=1;
        for(int b=0;b<ntbs && ok;b++){
            evaluated++;
            const char *r=run_pipe(tbs[b],depth);
            if(!r || strcmp(r,tbw[b])) ok=0;
        }
        if(ok){ pass_all++;
            printf("  !! tau CANDIDATE:");
            for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
            printf("\n");
        }
    }
    printf("[census tau d=%d] pipelines=%lld evals=%lld candidates=%lld\n", depth,total,evaluated,pass_all);
}

/* ---------------- parity wall ---------------- */
#define NU 63
static char us[NU][16]; static int ul[NU];
static void par_enum_u(void){
    us[0][0]=0; ul[0]=0; int nu=1;
    for(int m=1;m<=5;m++){
        int start=nu;
        for(int i=(m==1?0:start-(1<<(m-1))); i<start; i++){
            strcpy(us[nu],us[i]); strcat(us[nu],"ba"); ul[nu]=m; nu++;
            strcpy(us[nu],us[i]); strcat(us[nu],"bb"); ul[nu]=m; nu++;
        }
    }
    if(nu!=NU){ printf("u-enumeration bug: %d\n",nu); exit(1); }
}
static const char *g_eval(int i, const char *v, int depth){
    static char s[80];
    strcpy(s,us[i]); strcat(s,"baa"); strcat(s,v);
    return run_pipe(s,depth);
}
static void census_par(int depth){
    par_enum_u();
    const char *vs[3] = {"", "ba", "bbaa"};
    int IDA_BA=-1, IDA_BB=-1, IDE_0=-1, IDE_ABA=-1, IDD_ABB=-1, IDD_BBA=-1;
    for(int i=0;i<NU;i++){
        if(!strcmp(us[i],"ba")) IDA_BA=i;
        if(!strcmp(us[i],"bb")) IDA_BB=i;
        if(ul[i]==0) IDE_0=i;
        if(!strcmp(us[i],"baba")) IDE_ABA=i;
        if(!strcmp(us[i],"babb")) IDD_ABB=i;
        if(!strcmp(us[i],"bbba")) IDD_BBA=i;
    }
    long long total=0, nconst=0, npf=0, nhit=0; int idx[8];
    static char *g[NU];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++)
    for(idx[3]=0; idx[3]<(depth>3?nAS*nBS:1); idx[3]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        for(int vi=0; vi<3; vi++){
            const char *v = vs[vi];
            /* cheap prefilter: within-class pairs must agree */
            const char *r1=g_eval(IDA_BA,v,depth), *r2=g_eval(IDA_BB,v,depth);
            if(!r1||!r2||strcmp(r1,r2)) continue;
            const char *r3=g_eval(IDE_ABA,v,depth);
            if(!r3||strcmp(r3,g_eval(IDE_0,v,depth))) continue;
            const char *r4=g_eval(IDD_ABB,v,depth), *r5=g_eval(IDD_BBA,v,depth);
            if(!r4||!r5||strcmp(r4,r5)) continue;
            /* full check */
            for(int i=0;i<NU;i++){ const char *r=g_eval(i,v,depth); g[i]=r?strdup(r):NULL; }
            int pf=1;
            for(int i=0;i<NU&&pf;i++){
                int par=ul[i]%2;
                if(!g[i]||!g[par?IDA_BA:IDE_0]||strcmp(g[i],g[par?IDA_BA:IDE_0])) pf=0;
            }
            int nc=0; for(int i=1;i<NU;i++) if(!g[i]||!g[0]||strcmp(g[i],g[0])){nc=1;break;}
            if(nc) nconst++;
            if(pf) npf++;
            if(pf && strcmp(g[IDE_0], g[IDA_BA])){
                nhit++;
                printf("  !! PARITY HIT (v=%s):",v);
                for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
                printf("  g(eps)=%s g(ba)=%s\n", g[IDE_0], g[IDA_BA]);
            }
            for(int i=0;i<NU;i++) free(g[i]);
        }
    }
    printf("[census par d=%d] pipelines=%lld evals=%lld  nonconst-ctx=%lld parity-factored-ctx=%lld HITS=%lld\n",
        depth,total,evaluated,nconst,npf,nhit);
}

/* ---------------- equal-slope phenomenon ---------------- */
#define NW 1331
static char w2s[NW][64]; static int w2i[NW],w2j[NW],w2k[NW],w2S[NW]; static int nw=0;
static int MORDER[13]={1,2,2,3,3,4,6,4,6,5,12,12,12}; /* probe order M=1,2,3,4,6,12 */
static int *groups[13]; static int gsize[13]; /* concatenated groups per M */
static void slope_setup(int LO,int HI){
    nw=0;
    for(int i=LO;i<=HI;i++)for(int j=LO;j<=HI;j++)for(int k=LO;k<=HI;k++){
        mk_w2(i,j,k,w2s[nw]); w2i[nw]=i;w2j[nw]=j;w2k[nw]=k; w2S[nw]=i+j+k; nw++;
    }
    /* build groups for M in {1,2,3,4,6,12}: same (S, i%M, j%M, k%M) */
    int Ms[6]={1,2,3,4,6,12};
    for(int mi=0;mi<6;mi++){
        int M=Ms[mi];
        int *grp = malloc(sizeof(int)*nw*2);
        int gn=0;
        int used[NW]; memset(used,0,sizeof used);
        for(int x=0;x<nw;x++){
            if(used[x]) continue;
            for(int y=x;y<nw;y++){
                if(used[y]) continue;
                if(w2S[y]!=w2S[x]) continue;
                if(w2i[y]%M!=w2i[x]%M||w2j[y]%M!=w2j[x]%M||w2k[y]%M!=w2k[x]%M) continue;
                used[y]=1; grp[gn++]=y;
            }
            grp[gn++]=-1; /* group sentinel */
        }
        groups[M]=grp; gsize[M]=gn;
    }
}
static void census_slope(int depth){
    slope_setup(3,13);
    int Ms[6]={1,2,3,4,6,12};
    long long total=0, flagged=0; int idx[8]; long long Mstat[13]={0};
    static int cnt[NW]; static char bad[NW];
    for(idx[0]=0; idx[0]<nAS*nBS; idx[0]++)
    for(idx[1]=0; idx[1]<(depth>1?nAS*nBS:1); idx[1]++)
    for(idx[2]=0; idx[2]<(depth>2?nAS*nBS:1); idx[2]++){
        for(int t=0;t<depth;t++) PAT[t]=idx[t];
        total++;
        int anybad=0;
        for(int b=0;b<nw;b++){
            evaluated++;
            const char *r=run_pipe(w2s[b],depth);
            if(!r){cnt[b]=-1;bad[b]=1;anybad=1;continue;}
            int c=0; for(const char *q=r;*q;q++) if(*q=='a') c++;
            cnt[b]=c; bad[b]=0;
        }
        int found=0;
        if(!anybad)
        for(int mi=0;mi<6 && !found;mi++){
            int M=Ms[mi], ok=1;
            int *grp=groups[M];
            for(int p=0;p<gsize[M]&&ok;){
                int head=p;
                while(grp[p]!=-1){
                    if(cnt[grp[p]]!=cnt[grp[head]]){ok=0;break;}
                    p++;
                }
                p++; /* skip sentinel */
            }
            if(ok){found=M;Mstat[M]++;}
        }
        if(!found){ flagged++;
            printf("  ?? SLOPE FLAG (or overflow):");
            for(int t=0;t<depth;t++) printf(" [%s/%s]",AS[PAT[t]/nBS],BS[PAT[t]%nBS]);
            printf("\n");
        }
    }
    printf("[census slope d=%d] pipelines=%lld evals=%lld flagged=%lld\n",depth,total,evaluated,flagged);
    printf("  working M: M=1:%lld M=2:%lld M=3:%lld M=4:%lld M=6:%lld M=12:%lld\n",
        Mstat[1],Mstat[2],Mstat[3],Mstat[4],Mstat[6],Mstat[12]);
}

static void build_space(int maxlenA, int maxlenB){
    nAS=0; nBS=0;
    char s[8];
    for(int L=0;L<=maxlenA;L++)
        for(int m=0;m<(1<<L);m++){
            for(int i=0;i<L;i++) s[i]=(m>>(L-1-i))&1?'b':'a'; s[L]=0;
            strcpy(AS[nAS++],s);
        }
    for(int L=1;L<=maxlenB;L++)
        for(int m=0;m<(1<<L);m++){
            for(int i=0;i<L;i++) s[i]=(m>>(L-1-i))&1?'b':'a'; s[L]=0;
            strcpy(BS[nBS++],s);
        }
    printf("pass space: %d replacements x %d patterns = %d passes\n",nAS,nBS,nAS*nBS);
}

int main(int argc,char**argv){
    if(argc<2){fprintf(stderr,"usage: census ai|pb|tau|par|slope <depth> <maxlenA> <maxlenB>\n");return 1;}
    int depth = argc>2?atoi(argv[2]):4;
    int mlA = argc>3?atoi(argv[3]):2;
    int mlB = argc>4?atoi(argv[4]):2;
    build_space(mlA,mlB);
    srand(1);
    if(!strcmp(argv[1],"ai")) census_ai(depth);
    else if(!strcmp(argv[1],"pos")) census_pos(depth);
    else if(!strcmp(argv[1],"pb")) census_pb(depth);
    else if(!strcmp(argv[1],"tau")) census_tau(depth);
    else if(!strcmp(argv[1],"par")) census_par(depth);
    else if(!strcmp(argv[1],"slope")) census_slope(depth);
    else {fprintf(stderr,"unknown mode\n");return 1;}
    return 0;
}
