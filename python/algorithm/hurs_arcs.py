"""HURS: an interval-union forward pass over the sorted weights, where dummy weights 1 + S restore completeness
   (Brown's criterion, o <= 1), with the arc constructor of the paper as backward pass."""
import numpy as np, math, random, time, sys
from math import gcd
from functools import reduce
from sympy import primerange
Q=24
# ---------------- HURS ----------------
def augment(W):                                   # dummy weights d = 1 + S for every gap (o <= 1 afterwards)
    S=0; D=[]
    for w in sorted(W):
        while w>1+S:
            d=1+S; D.append(d); S+=d
        S+=w
    return D
def omicron(W):
    S=0; o=0.0
    for w in sorted(W): o=max(o,w/(1+S)); S+=w
    return o
def forward(Wp):                                  # interval history H_i, K_i = #intervals
    H=[[(0,0)]]; Kmax=1
    for w in Wp:
        cur=H[-1]; sh=[(a+w,b+w) for a,b in cur]; merged=[]
        for a,b in sorted(cur+sh):
            if merged and a<=merged[-1][1]+1: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
            else: merged.append((a,b))
        H.append(merged); Kmax=max(Kmax,len(merged))
    return H,Kmax
def inH(H,v): return any(a<=v<=b for a,b in H)
def hurs_solve(W,T,node_cap=10**6):              # backward pass: greedy skipping the dummies, then DFS
    D=augment(W); lab=sorted([(w,0) for w in W]+[(d,1) for d in D])
    Wp=[x for x,_ in lab]; H,K=forward(Wp)
    if not inH(H[-1],T): return None,'UNREACHABLE',K
    v=T; I=[]
    for i in range(len(Wp),0,-1):
        w,dm=lab[i-1]
        if dm: continue
        if v>=w and inH(H[i-1],v-w): I.append(w); v-=w
        elif not inH(H[i-1],v): break
    if v==0: return I,'greedy',K
    # DFS fallback over originals only, pruned by H and remaining-original sum
    orig_idx=[i for i in range(len(Wp)) if lab[i][1]==0]
    rem=[0]*(len(orig_idx)+1)
    for j in range(len(orig_idx)-1,-1,-1): rem[j]=rem[j+1]+Wp[orig_idx[j]]
    nodes=[0]; sol=[None]
    sys.setrecursionlimit(10000)
    def dfs(j,v,acc):                             # j runs over originals from the top
        if sol[0] is not None or nodes[0]>node_cap: return
        nodes[0]+=1
        if v==0: sol[0]=list(acc); return
        if j<0 or v<0: return
        i=orig_idx[j]
        if v> sum(Wp[orig_idx[t]] for t in range(j+1)): return
        if not inH(H[i+1],v): return
        w=Wp[i]; acc.append(w); dfs(j-1,v-w,acc); acc.pop(); dfs(j-1,v,acc)
    dfs(len(orig_idx)-1,T,[])
    return sol[0],('dfs' if sol[0] is not None else 'dfs-cap'),K
# ---------------- arc constructor (backward on originals only) ----------------
class Arcs:
    def __init__(self,W):
        self.W=W; n=len(W); self.S=[0]*(n+1); self.V=[0.0]*(n+1)
        self.N={q:[None]*(n+1) for q in range(2,Q+1)}
        for q in range(2,Q+1): self.N[q][n]=[1]+[0]*(q-1)
        for k in range(n-1,-1,-1):
            w=W[k]; self.S[k]=self.S[k+1]+w; self.V[k]=self.V[k+1]+w*w/4
            for q in range(2,Q+1):
                Nn=self.N[q][k+1]; self.N[q][k]=[Nn[c]+Nn[(c-w)%q] for c in range(q)]
    def score(self,k,T):
        S=self.S[k]; m=len(self.W)-k
        if T<0 or T>S: return -math.inf
        if m==0: return 0.0 if T==0 else -math.inf
        best=0.0
        for q in range(2,Q+1):
            Nc=self.N[q][k][T%q]
            if Nc==0: return -math.inf
            best=max(best, math.log(q*Nc)-m*math.log(2))
        v=self.V[k]
        return m*math.log(2)-0.5*math.log(2*math.pi*v)-(T-S/2)**2/(2*v)+best
def subset_sums(ws):
    s=np.zeros(1,np.int64)
    for w in ws: s=np.concatenate([s,s+w])
    return s
def mitm(W,T):
    h=len(W)//2; A_,B_=W[:h],W[h:]; sa=subset_sums(A_); sb=subset_sums(B_)
    ob=np.argsort(sb,kind='stable'); sbs=sb[ob]; need=T-sa
    pos=np.minimum(np.searchsorted(sbs,need),len(sbs)-1); hit=np.flatnonzero(sbs[pos]==need)
    if len(hit)==0: return None
    i=int(hit[0]); j=int(ob[pos[i]])
    return [A_[b] for b in range(len(A_)) if (i>>b)&1]+[B_[b] for b in range(len(B_)) if (j>>b)&1]
def mstar(W,cap=48,dens=16.0):
    for m in range(1,min(cap,len(W))+1):
        blk=W[-m:]; g=reduce(gcd,blk); sig=math.sqrt(sum(x*x for x in blk)/4) or 1.0
        if m*math.log(2)-math.log(math.sqrt(2*math.pi)*sig/g)>=math.log(dens): return m
    return min(cap,len(W))
def arc_construct(A,T,M):
    W=A.W; n=len(W); k=0; out=[]
    while True:
        if n-k<=M:
            rest=mitm(W[k:],T); return None if rest is None else out+rest
        w=W[k]; sin=A.score(k+1,T-w); sout=A.score(k+1,T)
        if sin==-math.inf and sout==-math.inf: return None
        if sin>=sout: out.append(w); T-=w
        k+=1
def hurs_arc_solve(W,T,M=None):                  # HURS forward with dummies (negative certificate), arc backward on originals
    D=augment(W); Wp=sorted(W+D); S_p=sum(Wp)
    if T<0 or T>S_p: return None,'UNREACHABLE'
    Wd=sorted(W,reverse=True); A=Arcs(Wd)
    if M is None: M=mstar(Wd)
    sol=arc_construct(A,T,M)
    return sol,'arc'
