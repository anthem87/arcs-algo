import numpy as np, math, random, time
random.seed(7)
Q=24; LIM=20000       # moduli used by the arcs; exact finish when remaining sum <= LIM
def exact_reach(W):
    r=1
    for w in W: r|=r<<w
    return r
def greedy(W,T):
    out=[]
    for w in sorted(W,reverse=True):
        if w<=T: T-=w; out.append(w)
    return out if T==0 else None
def dp_finish(W,T):                       # exact reconstruction on a small set
    S=sum(W)
    if T<0 or T>S: return None
    layers=[1]
    for w in W: layers.append(layers[-1]|(layers[-1]<<w))
    if not (layers[-1]>>T)&1: return None
    out=[]
    for k in range(len(W),0,-1):
        if (layers[k-1]>>T)&1: continue
        out.append(W[k-1]); T-=W[k-1]
    return out
class Arcs:
    """suffix data: for the set W[k:], residue counts N_c(q) (exact), sum, variance, size"""
    def __init__(self,W):
        self.W=W; n=len(W)
        self.S=[0]*(n+1); self.V=[0.0]*(n+1)
        self.N={q:[None]*(n+1) for q in range(2,Q+1)}
        for q in range(2,Q+1): self.N[q][n]=[1]+[0]*(q-1)
        for k in range(n-1,-1,-1):
            w=W[k]; self.S[k]=self.S[k+1]+w; self.V[k]=self.V[k+1]+w*w/4
            for q in range(2,Q+1):
                Nn=self.N[q][k+1]; self.N[q][k]=[Nn[c]+Nn[(c-w)%q] for c in range(q)]
    def score(self,k,T):                   # arc estimate of log(count) for target T with set W[k:]; -inf if certified impossible
        S=self.S[k]; m=len(self.W)-k
        if T<0 or T>S: return -math.inf
        if m==0: return 0.0 if T==0 else -math.inf
        best=0.0
        for q in range(2,Q+1):
            Nc=self.N[q][k][T%q]
            if Nc==0: return -math.inf
            best=max(best, math.log(q*Nc) - m*math.log(2))   # class density relative to uniform
        v=self.V[k]
        if v==0: return 0.0 if T==S//2 else -math.inf
        return m*math.log(2) - 0.5*math.log(2*math.pi*v) - (T-S/2)**2/(2*v) + best
def construct(A,T):
    W=A.W; k=0; out=[]
    while True:
        if A.S[k]<=LIM or k==len(W):
            rest=dp_finish(W[k:],T)
            return None if rest is None else out+rest
        w=W[k]
        sin=A.score(k+1,T-w); sout=A.score(k+1,T)
        if sin==-math.inf and sout==-math.inf: return None
        if sin>=sout: out.append(w); T-=w
        k+=1
tests={
 "dense random  n=200 in [1,2000]":       [random.randint(1,2000) for _ in range(200)],
 "mod-3 structure n=200":                 [3*random.randint(1,1000) for _ in range(198)]+[random.randint(1,3000) for _ in range(2)],
 "all even n=150 in [2,3000]":            [2*random.randint(1,1500) for _ in range(150)],
 "mod-6 mix n=150":                       [6*random.randint(1,500) for _ in range(140)]+[6*random.randint(1,500)+2 for _ in range(10)],
 "medium density n=60 in [1,1e4]":        [random.randint(1,10**4) for _ in range(60)],
 "sparse n=30 in [1,1e5]":                [random.randint(1,10**5) for _ in range(30)],
}
rng=np.random.default_rng(3)
print(f"{'instance':34s}{'S':>9s}{'DP full [s]':>12s}{'arc prep [s]':>13s}{'ms/target':>10s}{'constructor ok':>16s}{'(bulk)':>9s}{'(tails)':>9s}{'greedy ok':>11s}{'false no':>10s}")
for name,W in tests.items():
    W=sorted(W,reverse=True); S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
    t0=time.time(); R=exact_reach(W); tdp=time.time()-t0
    t0=time.time(); A=Arcs(W); tprep=time.time()-t0
    reach=[t for t in range(S+1) if (R>>t)&1]; reach=np.array(reach)
    bulk=reach[np.abs(reach-S/2)<=3*s]; tails=reach[np.abs(reach-S/2)>3*s]
    sb=rng.choice(bulk,min(400,len(bulk)),replace=False)
    st=rng.choice(tails,min(400,len(tails)),replace=False) if len(tails) else np.array([],int)
    def run(sample):
        ok=0; t0=time.time()
        for T in sample:
            sol=construct(A,int(T))
            if sol is not None and sum(sol)==T and all(x in W for x in sol): ok+=1
        return ok/len(sample) if len(sample) else float('nan'), (time.time()-t0)/max(1,len(sample))*1e3
    ob,tb=run(sb); ot,tt=run(st)
    allok=(ob*len(sb)+ (ot*len(st) if len(st) else 0))/(len(sb)+len(st))
    g=np.mean([greedy(W,int(T)) is not None for T in np.concatenate([sb,st])])
    # false "no": unreachable targets wrongly built? (impossible by verification) -> check unreachable rejected
    unreach=[t for t in rng.integers(0,S+1,3000) if not (R>>int(t))&1][:200]
    wrong=sum(construct(A,int(t)) is not None for t in unreach)
    print(f"{name:34s}{S:9d}{tdp:12.3f}{tprep:13.3f}{(tb+tt)/2:10.2f}{100*allok:15.1f}%{100*ob:8.1f}%{100*ot:8.1f}%{100*g:10.1f}%{wrong:6d}/{len(unreach)}")
