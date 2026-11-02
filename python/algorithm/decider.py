import numpy as np, math, random, time
random.seed(7)
def exact_reach(W):                       # ground truth: bitset DP
    r=1
    for w in W: r|=r<<w
    S=sum(W); return np.array([(r>>t)&1 for t in range(S+1)],bool)
def greedy_ok(W,T):
    for w in sorted(W,reverse=True):
        if w<=T: T-=w
    return T==0
def residue_counts(W,q):                  # exact N_c(q) = (1/q) sum_a e(-ca/q) F(e(a/q)); computed exactly (integers)
    N=[1]+[0]*(q-1)
    for w in W:
        N=[N[c]+N[(c-w)%q] for c in range(q)]
    return N
def arc_decider(W,Q=40,kappa=1.0):
    S=sum(W); n=len(W); w=np.array(W,float)
    mu=S/2; s2=(w**2).sum()/4; s=math.sqrt(s2)
    # residue obstructions from the arcs (exact)
    obst=[]
    for q in range(2,Q+1):
        N=residue_counts(W,q)
        if any(x==0 for x in N): obst.append((q,{c for c in range(q) if N[c]==0}))
    T=np.arange(S+1)
    ok=np.ones(S+1,bool)
    for q,bad in obst:
        ok&=~np.isin(T%q,list(bad))
    # bulk: Gaussian (q=1 arc) log2-count, corrected by the class density: if only m of q classes are live, density *= q/m
    boost=1.0
    for q,bad in obst: boost=max(boost,q/(q-len(bad)))
    log2cnt=n - 0.5*math.log2(2*math.pi*s2) - (T-mu)**2/(2*s2)/math.log(2) + math.log2(boost)
    ok&=log2cnt>kappa
    return ok,obst
tests={
 "dense random  n=200 in [1,2000]":       [random.randint(1,2000) for _ in range(200)],
 "mod-3 structure n=200 (198 mult of 3 + 2)": [3*random.randint(1,1000) for _ in range(198)]+[random.randint(1,3000) for _ in range(2)],
 "all even n=150 in [2,3000]":            [2*random.randint(1,1500) for _ in range(150)],
 "mod-6 mix n=150":                         [6*random.randint(1,500) for _ in range(140)]+[6*random.randint(1,500)+2 for _ in range(10)],
 "medium density n=60 in [1,1e4]":        [random.randint(1,10**4) for _ in range(60)],
 "sparse n=30 in [1,1e5]":                [random.randint(1,10**5) for _ in range(30)],
}
print(f"{'instance':44s}{'S':>9s}{'reach%':>8s}{'greedy ok (on reachable)':>26s}{'arc acc all':>12s}{'arc acc bulk±3σ':>17s}{'FP':>7s}{'FN':>7s}  obstructions")
for name,W in tests.items():
    S=sum(W); t0=time.time(); R=exact_reach(W); te=time.time()-t0
    t0=time.time(); P,obst=arc_decider(W); ta=time.time()-t0
    s=math.sqrt(sum(x*x for x in W)/4); T=np.arange(S+1); bulk=np.abs(T-S/2)<=3*s
    idx=np.flatnonzero(R); samp=np.random.default_rng(1).choice(idx,min(3000,len(idx)),replace=False)
    g=np.mean([greedy_ok(W,int(t)) for t in samp])
    acc=np.mean(P==R); accb=np.mean(P[bulk]==R[bulk]); FP=int(np.sum(P&~R)); FN=int(np.sum(~P&R))
    ob=", ".join(f"q={q}:{sorted(b)[:4]}{'…' if len(b)>4 else ''}" for q,b in obst[:3])
    print(f"{name:44s}{S:9d}{100*R.mean():8.2f}{100*g:25.1f}%{100*acc:11.3f}%{100*accb:16.4f}%{FP:7d}{FN:7d}  {ob}")
