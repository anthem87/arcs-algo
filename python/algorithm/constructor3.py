import numpy as np, math, random, time
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'constructor2.py')).read().split("random.seed(11)")[0])
CAP=48; DENS=16.0
def mstar(W):           # smallest final block (the m smallest weights) whose subset sums are dense: 2^m/(sqrt(2pi)*sigma_m) >= DENS
    for m in range(10,CAP+1):
        blk=W[-m:]; sig=math.sqrt(sum(x*x for x in blk)/4)
        if m*math.log(2)-math.log(math.sqrt(2*math.pi)*sig)>=math.log(DENS): return m
    return CAP
def construct3(A,T,M):
    W=A.W; n=len(W); k=0; out=[]
    while True:
        if n-k<=M:
            rest=mitm(W[k:],T); return None if rest is None else out+rest
        w=W[k]; sin=A.score(k+1,T-w); sout=A.score(k+1,T)
        if sin==-math.inf and sout==-math.inf: return None
        if sin>=sout: out.append(w); T-=w
        k+=1
random.seed(11); rng=np.random.default_rng(5)
cases={
 "n=200 in [1,1e10]":            [random.randint(1,10**10) for _ in range(200)],
 "n=200 in [1,1e13]":            [random.randint(1,10**13) for _ in range(200)],
 "n=200 mult of 7 in [1,1e12]":  [7*random.randint(1,10**11) for _ in range(200)],
 "n=120 in [1,1e15]":            [random.randint(1,10**15) for _ in range(120)],
 "n=60  in [1,1e17] (critical)": [random.randint(1,10**17) for _ in range(60)],
}
print(f"{'instance':32s}{'final block m*':>15s}{'s/T':>7s}{'built (verified)':>18s}{'bulk':>7s}{'±5σ':>7s}")
for name,W in cases.items():
    W=sorted(W,reverse=True); S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
    A=Arcs(W); M=mstar(W)
    Tb=[int(S//2+rng.normal()*s) for _ in range(40)]
    Tt=[int(S//2+rng.choice([-1,1])*rng.uniform(3,5)*s) for _ in range(40)]
    def run(Ts):
        ok=0; t0=time.time()
        for T in Ts:
            sol=construct3(A,T,M); ok+= sol is not None and sum(sol)==T
        return ok/len(Ts),(time.time()-t0)/len(Ts)
    ob,tb=run(Tb); ot,tt=run(Tt)
    print(f"{name:32s}{M:15d}{(tb+tt)/2:7.2f}{100*(ob+ot)/2:17.1f}%{100*ob:6.0f}%{100*ot:6.0f}%",flush=True)
