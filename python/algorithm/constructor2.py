import numpy as np, math, random, time
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'constructor.py')).read().split("tests={")[0])
MITM_M=40
def subset_sums(ws):
    s=np.zeros(1,np.int64)
    for w in ws: s=np.concatenate([s,s+w])
    return s
def mitm(W,T):                    # exact search on a small set (<= 40 weights)
    h=len(W)//2; A_,B_=W[:h],W[h:]
    sa=subset_sums(A_); sb=subset_sums(B_)
    ob=np.argsort(sb); sbs=sb[ob]
    need=T-sa; pos=np.searchsorted(sbs,need); pos=np.minimum(pos,len(sbs)-1)
    hit=np.flatnonzero(sbs[pos]==need)
    if len(hit)==0: return None
    i=hit[0]; j=ob[pos[i]]
    return [A_[b] for b in range(len(A_)) if (i>>b)&1]+[B_[b] for b in range(len(B_)) if (j>>b)&1]
def construct2(A,T):
    W=A.W; n=len(W); k=0; out=[]
    while True:
        m=n-k
        if m<=MITM_M:
            rest=mitm(W[k:],T); return None if rest is None else out+rest
        w=W[k]
        sin=A.score(k+1,T-w); sout=A.score(k+1,T)
        if sin==-math.inf and sout==-math.inf: return None
        if sin>=sout: out.append(w); T-=w
        k+=1
random.seed(11); rng=np.random.default_rng(5)
cases={
 "n=30  in [1,1e5]  (prev. failure)": [random.randint(1,10**5) for _ in range(30)],
 "n=200 in [1,1e10]  (S~1e12)":      [random.randint(1,10**10) for _ in range(200)],
 "n=200 in [1,1e13]  (S~1e15)":      [random.randint(1,10**13) for _ in range(200)],
 "n=200 mult. of 7 in [1,1e12]":    [7*random.randint(1,10**11) for _ in range(200)],
 "n=120 in [1,1e15]  (2^n vs S: 1e36 vs 6e16)": [random.randint(1,10**15) for _ in range(120)],
 "n=80  in [1,1e18]  (1e24 vs 4e19)": [random.randint(1,10**18) for _ in range(80)],
 "n=60  in [1,1e17]  (1e18 vs 3e18, critical)": [random.randint(1,10**17) for _ in range(60)],
}
print(f"{'instance':46s}{'DP bits needed':>15s}{'prep[s]':>8s}{'ms/T':>8s}{'built (verified)':>18s}{'bulk':>7s}{'±5σ':>7s}{'greedy':>8s}{'mod-q rejects':>14s}")
for name,W in cases.items():
    W=sorted(W,reverse=True); S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
    if S>=2**62: print(name,"skip (int64)"); continue
    t0=time.time(); A=Arcs(W); tp=time.time()-t0
    Tb=[int(S//2+rng.normal()*s) for _ in range(150)]
    Tt=[int(S//2+rng.choice([-1,1])*rng.uniform(3,5)*s) for _ in range(150)]
    def run(Ts):
        ok=0; t0=time.time()
        for T in Ts:
            sol=construct2(A,T)
            if sol is not None and sum(sol)==T: ok+=1
        return ok/len(Ts),(time.time()-t0)/len(Ts)*1e3
    ob,tb=run(Tb); ot,tt=run(Tt)
    g=np.mean([greedy(W,T) is not None for T in Tb+Tt])
    # targets in a forbidden class (only meaningful if obstruction exists)
    rej=0; tot=0
    for q in range(2,Q+1):
        bad=[c for c in range(q) if A.N[q][0][c]==0]
        if bad:
            for _ in range(50):
                T=int(S//2+rng.normal()*s); T+= (bad[0]-T)%q; tot+=1; rej+= construct2(A,T) is None
            break
    print(f"{name:46s}{len(W)*S:15.1e}{tp:8.2f}{(tb+tt)/2:8.1f}{100*(ob+ot)/2:17.1f}%{100*ob:6.0f}%{100*ot:6.0f}%{100*g:7.1f}%{(str(rej)+'/'+str(tot)) if tot else '—':>14s}")
