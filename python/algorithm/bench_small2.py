"""Floating-point counts and filtered endgame on the small rows of Table 9, exact ground truth by bitset DP over 200 reachable targets."""
import random, math, time
from collections import Counter
from arcs_float import ArcsF
from bench_big2 import solve2
def reach(W):
    r=1
    for w in W: r|=r<<w
    return r
random.seed(9)
for name,n,M,RHO in [("40 in [1,1e4]",40,10**4,500),("30 in [1,1e5]",30,10**5,500),("100 in [1,1e5]",100,10**5,500),("200 in [1,1e6]",200,10**6,500)]:
    W=[random.randint(1,M) for _ in range(n)]; R=reach(W); S=sum(W)
    Ts=[]
    while len(Ts)<200:
        T=random.randint(0,S)
        if (R>>T)&1: Ts.append(T)
    Wd=sorted(W,reverse=True); F=ArcsF(Wd); rng=random.Random(1)
    ok=wrong=0; t0=time.time(); fails=Counter()
    for T in Ts:
        sol,info,m,_=solve2(F,Wd,T,RHO,60,rng)
        if sol is None: fails[info]+=1; continue
        if sum(sol)==T and not (Counter(sol)-Counter(W)): ok+=1
        else: wrong+=1
    print(f"{name:16s} RHO={RHO}: found {ok}/200 wrong {wrong}  ms/target {1e3*(time.time()-t0)/200:6.2f}  {dict(fails)}",flush=True)
