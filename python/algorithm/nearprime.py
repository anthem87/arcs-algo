import random, math, cmath, time
from collections import Counter
from sympy import primerange
from hurs_arcs import Arcs, omicron
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'pure2.py')).read().split("print(f\"{'n'")[0])
from hurs_hybrid import forward_orig
random.seed(9)
def gok(W,T):
    for w in sorted(W,reverse=True):
        if w<=T: T-=w
    return T==0
P=list(primerange(2,4000))
sets={
 "primes ≡1 mod 4":      [p for p in P if p%4==1],
 "primes ≡3 mod 4":      [p for p in P if p%4==3],
 "primes ≡1 mod 3":      [p for p in P if p%3==1],
 "odd primes (no 1,2)":  [p for p in P if p>2],
 "primes, every 3rd removed": [p for i,p in enumerate(P) if i%3],
}
print(f"{'set':28s}{'n':>5}{'omicron':>9}{'K (HURS)':>9}{'reach%':>8}{'greedy':>8}{'arcs':>7}   top arcs |F(e(a/q))|/2^n  (log, per weight)")
for name,W in sets.items():
    t0=time.time()
    Wd=sorted(W,reverse=True); n=len(W); S=sum(W); A=Arcs(Wd)
    R=1
    for w in W: R|=R<<w
    H=forward_orig(sorted(W),10**7); K=len(H[-1])
    reach=[t for t in range(S+1) if (R>>t)&1]; Ts=random.sample(reach,300)
    g=sum(gok(W,T) for T in Ts)/3
    a=sum((lambda s:s is not None and sum(s)==T)(arc_with_full_endgame(A,T,5000)[0]) for T in Ts)/3
    arcs=[]
    for q in range(2,13):
        for aa in range(1,q):
            if math.gcd(aa,q)!=1 or aa>q-aa: continue
            l=sum(math.log(abs(1+cmath.exp(2j*math.pi*aa*w/q))) if abs(1+cmath.exp(2j*math.pi*aa*w/q))>1e-12 else -1e9 for w in W)-n*math.log(2)
            arcs.append((l/n,f"{aa}/{q}"))
    arcs.sort(reverse=True); top=", ".join(f"{s} {v:+.3f}" for v,s in arcs[:4] if v>-50)
    print(f"{name:28s}{n:5d}{omicron(W):9.2f}{K:9d}{100*len(reach)/(S+1):7.2f}%{g:7.0f}%{a:6.0f}%   {top}   [{time.time()-t0:.0f}s]",flush=True)
