"""Fixed Q = 24 vs dynamic Q(k) vs no arcs, planted targets (as ablation.py), filtered endgame.
   usage: python3 bench_dyn.py <case> [RHO] [C_EPS] [NT]"""
import random, math, time, sys
from collections import Counter
from arcs_dyn import ArcsDyn
from endgame_fast import endgame_mod
def solve(F,Wd,T,RHO,CAP,rng):
    out=[]
    for k,w in enumerate(Wd):
        r=F.score(k,T)
        if r==-math.inf: return None
        sc,m,v=r
        if m<=CAP and m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest,_=endgame_mod(Wd[k:],T,math.exp(sc),rng); return None if rest is None else out+rest
        si=F.score(k+1,T-w); so=F.score(k+1,T)
        si=si[0] if si!=-math.inf else si; so=so[0] if so!=-math.inf else so
        if si==-math.inf and so==-math.inf: return None
        if si>=so: out.append(w); T-=w
    return out if T==0 else None
def cases():
    random.seed(3)
    return [("200 random in [1,1e10]",[random.randint(1,10**10) for _ in range(200)]),
     ("198×3k + 2 in [1,3e9]",[3*random.randint(1,10**9) for _ in range(198)]+[random.randint(1,3*10**9) for _ in range(2)]),
     ("195×7k + 5 in [1,7e9]",[7*random.randint(1,10**9) for _ in range(195)]+[random.randint(1,7*10**9) for _ in range(5)]),
     ("195×101k + 5 in [1,1.01e11]",[101*random.randint(1,10**9) for _ in range(195)]+[random.randint(1,101*10**9) for _ in range(5)]),
     ("195×1009k + 5 in [1,1e12]",[1009*random.randint(1,10**9) for _ in range(195)]+[random.randint(1,1009*10**9) for _ in range(5)]),
     ("190×6k + 10 in [1,6e9]",[6*random.randint(1,10**9) for _ in range(190)]+[random.randint(1,6*10**9) for _ in range(10)])]
if __name__=="__main__":
    c=int(sys.argv[1]); RHO=float(sys.argv[2]) if len(sys.argv)>2 else 5e4; CE=float(sys.argv[3]) if len(sys.argv)>3 else 1.0; NT=int(sys.argv[4]) if len(sys.argv)>4 else 20
    name,W=cases()[c]; rnd=random.Random(100+c)
    Ts=[sum(w for w in W if rnd.random()<0.5) for _ in range(NT)]
    Wd=sorted(W,reverse=True)
    for label,kw in [("Q=24 fixed",dict(fixed=range(2,25),C_EPS=0)),("dynamic",dict(C_EPS=CE)),("no arcs",dict(fixed=[]))]:
        t0=time.time(); F=ArcsDyn(Wd,**kw); tp=time.time()-t0
        rng=random.Random(7); ok=wrong=0; t0=time.time()
        for T in Ts:
            s=solve(F,Wd,T,RHO,60,rng)
            if s is None: continue
            if sum(s)==T and not (Counter(s)-Counter(W)): ok+=1
            else: wrong+=1
        dt=(time.time()-t0)/len(Ts)
        sz=sum(len(x) for x in F.sel[:len(Wd)-40])/max(1,len(Wd)-40)
        top=sorted(set(q for x in F.sel[:len(Wd)-40] for q in x))[:8]
        print(f"{name:28s} {label:11s} found {ok:2d}/{NT} wrong {wrong}  prep {tp:6.3f}s  ms/target {1e3*dt:8.1f}  mean|Q(k)| {sz:5.1f}  moduli {top}",flush=True)
