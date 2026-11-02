"""Validation of arcs_float.py and endgame_fast.py against the exact reference (hurs_arcs.Arcs, hurs_arcs.mitm)."""
import random, math, time
from collections import Counter
from hurs_arcs import Arcs, mitm
from arcs_float import ArcsF
from endgame_fast import mitm_merge, endgame_mod
random.seed(123)
print("== (3) float class counts vs exact integers ==")
cases=[("60 in [1,2000]",[random.randint(1,2000) for _ in range(60)]),
       ("150 even",[2*random.randint(1,1000) for _ in range(150)]),
       ("198 mult 3 + 2",[3*random.randint(1,700) for _ in range(198)]+[random.randint(1,2000) for _ in range(2)]),
       ("200 in [1,1e10]",[random.randint(1,10**10) for _ in range(200)]),
       ("150 mult 7 in [1,7e11]",[7*random.randint(1,10**11) for _ in range(150)])]
for name,W in cases:
    W=sorted(W,reverse=True); n=len(W)
    t0=time.time(); A=Arcs(W); te=time.time()-t0
    t0=time.time(); F=ArcsF(W); tf=time.time()-t0
    zmis=0; dmax=0.0; checks=0
    for k in range(0,n+1,max(1,n//40)):
        S=A.S[k]
        for _ in range(25):
            T=random.randint(0,S) if S>0 else 0
            for q in range(2,25):
                ex=A.N[q][k][T%q]; fl=F.N[q][k,T%q]
                if (ex==0)!=(fl==0.0): zmis+=1
            a=A.score(k,T); b=F.score(k,T)
            a0=a if a==-math.inf else (a[0] if isinstance(a,tuple) else a); b0=b if b==-math.inf else b[0]
            checks+=1
            if (a0==-math.inf)!=(b0==-math.inf): zmis+=1
            elif a0!=-math.inf: dmax=max(dmax,abs(a0-b0))
    print(f"{name:24s} n={n:3d}  prep exact {te:6.3f}s  float {tf:6.3f}s  zero mismatches {zmis}  max|score diff| {dmax:.2e}  ({checks} scores)")
print("== (2)+(1) endgame vs exact mitm ==")
for m,M in [(20,10**4),(30,10**6),(36,10**8),(40,10**9)]:
    agree=0; okm=0; okmod=0; t_old=t_new=t_mod=0.0; N=20; Fs=[]
    erng=random.Random(1000*m+M%997)                 # the endgame's own generator: the draws of the blocks do not depend on it
    for it in range(N):
        W=[random.randint(1,M) for _ in range(m)]; S=sum(W)
        T=S//2+random.randint(-M//2,M//2)
        t0=time.time(); a=mitm(W,T); t_old+=time.time()-t0
        t0=time.time(); b=mitm_merge(W,T); t_new+=time.time()-t0
        sig=math.sqrt(sum(x*x for x in W)/4); F=2**m/math.sqrt(2*math.pi*sig*sig)
        Fs.append(F); t0=time.time(); c,_=endgame_mod(W,T,F,erng); t_mod+=time.time()-t0
        for s in (b,c):
            if s is not None: assert sum(s)==T and not (Counter(s)-Counter(W))
        agree+=((a is None)==(b is None)); okm+=(b is not None); okmod+=((a is None)==(c is None))
    print(f"m={m} M={M:.0e} lambda mean {sum(Fs)/N:7.1f} (last block {F:7.1f}): merge agrees {agree}/{N}, mod agrees {okmod}/{N}, found {okm}/{N}; ms old {1e3*t_old/N:8.2f} merge {1e3*t_new/N:8.2f} mod {1e3*t_mod/N:8.2f}")
