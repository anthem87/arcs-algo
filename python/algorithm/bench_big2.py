"""Benchmark of the floating-point counts (§5.4) and the filtered endgame (§5.6) on the instances and targets of bench_big.py (same seed 77).
   usage: python3 bench_big2.py <case 0|1|2> <old|new> [RHO] [CAP]"""
import random, math, time, sys
from collections import Counter
from hurs_arcs import omicron, augment
from arcs_float import ArcsF
from endgame_fast import endgame_mod
def solve2(F,Wd,T,RHO,CAP,rng):
    out=[]
    for k,w in enumerate(Wd):
        r=F.score(k,T)
        if r==-math.inf: return None,'scored-out',0,0
        sc,m,v=r
        if m<=CAP and m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest,tries=endgame_mod(Wd[k:],T,math.exp(sc),rng)
            return (None,'endgame-no',m,tries) if rest is None else (out+rest,'ok',m,tries)
        si=F.score(k+1,T-w); so=F.score(k+1,T)
        si=si[0] if si!=-math.inf else si; so=so[0] if so!=-math.inf else so
        if si==-math.inf and so==-math.inf: return None,'both-out',0,0
        if si>=so: out.append(w); T-=w
    return (out,'ok',0,0) if T==0 else (None,'end',0,0)
def _main():
    case=int(sys.argv[1]); mode=sys.argv[2]; RHO=float(sys.argv[3]) if len(sys.argv)>3 else 50.0; CAP=int(sys.argv[4]) if len(sys.argv)>4 else 46
    random.seed(77)
    cases=[("200 in [1,1e10]",[random.randint(1,10**10) for _ in range(200)],None),
           ("200 in [1,1e12]",[random.randint(1,10**12) for _ in range(200)],None),
           ("150 mult. of 7 in [1,7e11]",[7*random.randint(1,10**11) for _ in range(150)],7)]
    allTs=[]
    for name,W,g in cases:                             # same draw order as bench_big.py
        S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
        Ts=[int(S//2+random.gauss(0,1)*s) for _ in range(12)]+[int(S//2+random.choice([-1,1])*random.uniform(2,4)*s) for _ in range(8)]
        if g: Ts=[T-T%g for T in Ts]
        allTs.append(Ts)
    name,W,g=cases[case]; Ts=allTs[case]
    if mode=='old':
        exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'deblur.py')).read().split("random.seed(21)")[0], globals())
        from hurs_arcs import mitm; globals()['mitm']=mitm   # the exec'd code runs in the module globals
        exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'bench_big.py')).read().split("random.seed(77)")[0].split("from hurs_arcs import mitm")[1], globals())
        t0=time.time(); B=Deblurred(W); tp=time.time()-t0
        run=lambda T: solve_big(B,T,RHO)+(0,)
    else:
        Wd=sorted(W,reverse=True); rng=random.Random(2026)
        t0=time.time(); F=ArcsF(Wd); tp=time.time()-t0
        run=lambda T: solve2(F,Wd,T,RHO,CAP,rng)
    ok=wrong=0; ms=[]; fails=Counter(); fb=0; times=[]
    for T in Ts:
        t0=time.time(); sol,info,m,tries=run(T); times.append(time.time()-t0)
        if tries==-1: fb+=1
        if sol is None: fails[info]+=1; continue
        if sum(sol)==T and not (Counter(sol)-Counter(W)): ok+=1; ms.append(m)
        else: wrong+=1
    print(f"{mode:3s} RHO={RHO:<7g} CAP={CAP:<3d} {name:28s} o={omicron(W):9.3g} prep {tp:6.3f}s  found {ok:2d}/{len(Ts)} wrong {wrong}  ms/target {1e3*sum(times)/len(Ts):9.2f}  endgame m {(sum(ms)/len(ms) if ms else 0):5.1f}  fallbacks {fb}  {dict(fails)}",flush=True)
if __name__=="__main__": _main()
