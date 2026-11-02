import random, math, time, sys
from collections import Counter
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'deblur.py')).read().split("random.seed(21)")[0])
def solve_r(B,T,RHO):
    lab=B.lab; out=[]
    for k,(w,dm) in enumerate(lab):
        if dm: continue
        r=B.score(k,T)
        if r==-math.inf: return None,('scored-out',k)
        _,m,v=r
        if m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest=full_spectrum_tail([x for x,d in lab[k:] if d==0],T)
            return (None,('endgame-no',m)) if rest is None else (out+rest,('ok',m))
        si=B.score(k+1,T-w); so=B.score(k+1,T)
        si=si[0] if si!=-math.inf else si; so=so[0] if so!=-math.inf else so
        if si==-math.inf and so==-math.inf: return None,('both-out',k)
        if si>=so: out.append(w); T-=w
    return (out,('ok',0)) if T==0 else (None,('end',0))
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
inst=[("40 in [1,1e4]",40,10**4),("30 in [1,1e5]",30,10**5),("60 in [1,1e5]",60,10**5),
      ("100 in [1,1e5]",100,10**5),("150 in [1,1e6]",150,10**6),("200 in [1,1e6]",200,10**6)]
print(f"{'instance':15s}{'o':>7}{'dum':>4}{'S':>11}{'DP [s]':>8}{'prep [s]':>9} {'λ*':>5}{'found':>8}{'wrong':>6}{'ms/T':>8}{'endgame m':>10}  failures")
for name,n,wm in inst:
    W=[random.randint(1,wm) for _ in range(n)]; S=sum(W)
    t0=time.time(); R=1
    for w in W: R|=R<<w
    tdp=time.time()-t0
    Ts=[]
    while len(Ts)<200:
        t=random.randint(0,S)
        if (R>>t)&1: Ts.append(t)
    t0=time.time(); B=Deblurred(W); tp=time.time()-t0
    for RHO in (50.0,500.0):
        ok=wrong=0; fails=Counter(); ms=[]; t0=time.time()
        for T in Ts:
            s,info=solve_r(B,T,RHO)
            if s is None: fails[info[0]]+=1; continue
            if sum(s)==T and not (Counter(s)-Counter(W)): ok+=1; ms.append(info[1])
            else: wrong+=1
        dt=(time.time()-t0)/len(Ts)*1e3
        print(f"{name:15s}{omicron(W):7.0f}{len(augment(W)):4d}{S:11d}{tdp:8.2f}{tp:9.2f} {RHO:5.0f}{100*ok/200:7.1f}%{wrong:6d}{dt:8.1f}{(sum(ms)/len(ms) if ms else 0):10.1f}  {dict(fails)}",flush=True)
