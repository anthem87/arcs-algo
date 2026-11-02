import random, math, time
from collections import Counter
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'deblur.py')).read().split("random.seed(21)")[0])
from hurs_arcs import mitm
def solve_big(B,T,RHO,CAP=46):
    lab=B.lab; out=[]
    for k,(w,dm) in enumerate(lab):
        if dm: continue
        r=B.score(k,T)
        if r==-math.inf: return None,'scored-out',0
        _,m,v=r
        if m<=CAP and m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest=mitm([x for x,d in lab[k:] if d==0],T)          # exact finish (meet-in-the-middle) on the originals left
            return (None,'endgame-no',m) if rest is None else (out+rest,'ok',m)
        si=B.score(k+1,T-w); so=B.score(k+1,T)
        si=si[0] if si!=-math.inf else si; so=so[0] if so!=-math.inf else so
        if si==-math.inf and so==-math.inf: return None,'both-out',0
        if si>=so: out.append(w); T-=w
    return (out,'ok',0) if T==0 else (None,'end',0)
random.seed(77)
cases=[("200 in [1,1e10]",[random.randint(1,10**10) for _ in range(200)],None),
       ("200 in [1,1e12]",[random.randint(1,10**12) for _ in range(200)],None),
       ("150 mult. of 7 in [1,7e11]",[7*random.randint(1,10**11) for _ in range(150)],7)]
print(f"{'instance':28s}{'o':>12}{'dummies':>8}{'DP table (n·S bits)':>21}{'prep[s]':>8}{'found (verified)':>18}{'wrong':>6}{'s/T':>7}{'endgame m':>10}")
for name,W,g in cases:
    S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
    t0=time.time(); B=Deblurred(W); tp=time.time()-t0
    Ts=[int(S//2+random.gauss(0,1)*s) for _ in range(12)]+[int(S//2+random.choice([-1,1])*random.uniform(2,4)*s) for _ in range(8)]
    if g: Ts=[T-T%g for T in Ts]
    ok=wrong=0; ms=[]; fails=Counter(); t0=time.time()
    for T in Ts:
        sol,info,m=solve_big(B,T,50.0)
        if sol is None: fails[info]+=1; continue
        if sum(sol)==T and not (Counter(sol)-Counter(W)): ok+=1; ms.append(m)
        else: wrong+=1
    dt=(time.time()-t0)/len(Ts)
    print(f"{name:28s}{omicron(W):12.3g}{len(augment(W)):8d}{len(W)*S:21.2e}{tp:8.2f}{ok:11d}/{len(Ts)}{'':4s}{wrong:6d}{dt:7.2f}{(sum(ms)/len(ms) if ms else 0):10.1f}  {dict(fails)}",flush=True)
