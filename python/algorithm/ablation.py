import random, math, time, signal
from collections import Counter
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'deblur.py')).read().split("random.seed(21)")[0])
from hurs_arcs import mitm
class TO(Exception): pass
def _h(*a): raise TO()
signal.signal(signal.SIGALRM,_h)
def run(B,T,use_arcs,RHO=50.0,CAP=46):
    lab=B.lab; out=[]
    orig=[x for x,d in lab if d==0]; Ssuf=[0]*(len(orig)+1)
    for i in range(len(orig)-1,-1,-1): Ssuf[i]=Ssuf[i+1]+orig[i]
    i=0
    for k,(w,dm) in enumerate(lab):
        if dm: continue
        r=B.score(k,T)
        if r==-math.inf: return None
        _,m,v=r
        if m<=CAP and m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest=mitm(orig[i:],T); return None if rest is None else out+rest
        if use_arcs:
            si=B.score(k+1,T-w); so=B.score(k+1,T)
            si=si[0] if isinstance(si,tuple) else si; so=so[0] if isinstance(so,tuple) else so
            take = si>=so if (si!=-math.inf or so!=-math.inf) else None
            if take is None: return None
        else:                                   # no arcs: keep the residue closest to the centre of the remaining block
            c=Ssuf[i+1]/2; take = abs((T-w)-c) <= abs(T-c) and T-w>=0
        if take: out.append(w); T-=w
        i+=1
    return out if T==0 else None
random.seed(3)
cases=[("200 random in [1,1e10]",[random.randint(1,10**10) for _ in range(200)],None),
       ("almost-divisor: 198×(3k)+2 in [1,3e9]",[3*random.randint(1,10**9) for _ in range(198)]+[random.randint(1,3*10**9) for _ in range(2)],None),
       ("almost-divisor: 195×(7k)+5 in [1,7e9]",[7*random.randint(1,10**9) for _ in range(195)]+[random.randint(1,7*10**9) for _ in range(5)],None)]
print(f"{'instance':40s}{'arcs':>10}{'no arcs (centre)':>18}")
for name,W,_ in cases:
    signal.alarm(60)
    try:
        B=Deblurred(W); S=sum(W); s=math.sqrt(sum(x*x for x in W)/4)
        Ts=[]
        while len(Ts)<12:                         # planted targets (reachable by construction)
            Ts.append(sum(w for w in W if random.random()<0.5))
        a=sum((lambda x: x is not None and sum(x)==T)(run(B,T,True)) for T in Ts)
        b=sum((lambda x: x is not None and sum(x)==T)(run(B,T,False)) for T in Ts)
        print(f"{name:40s}{a:>7}/12{b:>15}/12",flush=True)
    except TO: print(f"{name:40s}  -- timeout 60 s --",flush=True)
    signal.alarm(0)
