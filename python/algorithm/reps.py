import random, math, time, signal, itertools, cmath
import numpy as np
from sympy import nextprime
class TO(Exception): pass
def _h(*a): raise TO()
signal.signal(signal.SIGALRM,_h)
def instance(n,seed):
    rnd=random.Random(seed); a=[rnd.randrange(1,2**n) for _ in range(n)]
    idx=rnd.sample(range(n),n//2); T=sum(a[i] for i in idx); return a,T,set(idx)
def mitm_full(a,T):
    h=len(a)//2; A,B=a[:h],a[h:]
    def sums(ws):
        s=np.zeros(1,np.int64)
        for w in ws: s=np.concatenate([s,s+w])
        return s
    sa,sb=sums(A),sums(B); ob=np.argsort(sb); sbs=sb[ob]; need=T-sa
    pos=np.minimum(np.searchsorted(sbs,need),len(sbs)-1); hit=np.flatnonzero(sbs[pos]==need)
    return len(hit)>0, len(sa)+len(sb)
def half_list(a,I,k,M,c,rng):
    """y supported in I with |y| = k, a.y ≡ c (mod M): split I in two, enumerate k/2 + k/2, join on residue."""
    I=list(I); rng.shuffle(I); I1,I2=I[:len(I)//2],I[len(I)//2:]
    d={}
    ops=0
    for comb in itertools.combinations(I1,k//2):
        s=sum(a[i] for i in comb); d.setdefault(s%M,[]).append((s,comb)); ops+=1
    out=[]
    for comb in itertools.combinations(I2,k-k//2):
        s=sum(a[i] for i in comb); ops+=1
        for s1,c1 in d.get((c-s)%M,()): out.append((s1+s,c1+comb))
    return out,ops
def reps(a,T,tries=200):
    n=len(a); k=n//4
    R=math.comb(n//2,n//4)                          # representations x = y + z, |y|=|z|=n/4
    M=nextprime(max(3,R//8))
    rng=random.Random(1); ops=0
    for t in range(tries):
        c=rng.randrange(M)
        L1,o1=half_list(a,range(n),k,M,c,rng); L2,o2=half_list(a,range(n),k,M,(T-c)%M,rng); ops+=o1+o2
        d={}
        for s,cm in L2: d.setdefault(s,[]).append(set(cm))
        for s,cm in L1:
            for z in d.get(T-s,()):
                if not (z & set(cm)): return True,ops,t+1
        ops+=len(L1)+len(L2)
    return False,ops,tries
def arc_signal(a,Q=24):
    """largest normalized arc |F(e(a'/q))|/2^n over q<=Q, versus the random-sea expectation."""
    n=len(a); best=-1e9
    for q in range(2,Q+1):
        for aa in range(1,q):
            if math.gcd(aa,q)!=1: continue
            l=sum(math.log(abs(1+cmath.exp(2j*math.pi*aa*(w%q)/q))+1e-300) for w in a)-n*math.log(2)
            best=max(best,l)
    return best
print(f"{'n':>3}{'MITM ops':>12}{'reps ops':>12}{'reps tries':>11}{'log2 ops: MITM / reps':>24}{'max arc level (per weight)':>28}")
for n in (28,32,36,40,44):
    a,T,_=instance(n,n)
    row=[]
    for f in (mitm_full,reps):
        signal.alarm(60)
        try:
            r=f(a,T); row.append(r)
        except TO: row.append(None)
        signal.alarm(0)
    m=row[0]; r=row[1]
    ms=f"{m[1]:12d}" if m else "   timeout  "; rs=f"{r[1]:12d}{r[2]:11d}" if r else "     timeout          "
    lm=math.log2(m[1]) if m else float('nan'); lr=math.log2(r[1]) if r else float('nan')
    print(f"{n:3d}{ms}{rs}{lm:12.1f} / {lr:5.1f}{arc_signal(a)/n:+28.3f}",flush=True)
