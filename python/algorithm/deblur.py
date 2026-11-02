"""Arcs traced on W ∪ D (o <= 1), dummies never read: the score uses the de-blurred counts.
   Gaussian part: cumulants of W = cumulants of W∪D minus those of the dummies (the blur is an independent sum).
   Class part: N^{W∪D}(x) = N^W(x) * prod_D (1 + x^{d mod q})  in Z[x]/(x^q - 1);  divide out each dummy factor exactly.
   A factor (1 + x^s) is invertible iff the cycle length q/gcd(q,s) is odd; otherwise those frequencies are killed by the dummy."""
import random, math, time
from math import gcd
from collections import Counter
import hurs_arcs
from hurs_arcs import Arcs, augment, omicron
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'pure2.py')).read().split("print(f\"{'n'")[0])
Q=24
def div_factor(c,s,q):                        # solve y_i + y_{i-s} = c_i in Z[x]/(x^q-1); None if (1+x^s) not invertible
    s%=q
    if s==0: return [v//2 for v in c] if all(v%2==0 for v in c) else None
    g=gcd(q,s); L=q//g
    if L%2==0: return None
    y=[0]*q
    for i0 in range(g):
        p=[(i0+j*s)%q for j in range(L)]
        alt=sum(((-1)**j)*c[p[j]] for j in range(L))      # = 2*y[p[L-1]]
        if alt%2: return None
        y[p[L-1]]=alt//2
        for j in range(L-1): y[p[j]]=c[p[j]]-y[p[j-1]] if j>0 else c[p[0]]-y[p[L-1]]
    return y
class Deblurred:
    def __init__(self,W):
        D=augment(W); lab=sorted([(w,0) for w in W]+[(d,1) for d in D],reverse=True)
        self.lab=lab; self.Wp=[x for x,_ in lab]; self.isd=[d for _,d in lab]
        self.A=Arcs(self.Wp)                       # arcs traced on W ∪ D
        n=len(lab); self.Dsum=[0]*(n+1); self.Dsq=[0]*(n+1); self.Dlist=[[] for _ in range(n+1)]
        for k in range(n-1,-1,-1):
            w,dm=lab[k]; self.Dsum[k]=self.Dsum[k+1]+(w if dm else 0); self.Dsq[k]=self.Dsq[k+1]+(w*w if dm else 0)
            self.Dlist[k]=self.Dlist[k+1]+([w] if dm else [])
        self.killed=set(); self.cache={}
        self.Wonly=Arcs([x for x,d in lab if d==0])   # used ONLY for frequencies killed by the dummies (and to cross-check)
        self.orig_index=[]; c=0
        for k in range(n+1):
            self.orig_index.append(c)
            if k<n and lab[k][1]==0: c+=1
    def NW(self,k,q):                            # class counts of the ORIGINALS in suffix k, from W∪D arcs by exact de-blurring
        key=(k,q)
        if key in self.cache: return self.cache[key]
        c=list(self.A.N[q][k])
        for d in self.Dlist[k]:
            c=div_factor(c,d,q)
            if c is None: break
        if c is None:
            self.killed.add(q); c=self.Wonly.N[q][self.orig_index[k]]
        self.cache[key]=c; return c
    def score(self,k,T):                         # log of the de-blurred count estimate for originals in suffix k
        S=self.A.S[k]-self.Dsum[k]; m=sum(1 for j in range(k,len(self.lab)) if self.lab[j][1]==0)
        if T<0 or T>S: return -math.inf
        if m==0: return 0.0 if T==0 else -math.inf
        best=0.0
        for q in range(2,Q+1):
            Nc=self.NW(k,q)[T%q]
            if Nc==0: return -math.inf
            best=max(best, math.log(q*Nc)-m*math.log(2))
        v=self.A.V[k]-self.Dsq[k]/4               # de-blurred variance
        return m*math.log(2)-0.5*math.log(2*math.pi*v)-(T-S/2)**2/(2*v)+best, m, v
def solve(B,T,RHO=50.0):
    lab=B.lab; out=[]
    for k,(w,dm) in enumerate(lab):
        if dm: continue                            # never read a dummy
        r=B.score(k,T)
        if r==-math.inf: return None
        _,m,v=r
        if m*math.log(2)-0.5*math.log(2*math.pi*max(v,1))<math.log(RHO):
            rest=full_spectrum_tail([x for x,d in lab[k:] if d==0],T); return None if rest is None else out+rest
        si=B.score(k+1,T-w); so=B.score(k+1,T)
        si=si[0] if si!=-math.inf else si; so=so[0] if so!=-math.inf else so
        if si==-math.inf and so==-math.inf: return None
        if si>=so: out.append(w); T-=w
    return out if T==0 else None
random.seed(21)
print(f"{'instance':16s}{'o(W)':>6}{'dummies':>8}{'found':>8}{'max |score diff| vs arcs on originals':>40}{'q killed by dummies':>22}")
for name,W in [("60 in [1,2000]",[random.randint(1,2000) for _ in range(60)]),
               ("40 in [1,1e4]",[random.randint(1,10**4) for _ in range(40)]),
               ("30 in [1,1e5]",[random.randint(1,10**5) for _ in range(30)])]:
    B=Deblurred(W); S=sum(W); R=1
    for w in W: R|=R<<w
    reach=[t for t in range(S+1) if (R>>t)&1]; Ts=random.sample(reach,150)
    ok=sum((lambda s: s is not None and sum(s)==T and not (Counter(s)-Counter(W)))(solve(B,T)) for T in Ts)
    # cross-check: de-blurred class counts equal the originals' counts on non-killed q
    diff=0
    for k in range(len(B.lab)):
        for q in range(2,Q+1):
            if q in B.killed: continue
            if B.NW(k,q)!=B.Wonly.N[q][B.orig_index[k]]: diff+=1
    print(f"{name:16s}{omicron(W):6.0f}{len(augment(W)):8d}{100*ok/150:7.1f}%{('exact (0 mismatches)' if diff==0 else str(diff)+' mismatches'):>40}{str(sorted(B.killed)):>22}",flush=True)
