"""Dynamic set of moduli Q(k) for the arc scores.
   Candidates: q = 2..Q0, plus the divisors (<= DCAP) of gcds of random pairs of weights (almost divisors).
   For every candidate q and suffix k the class counts N_c(q) are computed in floating point (as arcs_float),
   and the deviation  delta_q(k) = max_c |q N_c / 2^m - 1|  is stored.
   Selection: q is read at suffix k iff delta_q(k) >= eps_k = min(1, C_EPS/m_k).
   Pruning lemma: an empty class gives delta = 1 >= eps, so no obstruction is ever skipped; a skipped modulus
   would have changed the score by at most log(1+eps_k)."""
import numpy as np, math, random
from math import gcd
def _divisors(g,cap):
    out=set(); i=1
    while i*i<=g:
        if g%i==0:
            if 1<i<=cap: out.add(i)
            j=g//i
            if 1<j<=cap: out.add(j)
        i+=1
    return out
def class_counts(W,qs):
    """N[i] has shape (n+1, qs[i]) (rescaled rows), E[i] the exponents; all moduli at once."""
    n=len(W); qs=list(qs); off=np.concatenate([[0],np.cumsum(qs)]).astype(np.int64); L=int(off[-1])
    qof=np.concatenate([[q]*q for q in qs]).astype(np.int64)
    base=np.concatenate([np.full(q,off[i],np.int64) for i,q in enumerate(qs)]); cls=np.arange(L)-base; starts=off[:-1]
    N=np.zeros((n+1,L)); E=np.zeros((n+1,len(qs)),dtype=np.int64); N[n,starts]=1.0
    for k in range(n-1,-1,-1):
        row=N[k+1]+N[k+1][base+(cls-W[k])%qof]
        e=np.frexp(np.maximum.reduceat(row,starts))[1].astype(np.int64)
        N[k]=np.ldexp(row,-np.repeat(e,qs)); E[k]=E[k+1]+e
    return N,E,off
class ArcsDyn:
    def __init__(self,W,Q0=24,DCAP=2000,PAIRS=64,C_EPS=1.0,seed=0,fixed=None):
        W=list(W); n=len(W); assert n<=1020   # positive counts lie in [1,2^n]; 2^-1020 is still a normal double
        self.W=W; self.n=n; self.LN2=math.log(2)
        self.S=[0]*(n+1); self.V=[0.0]*(n+1)
        for k in range(n-1,-1,-1): self.S[k]=self.S[k+1]+W[k]; self.V[k]=self.V[k+1]+W[k]*W[k]/4
        if fixed is not None: cand=sorted(set(fixed))
        else:
            cand=set(range(2,Q0+1)); rng=random.Random(seed)
            for _ in range(PAIRS if n>=2 else 0):      # no pairs on a one-weight instance
                a,b=rng.sample(W,2); g=gcd(a,b)
                if g>1: cand|=_divisors(g,DCAP)
            cand=sorted(cand)
        self.cand=cand
        if not cand: self.sel=[[] for _ in range(n+1)]; self.N={}; self.E={}; return
        N,E,off=class_counts(W,cand)
        self.N={q:N[:,off[i]:off[i+1]] for i,q in enumerate(cand)}; self.E={q:E[:,i] for i,q in enumerate(cand)}
        self.sel=[]; self.C_EPS=C_EPS
        for k in range(n+1):
            m=n-k; eps=1.0 if m==0 else min(1.0,C_EPS/m) if fixed is None or C_EPS>0 else 0.0
            s=[]
            for q in cand:
                row=self.N[q][k]; sc=float(q)*np.ldexp(1.0,int(self.E[q][k])-m)
                dev=float(np.max(np.abs(row*sc-1.0)))
                if fixed is not None and C_EPS==0: s.append(q)
                elif dev>=eps: s.append(q)
            self.sel.append(s)
    def score(self,k,T):
        S=self.S[k]; m=self.n-k
        if T<0 or T>S: return -math.inf
        if m==0: return (0.0,0,0.0) if T==0 else -math.inf
        best=0.0
        for q in self.sel[k]:
            x=self.N[q][k,T%q]
            if x==0.0: return -math.inf
            l=math.log(q)+math.log(x)+(int(self.E[q][k])-m)*self.LN2
            if l>best: best=l
        v=self.V[k]
        return m*self.LN2-0.5*math.log(2*math.pi*v)-(T-S/2)**2/(2*v)+best, m, v
