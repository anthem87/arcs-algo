"""Suffix class counts (paper §5.4) N_c(q) of the ORIGINAL weights in floating point.
   The recursion N_c <- N_c + N_{c-w} adds non-negative numbers only: no cancellation, relative error <= n*eps,
   and a zero stays an exact zero (a sum of non-negatives is 0 iff both terms are 0). Each row is rescaled by a power
   of two (exact), its exponent kept apart. Counts are integers in [1, 2^n] when positive, so for n <= 1020 no positive
   entry can underflow after rescaling by the row maximum. No big integers, no dummies, no de-blurring
   (the de-blurred scores coincide with the scores on the originals, paper section 5.4)."""
import numpy as np, math
Q=24
class ArcsF:
    def __init__(self,W,Q=Q):
        W=list(W); n=len(W); assert n<=1020, "use log-domain beyond n=1020"   # 2^-1020 is still a normal double
        self.W=W; self.n=n; self.Q=Q
        self.S=[0]*(n+1); self.V=[0.0]*(n+1)
        for k in range(n-1,-1,-1): self.S[k]=self.S[k+1]+W[k]; self.V[k]=self.V[k+1]+W[k]*W[k]/4
        qs=list(range(2,Q+1)); off=np.concatenate([[0],np.cumsum(qs)]).astype(np.int64); L=int(off[-1])
        qof=np.concatenate([[q]*q for q in qs]).astype(np.int64); base=np.concatenate([off[i]*np.ones(q,np.int64) for i,q in enumerate(qs)])
        cls=np.arange(L)-base                       # class index c inside its modulus
        starts=off[:-1]
        N=np.zeros((n+1,L)); E=np.zeros((n+1,len(qs)),dtype=np.int64); N[n,starts]=1.0
        for k in range(n-1,-1,-1):                 # all moduli at once: one gather per weight
            idx=base+(cls-W[k])%qof
            row=N[k+1]+N[k+1][idx]
            mx=np.maximum.reduceat(row,starts); e=np.frexp(mx)[1].astype(np.int64)
            N[k]=np.ldexp(row,-np.repeat(e,qs)); E[k]=E[k+1]+e
        self.N={q:N[:,off[i]:off[i+1]] for i,q in enumerate(qs)}
        self.E={q:E[:,i] for i,q in enumerate(qs)}
        self.LN2=math.log(2)
    def logclass(self,k,q,c):                     # log(q*N_c) - m log 2, or -inf if the class is empty
        x=self.N[q][k,c]
        if x==0.0: return -math.inf
        return math.log(q)+math.log(x)+(int(self.E[q][k])-(self.n-k))*self.LN2
    def score(self,k,T):
        S=self.S[k]; m=self.n-k
        if T<0 or T>S: return -math.inf
        if m==0: return (0.0,0,0.0) if T==0 else -math.inf
        best=0.0
        for q in range(2,self.Q+1):
            l=self.logclass(k,q,T%q)
            if l==-math.inf: return -math.inf
            if l>best: best=l
        v=self.V[k]
        return m*self.LN2-0.5*math.log(2*math.pi*v)-(T-S/2)**2/(2*v)+best, m, v
