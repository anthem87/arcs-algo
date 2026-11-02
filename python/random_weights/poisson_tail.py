# Is the endgame count quasi-Poisson?  Empirical P(Z(u)=0 | S_E ~ s) vs e^{-F(s)} (exact F) vs Chebyshev Var/F^2 (exact)
import numpy as np, itertools, time, signal
from math import comb, sqrt, exp
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h); signal.alarm(55); t0=time.time()
M=64; mu=(M+1)/2; sg=sqrt((M*M-1)/12); rng=np.random.default_rng(5)
def exact(m,u,s):
    N=m*M+1; P=[np.zeros(N) for _ in range(m+1)]; P[0][0]=1; one=np.zeros(M+1); one[1:]=1/M
    for k in range(1,m+1): P[k]=np.convolve(P[k-1],one)[:N]
    def num(j,v,t):
        a2=t+v
        if a2%2: return 0.0
        a=a2//2; b=t-a
        if a<0 or b<0 or a>=N or b>=N: return 0.0
        return sum(comb(j,i)*P[i][a]*P[j-i][b] for i in range(j+1))
    F=num(m,u,s)/P[m][s]
    return F
try:
  for m in [9,10,11,12]:
    eps=np.array(list(itertools.product([1,-1],repeat=m)),dtype=np.int32)
    s0=int(round(m*mu)); u=2 if s0%2==0 else 3
    F=exact(m,u,s0)
    zeros=0; n=0
    while n<60000 and time.time()-t0<50:
        W=rng.integers(1,M+1,(m,20000)).astype(np.int32); SE=W.sum(0)
        sel=np.abs(SE-s0)<=1                       # S_E in {s0-1,s0,s0+1}; keep right parity
        sel&=((SE-u)%2==0); W=W[:,sel]
        if W.shape[1]==0: continue
        Z=((eps@W)==u).sum(0); zeros+=int((Z==0).sum()); n+=Z.size
    p=zeros/n
    print(f"m={m}: F(s0)={F:6.2f}  empirical P(Z=0|S_E=s0) = {p:.5f} (n={n})   e^-F = {exp(-F):.5f}   [{time.time()-t0:.0f}s]",flush=True)
except TimeoutError: print("-- timeout --")
