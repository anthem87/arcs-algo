# Conditional (S_E at centre) moments of Z/F and the anatomy of the tail, M=64
import numpy as np, itertools, time, signal
from math import comb
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h); signal.alarm(55); t0=time.time()
M=64; mu=(M+1)/2; rng=np.random.default_rng(21)
try:
  for m in [10,11,12,13]:
    eps=np.array(list(itertools.product([1,-1],repeat=m)),dtype=np.int32)
    s0=int(round(m*mu)); u=2 if s0%2==0 else 3
    Zs=[];odd=[];n=0
    while n<80000 and time.time()-t0<12*(m-9):
        W=rng.integers(1,M+1,(m,20000)).astype(np.int32); SE=W.sum(0)
        sel=(np.abs(SE-s0)<=1)&((SE-u)%2==0); W=W[:,sel]
        Zs.append(((eps@W)==u).sum(0)); odd.append((W%2).sum(0)); n+=W.shape[1]
    Z=np.concatenate(Zs).astype(float); O=np.concatenate(odd); F=Z.mean(); X=Z/F-1
    m2=(X**2).mean(); m4=(X**4).mean(); p0=(Z==0).mean()
    lowodd=O<=m//4
    print(f"m={m} n={len(Z)} F={F:.1f}: E X^2={m2:.4f} (2/F={2/F:.4f})  E X^4={m4:.5f} (3(2/F)^2={12/F**2:.5f})  P(Z=0)={p0:.5f}  Markov4 bound={m4:.5f}")
    print(f"      P(#odd<=m/4)={lowodd.mean():.4f};  P(Z=0 | #odd<=m/4)={(Z[lowodd]==0).mean():.4f};  P(Z=0 | #odd>m/4)={(Z[~lowodd]==0).mean():.6f}   [{time.time()-t0:.0f}s]",flush=True)
except TimeoutError: print("-- timeout --")
