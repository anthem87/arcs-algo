# E2(N) = sum_{p<=N} p^2 - li(N^3), normalized by N^{5/2}/... ; RH predicts E2 = O(N^{5/2} log N)
import numpy as np, mpmath as mp, time
mp.mp.dps=30
t0=time.time(); X=10**8
s=np.ones(X//2+1,bool); s[0]=False
for i in range(1,int(X**.5)//2+1):
    if s[i]: p=2*i+1; s[p*p//2::p]=False
P=np.concatenate(([2],2*np.nonzero(s)[0]+1)).astype(np.float64)
C=np.cumsum(P*P)
out=[]
for N in np.unique(np.logspace(2,8,25).astype(np.int64)):
    k=np.searchsorted(P,N,side='right'); M2=C[k-1]
    E=M2-float(mp.li(mp.mpf(int(N))**3)-mp.li(8))
    out.append((N,E/(N**2.5),E/(N**2.5*np.log(N))))
for r in out: print(f"N={r[0]:>10d}  E2/N^2.5 = {r[1]:+.4f}   E2/(N^2.5 log N) = {r[2]:+.5f}")
print(f"[{time.time()-t0:.0f}s]")
