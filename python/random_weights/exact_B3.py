# EXACT conditional second moment via the identity of Lemma B''' (exact distributions of S_k by convolution).
# Output: max over s in the window |s-m*mu|<=lam*sigma*sqrt(m) and over |u|<=M (right parity) of Var(Z(u)|S_E=s)/F^2,
# which bounds P(Z(u)=0 | S_E=s) by Chebyshev.   Usage: python3 exact_B3.py M lam m1 m2 [ustep]
import numpy as np, sys, time, signal
from math import comb, sqrt
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h); signal.alarm(55)
M=int(sys.argv[1]); lam=float(sys.argv[2]); m1,m2=int(sys.argv[3]),int(sys.argv[4]); ustep=int(sys.argv[5]) if len(sys.argv)>5 else 2
mu=(M+1)/2; sg=sqrt((M*M-1)/12); t0=time.time()
try:
  for m in range(m1,m2+1):
    N=m*M+1
    P=[np.zeros(N) for _ in range(m+1)]; P[0][0]=1.0; one=np.zeros(M+1); one[1:]=1.0/M
    for k in range(1,m+1): P[k]=np.convolve(P[k-1],one)[:N]
    def num(j,v):           # num_j(v,t) = sum_i C(j,i) P_i(a) P_{j-i}(t-a),  a=(t+v)/2
        out=np.zeros(N); t=np.arange(N); a2=t+v; ok=(a2%2==0)
        a=np.where(ok,a2//2,0); b=t-a; ok&=(a>=0)&(a<N)&(b>=0)
        a=np.clip(a,0,N-1); b=np.clip(b,0,N-1)
        for i in range(j+1): out+=comb(j,i)*np.where(ok,P[i][a]*P[j-i][b],0.0)
        return out
    N0=[num(j,0) for j in range(m+1)]
    worst=0; Fmin=np.inf; arg=None
    for u in range(0,M+1,ustep):
        Nu=[num(j,u) for j in range(m+1)]
        E2=np.zeros(N)
        for k in range(m+1): E2+=comb(m,k)*np.convolve(Nu[m-k],N0[k])[:N]
        s=np.arange(N); win=(np.abs(s-m*mu)<=lam*sg*sqrt(m))&((s-u)%2==0)&(P[m]>0)
        F=Nu[m][win]/P[m][win]; R=(E2[win]/P[m][win])/F**2-1
        if R.max()>worst: worst=R.max(); arg=(u,int(s[win][R.argmax()]))
        Fmin=min(Fmin,F.min())
    print(f"M={M} m={m}: min F={Fmin:8.2f}  max Var/F^2 = {worst:.4f} (at u,s={arg})  vs 2/Fmin={2/Fmin:.4f}  [{time.time()-t0:.0f}s]",flush=True)
except TimeoutError: print("-- timeout 55 s --")
