import numpy as np
from math import log
from sympy import primerange, divisors, mobius, totient, factorint
kap=2*1.0149416064096536/(2*np.pi)
best=None
for th in np.arange(0.5,0.96,0.01):
    lM=0.0
    for p in primerange(2,10**6):
        p=float(p)
        f=max(log(2)+a*th*log(p)-(a-1)*log(p)-log(p-1) for a in range(1,60))
        if f>0: lM+=f
        elif 2*p**th<p-1: break
    M=np.exp(lM)
    # g(q) <= M q^-th (1+log2+log q)/2 ; find Q0 beyond which < 0.1316 (g decreasing for large q)
    q=np.logspace(1,12,20000); g=M*q**(-th)*(1+log(2)+np.log(q))/2
    ok=np.nonzero(g>=0.1316)[0]; Q0=q[ok[-1]] if len(ok) else 10
    if best is None or Q0<best[0]: best=(Q0,th,M)
print(f"best: theta={best[1]:.2f}, M_theta={best[2]:.3f}, bound < 0.1316 for all q >= {best[0]:.0f}")
# tail X >= 4 for the 145 candidates: A_q(X) <= (kap/X) * sum_{d|q, mu!=0} 1/d  (all terms in the regime dX >= 1)
def emerging(q):
    if q==1: return True
    if q%2: return False
    return len(factorint(q//2))==1
cand=[q for q in range(3,2731) if not emerging(q)]
t=max((kap/4)*sum(1/d for d in divisors(q) if mobius(q//d)!=0)/int(totient(q)) for q in cand)
print(f"tail X>=4 over non-emerging q <= 2730: A_q/phi <= {t:.4f}")
