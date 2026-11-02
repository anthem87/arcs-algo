# Lemma Q: explicit lobe bound for non-emerging q, and numerical checks
import numpy as np, signal, time
from sympy import totient, divisors, mobius, factorint
from math import gcd, log, e
class TO(Exception): pass
signal.signal(signal.SIGALRM,lambda *a:(_ for _ in ()).throw(TO()))
kap=2*1.0149416064096536/(2*np.pi)           # Cl2(pi/3)/pi
def emerging(q):
    if q==1: return True
    if q%2: return False
    f=factorint(q//2); return len(f)==1 or q//2==1
def R(q):                                      # sup over X >= 1/(2q) of the bound (attained at X = 1/(2q))
    X=1/(2*q); s=0.0
    for d in divisors(q):
        m=mobius(q//d)
        if m==1: s+=min(log(2),kap/(d*X))
        elif m==-1:
            L=d*X; s+= kap/L if L>1 else min(kap/L,log(e/(2*L)))
    return s/int(totient(q))
def curve(q,Xmax=4.0):
    K=int(min(4e6,max(200000,400*q*Xmax)))
    x=(np.arange(K)+0.5)/K*Xmax; h=np.zeros(K)
    for d in divisors(q):                       # Moebius form: h = sum mu(q/d) log|2 sin pi(dx+d/2)|
        m=int(mobius(q//d))
        if m: h+=m*np.log(np.abs(2*np.sin(np.pi*(d*x+d/2))))
    X=(np.arange(K)+1)/K*Xmax; A=np.cumsum(h)*(Xmax/K)/X
    return X,A/int(totient(q))
lam=0.1316
signal.alarm(55); t0=time.time()
try:
    # 1) exhaustive bound R_q for q < 2*10^5; collect non-emerging q with R_q >= lam
    bad=[q for q in range(3,20001) if not emerging(q) and R(q)>=lam]
    print("non-emerging q <= 20000 with R_q >= 0.1316:",len(bad),"largest",max(bad),flush=True)
    print("  first ones:",bad[:30],flush=True)
    # 2) check first minimum X_q >= 1/(2q) and the true lobe level for the candidates and a sample
    worst=0; viol=[]; mx=(0,0)
    for q in sorted(set(bad)|set(range(3,121))):
        if emerging(q): continue
        X,A=curve(q); i0=np.argmax(np.diff(A)>0); Xq=X[i0]; l=A[i0:].max()
        if Xq<1/(2*q): viol.append(q)
        if l>mx[0]: mx=(l,q)
        worst=max(worst,l-R(q))
    print(f"checked {len(set(bad)|set(range(3,121)))} q: violations of X_q>=1/(2q): {viol}; max lobe {mx[0]:.4f} at q={mx[1]}; max(lobe - R_q) = {worst:.4f} (must be <= 0)  [{time.time()-t0:.0f}s]")
except TO: print("-- timeout 55 s --", time.time()-t0)
