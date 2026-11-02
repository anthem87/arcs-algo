import numpy as np, math
from sympy import factorint, totient
from math import gcd
def logPhi_direct(q,x):
    return sum(np.log(np.abs(2*np.cos(np.pi*(r/q+x)))) for r in range(1,q+1) if gcd(r,q)==1)
def closed(q,x):
    f=factorint(q//2) if q%2==0 else {}
    if q>=4 and (q & (q-1))==0: return np.log(np.abs(2*np.cos(np.pi*q*x/2)))
    (p,j),=f.items(); th=np.pi*p**(j-1)*x
    return np.log(np.abs(np.sin(p*th)/np.sin(th)))
emerg=[q for q in range(4,401) if q%2==0 and (len(factorint(q//2))==1)]
x=np.linspace(1e-4,1.0,20011)+1e-7
err=max(np.max(np.abs(logPhi_direct(q,x)-closed(q,x))) for q in emerg[:40])
print("identity |Phi_q(-e(x))| closed form, max abs error (first 40 emerging q):",f"{err:.1e}")
# margin c_q - l_q for emerging q up to 4000 using the closed form (exact averages on a fine grid)
worst=(1e9,None)
for q in [q for q in range(4,4001) if q%2==0 and len(factorint(q//2))==1]:
    lam=math.log(list(factorint(q//2).keys())[0]); phi=int(totient(q))
    K=max(20000,40*q); X=(np.arange(K)+1)/K*6; xs=(np.arange(K)+0.5)/K*6
    f=closed(q,xs); A=np.cumsum(f)*(6/K)/X
    assert f.max()<=lam+1e-9                      # maximum principle: |Phi_q(-e(x))| <= Phi_q(-1)
    d=np.diff(A); i0=np.argmax(d>0); lq=A[i0:].max()
    m=(lam-lq)/phi
    if m<worst[0]: worst=(m,q)
print("min over emerging q<=4000 of (c_q - l_q):",f"{worst[0]:.4f} at q={worst[1]}; maximum principle holds for all")
