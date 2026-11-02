import numpy as np
from sympy import primerange, totient
from math import gcd, log
N=1000
P=np.array(list(primerange(2,N+1)),dtype=float); L2=log(2)
def logPhi(q,x):
    rs=[r for r in range(1,q+1) if gcd(r,q)==1] if q>1 else [0]
    return sum(np.log(np.abs(2*np.cos(np.pi*(r/q+x)))) for r in rs)
def curve(q,Xmax=8,K=80000):
    x=(np.arange(K)+0.5)/K*Xmax; X=(np.arange(K)+1)/K*Xmax
    return X,np.cumsum(logPhi(q,x))*(Xmax/K)/X
print(" q  emerg  centre   lobe(after 1st min)  X_lobe  lobe<centre?")
rows=[]
for q in range(1,61):
    if q==2: continue
    phi=1 if q==1 else int(totient(q))
    X,A=curve(q); A=A/phi
    c=A[0]
    # first local minimum index
    d=np.diff(A); i0=np.argmax(d>0)  # first place curve rises
    j=i0+np.argmax(A[i0:]); l=A[j]
    em = q==1 or (q%2==0 and c>1e-6)
    rows.append((q,em,c,l,X[j]))
    if q<=16 or em: print(f"{q:3d}  {str(em):5s} {c:8.4f}  {l:8.4f}  {X[j]:7.3f}   {l<c}")
non=[r for r in rows if not r[1]]
print("max lobe over NON-emerging q<=60:", max(non,key=lambda r:r[3])[:5:2], max(r[3] for r in non))
print("max lobe/centre over emerging:", max(r[3]-r[2] for r in rows if r[1]))
# measured at N=1000: q=1 lobe near X=4/3, q=3 lobe
def ell(th): return np.mean(np.log(np.abs(np.cos(np.pi*P[None,:]*th[:,None]))),axis=1)+L2
for q,a,X0 in [(1,0,4/3),(3,1,None)]:
    phi=1 if q==1 else 2
    X,A=curve(q); A=A/phi
    d=np.diff(A); i0=np.argmax(d>0); j=i0+np.argmax(A[i0:])
    Xs=np.linspace(max(X[i0]-.2,0.05),X[j]+1.5,3000); m=ell(a/q+Xs/N)
    k=np.argmax(np.where(Xs>X[i0],m,-9))
    print(f"q={q}: theory lobe {A[j]:.4f} at X={X[j]:.3f} | measured N=1000: {m[k]:.4f} at X={Xs[k]:.3f}")
