"""First version of the arc formula, superseded by arcform2.py; kept only because other scripts load it with exec.
   Run alone it prints meaningless predictions."""
import mpmath as mp, numpy as np, math
mp.mp.dps=90
def primes(n):
    s=np.ones(n+1,bool); s[:2]=False
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(p) for p in np.nonzero(s)[0]]
N=500; W=[1]+primes(N); n=len(W); S=sum(W)
r=[0]*(S+1); r[0]=1
for w in W:
    for t in range(S,w-1,-1): r[t]+=r[t-w]
print('n=%d S=%d  exact counts done, max r ~ 2^%.1f'%(n,S,math.log2(max(r))))
e=lambda x: mp.expj(2*mp.pi*x)
def arc(a,q):
    u=[e(mp.mpf(w*a)/q) for w in W]
    F=mp.fprod(1+x for x in u)
    m=mp.fsum(w*x/(1+x) for w,x in zip(W,u))
    v=mp.fsum(w*w*x/(1+x)**2 for w,x in zip(W,u))
    return F,m,v
H=mp.mpf(60)
for q,a in [(4,1),(6,1),(10,1),(10,3),(12,1),(14,1)]:
    F,m,v=arc(a,q)
    print('q=%d a=%d |F|/2^n=%s  m=%s  v=%s'%(q,a,mp.nstr(abs(F)/2**n,5),mp.nstr(m,6),mp.nstr(v,6)))
    for T0 in [S//2, S//2+150, S//2-400]:
        Y=mp.fsum(r[t]*e(mp.mpf(a*t)/q)*mp.exp(-(t-T0)**2/(2*H*H)) for t in range(max(0,T0-12*int(H)),min(S,T0+12*int(H))+1))
        P=mp.fsum(F*mp.exp(-(t-m)**2/(2*v))/mp.sqrt(2*mp.pi*v)*mp.exp(-(t-T0)**2/(2*H*H)) for t in range(max(0,T0-12*int(H)),min(S,T0+12*int(H))+1))
        print('    T0=%d  exact twisted window %s   predicted %s   ratio %s'%(T0,mp.nstr(Y,8),mp.nstr(P,8),mp.nstr(Y/P,8)))
