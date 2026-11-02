import mpmath as mp, numpy as np, math
mp.mp.dps=90
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'arcform.py')).read().split("e=lambda")[0].split("mp.mp.dps=90")[1])
e=lambda x: mp.expj(2*mp.pi*x)
def arc(a,q):
    good=[];zero=[]
    for w in W:
        u=e(mp.mpf(w*a)/q)
        (zero if abs(1+u)<mp.mpf(10)**-40 else good).append((w,u))
    F=mp.fprod(1+u for w,u in good)
    m=mp.fsum(w*u/(1+u) for w,u in good)+mp.fsum(mp.mpf(w)/2 for w,u in zero)
    v=mp.fsum(w*w*u/(1+u)**2 for w,u in good)+mp.fsum(mp.mpf(w)**2/12 for w,u in zero)  # (1-e(wb)) ~ -2πi w b e(wb/2)(1+...)
    return F,m,v,[w for w,u in zero]
H=mp.mpf(60)
for q,a in [(8,1),(6,1),(10,1),(10,3),(4,1),(14,1)]:
    F,m,v,z=arc(a,q)
    k=len(z); C=F*mp.fprod(z) if z else F
    print('q=%d a=%d  vanishing weights %s  |F*|/2^n=%s'%(q,a,z,mp.nstr(abs(F)/2**n,5)))
    for T0 in [S//2, S//2+150, S//2-400]:
        rng=range(max(0,T0-12*int(H)),min(S,T0+12*int(H))+1)
        Y=mp.fsum(r[t]*e(mp.mpf(a*t)/q)*mp.exp(-(t-T0)**2/(2*H*H)) for t in rng)
        G=lambda t: mp.exp(-(t-m)**2/(2*v))/mp.sqrt(2*mp.pi*v)
        if k==0: P=mp.fsum(F*G(t)*mp.exp(-(t-T0)**2/(2*H*H)) for t in rng)
        else:
            # k-th derivative of the complex Gaussian in T, times prod(w0)
            P=mp.fsum(C*mp.diff(G,t,k)*mp.exp(-(t-T0)**2/(2*H*H)) for t in rng)
        print('    T0=%d  exact %s  predicted %s  ratio %s'%(T0,mp.nstr(Y,7),mp.nstr(P,7),mp.nstr(Y/P,6)))
