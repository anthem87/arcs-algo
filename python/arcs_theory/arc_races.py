import numpy as np, math
X=10**8
sv=np.ones(X//2+1,dtype=np.bool_); sv[0]=False
for i in range(1,int(math.isqrt(X))//2+1):
    if sv[i]: p=2*i+1; sv[p*p//2::p]=False
pr=np.concatenate(([2],2*np.nonzero(sv)[0]+1)); del sv
for q,a in [(14,1),(10,1),(8,1),(6,1),(18,1),(22,1)]:
    G=[r for r in range(1,q) if math.gcd(r,q)==1]
    w={r:math.log(abs(math.cos(math.pi*a*r/q))) for r in G}; wb=np.mean(list(w.values()))
    c={r:w[r]-wb for r in G}
    cop=np.gcd(pr,q)==1; pp=pr[cop]; cs=np.cumsum(np.array([c[r] for r in pp%q]))
    us=np.linspace(math.log(1e4),math.log(1e8),3000); v=[]
    for u in us:
        k=np.searchsorted(pp,math.exp(u),side='right'); v.append(cs[k-1]*u/math.exp(u/2))
    v=np.array(v)
    sym=all(abs(c[r]-c[q-r])<1e-12 for r in G)
    print('q=%2d a=%d  w̄=%.4f  weights symmetric r↔-r: %s   race/(√N/logN): min %.3f max %.3f mean %.3f  (all equal weights: %s)'%(q,a,wb,sym,v.min(),v.max(),v.mean(),max(abs(x) for x in c.values())<1e-12))
