# Conditional second moment: excess E[Z^2|S_E~s]/E[Z|S_E~s]^2 - 1 - 1/E[Z]  vs  kappa_cond/m = 1/(80m), unconditional 1/(5m)
import numpy as np, itertools, time, signal
def _h(*a): raise TimeoutError
signal.signal(signal.SIGALRM,_h); signal.alarm(50); t0=time.time(); rng=np.random.default_rng(11)
m,M=12,32
eps=np.array(list(itertools.product([1,-1],repeat=m)),dtype=np.int32)       # 4096 x m
mu=(M+1)/2; sd=np.sqrt(m*(M*M-1)/12); us=[10,12,20]
acc={u:{'all':[], 'bin':[]} for u in us}
try:
    while True:
        W=rng.integers(1,M+1,(m,20000)).astype(np.int32); SE=W.sum(0)
        ok=SE%2==0; W=W[:,ok]; SE=SE[ok]; S=eps@W
        inbin=np.abs(SE-m*mu)<=0.15*sd
        for u in us:
            z=(S==u).sum(0); acc[u]['all'].append(z); acc[u]['bin'].append(z[inbin])
except Exception: pass
for u in us:
    for key in ['all','bin']:
        z=np.concatenate(acc[u][key]).astype(float); F=z.mean(); ex=(z**2).mean()/F**2-1-1/F
        se=np.std((z/F)**2)/np.sqrt(len(z))
        print(f"u={u} {key:3s}: n={len(z):7d} EZ={F:6.1f} excess={ex:+.5f} +- {se:.5f}   (1/(5m)={1/(5*m):.5f}, 1/(80m)={1/(80*m):.5f})")
print(f"[{time.time()-t0:.0f}s]")
