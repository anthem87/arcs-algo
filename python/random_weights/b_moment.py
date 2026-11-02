# Second-moment constant: E[Z(u)^2]/E[Z(u)]^2 - 1 - 1/E[Z]  vs  1/(5m)   (unconditional on S_E, right parity only)
import numpy as np, time, signal
signal.alarm(55); rng=np.random.default_rng(7); t0=time.time()
def sums(w):
    s=np.zeros(1,dtype=np.int64)
    for x in w: s=np.concatenate((s+x,s-x))
    return s
for m,M,N in [(12,2**5,40000),(16,2**7,20000)]:
    us=[10,12,40]; Z={u:[] for u in us}
    try:
        for _ in range(N):
            w=rng.integers(1,M+1,m)
            if w.sum()%2: continue
            s=sums(w)
            for u in us: Z[u].append(int(np.count_nonzero(s==u)))
    except Exception: pass
    for u in us:
        z=np.array(Z[u],float); F=z.mean(); ex=(z**2).mean()/F**2-1-1/F
        se=np.std((z/F)**2)/np.sqrt(len(z))
        print(f"m={m} M={M} u={u}: n={len(z)} E Z={F:.1f}  excess={ex:.4f} +- {se:.4f}   1/(5m)={1/(5*m):.4f}  [{time.time()-t0:.0f}s]",flush=True)
