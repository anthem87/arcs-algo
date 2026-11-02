# Lemma B check: Z(u) = #{eps in {+-1}^m : sum eps_i w_i = u}, w_i iid uniform{1..M}; all |u| <= M of the parity of S_E
import numpy as np, time, signal
signal.signal(signal.SIGALRM, lambda *a: (_ for _ in ()).throw(TimeoutError())); signal.alarm(55)
rng=np.random.default_rng(3); t0=time.time()
def signed_sums(w):
    s=np.zeros(1,dtype=np.int64)
    for x in w: s=np.concatenate((s+x,s-x))
    return s
for m,b in [(20,10),(22,12),(24,14)]:
    M=2**b; cM=1/3+1/(2*M)+1/(6*M*M); rho=2**(m+1)/(M*np.sqrt(2*np.pi*m*cM))
    mins=[];means=[];zero=0;inst=0
    try:
        while inst<60:
            w=rng.integers(1,M+1,m); s=signed_sums(w); SE=int(w.sum())
            off=int(np.abs(s).max()); cnt=np.bincount(s+off)
            u=np.arange(-M,M+1); u=u[(u-SE)%2==0]
            z=cnt[u+off]; mins.append(z.min()/rho); means.append(z.mean()/rho); zero+=int((z==0).any()); inst+=1
    except TimeoutError: pass
    print(f"m={m} M=2^{b} rho={rho:.0f}: instances {inst}, mean Z/rho over |u|<=M = {np.mean(means):.3f}, worst min_u Z/rho = {min(mins):.3f}, instances with some empty u: {zero}  [{time.time()-t0:.0f}s]",flush=True)
