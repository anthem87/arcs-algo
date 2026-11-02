import numpy as np, itertools, math
rng=np.random.default_rng(1); worst=0
for trial in range(2000):                       # Lemma A
    n=rng.integers(10,60); m=rng.integers(3,9); M=int(rng.integers(10,10**6))
    w=rng.integers(1,M+1,n); H,E=w[:n-m],w[n-m:]; S=w.sum(); SE=E.sum()
    T=int(S/2+rng.uniform(-1,1)*(H.sum()/2+H.max()/2))
    t=T; R=H.sum()
    for x in H:
        R-=x; c=(R+SE)/2
        t = t if abs(t-c)<=abs(t-x-c) else t-x
    worst=max(worst,abs(t-SE/2)/(H.max()/2))
print("Lemma A: max |t - S_E/2| / (w*/2) =",round(worst,4),"(must be <= 1)")
bad=0                                            # Lemma C(1) on small sets
for trial in range(300):
    n=int(rng.integers(3,13)); d=int(rng.integers(2,13)); w=rng.integers(1,60,n)
    r=np.zeros(d)
    for x in itertools.product([0,1],repeat=n): r[int(np.dot(x,w))%d]+=1
    lhs=np.abs(d*r/2**n-1).max()
    mid=sum(np.prod(np.abs(np.cos(np.pi*a*w/d))) for a in range(1,d))
    rhs=sum(sum(1 for a in range(1,dp+1) if math.gcd(a,dp)==1)*math.exp(-math.pi**2*sum(1 for x in w if x%dp)/(2*dp*dp)) for dp in range(2,d+1) if d%dp==0)
    bad+= not (lhs<=mid+1e-9 and mid<=rhs+1e-9)
print("Lemma C(1) violations in 300 random cases:",bad)
