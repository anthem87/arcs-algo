import random, math, numpy as np
from hurs_arcs import Arcs
random.seed(5)
bins=np.arange(-1.5,3.01,0.25); err=np.zeros(len(bins)); cnt=np.zeros(len(bins))
for n,wmax in [(40,500),(60,2000),(80,5000),(120,2000)]:
    for rep in range(3):
        W=sorted([random.randint(1,wmax) for _ in range(n)],reverse=True); A=Arcs(W); S=sum(W)
        asc=W[::-1]; L=[1]
        for w in asc: L.append(L[-1]|(L[-1]<<w))           # L[m] = exact reachability of the m smallest = suffix of size m
        reach=L[n]
        Ts=random.sample([t for t in range(S+1) if (reach>>t)&1],1500)
        for T in Ts:
            for k,w in enumerate(W):
                m=n-k-1                                     # size of suffix after this step
                sin=A.score(k+1,T-w); sout=A.score(k+1,T)
                if sin==-math.inf and sout==-math.inf: break
                take= sin>=sout; Tn= T-w if take else T; sc=max(sin,sout)
                feas= Tn>=0 and (L[m]>>Tn)&1
                other= (T if take else T-w); ofeas= other>=0 and (L[m]>>other)&1
                if not ofeas and not feas: break           # already lost earlier; not a fresh decision
                lr=sc/math.log(10)                          # log10 of estimated count rho
                b=np.searchsorted(bins,lr)-1
                if 0<=b<len(bins):
                    cnt[b]+=1; err[b]+= (not feas) and ofeas
                if not feas: break
                T=Tn
print(f"{'log10 rho':>10}{'decisions':>11}{'P(chosen branch empty) measured':>33}{'e^-rho':>10}")
for i in range(len(bins)):
    if cnt[i]>=30:
        rho=10**(bins[i]+0.125)
        print(f"{bins[i]+0.125:10.2f}{int(cnt[i]):11d}{err[i]/cnt[i]:33.4f}{math.exp(-rho):10.4f}")
