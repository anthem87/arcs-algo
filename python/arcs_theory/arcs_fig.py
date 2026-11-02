"""Races carried by the emerging arcs of F_N(z) = (1+z) prod_{p<=N} (1+z^p), q = 6, 8, 10, 14.
Measured H_{a/q}(N)·log N/sqrt N against the Rubinstein–Sarnak mean and +-2 sd (GRH + LI)."""
import numpy as np, math, cmath, itertools, mpmath as mp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps=25
X=10**8
sv=np.ones(X//2+1,dtype=np.bool_); sv[0]=False
for i in range(1,int(math.isqrt(X))//2+1):
    if sv[i]: p=2*i+1; sv[p*p//2::p]=False
pr=np.concatenate(([2],2*np.nonzero(sv)[0]+1)); del sv
gens={6:[(5,2)],8:[(3,2),(5,2)],10:[(3,4)],14:[(3,6)]}
def chars(q):
    G=[r for r in range(1,q) if math.gcd(r,q)==1]; gl=gens[q]; rep={}
    for ex in itertools.product(*[range(o) for _,o in gl]):
        v=1
        for (g,o),e in zip(gl,ex): v=v*pow(g,e,q)%q
        rep[v]=ex
    return [{r:cmath.exp(2j*math.pi*sum(k*e/o for k,e,(g,o) in zip(ks,rep[r],gl))) for r in G} for ks in itertools.product(*[range(o) for _,o in gl])]
def primitive(chi,q):
    for d in sorted(x for x in range(1,q+1) if q%x==0):
        if all(abs(chi[n]-1)<1e-9 for n in chi if n%d==1%d):
            vals=[0]*d
            for n in chi: vals[n%d]=chi[n]
            return d,vals
def B(d,vals):
    s0=mp.fsum(vals[k]*mp.digamma(mp.mpf(k)/d) for k in range(1,d))
    s1=mp.fsum(vals[k]*mp.stieltjes(1,mp.mpf(k)/d) for k in range(1,d))
    L1=-s0/d; d1=(mp.log(d)*s0-s1)/d
    a=0 if abs(vals[(d-1)%d]-1)<1e-9 else 1
    return float(2*(mp.re(d1/L1)+0.5*mp.log(mp.mpf(d)/mp.pi)+0.5*mp.digamma((1+a)/mp.mpf(2))))
us=np.linspace(math.log(1e4),math.log(1e8),3000)
fig,axs=plt.subplots(2,2,figsize=(13,8.5)); out=[]
for ax,(q,a,lab) in zip(axs.flat,[(6,1,'q = 6: only the principal character'),(8,1,'q = 8: the character χ₈'),(10,1,'q = 10: the Legendre symbol mod 5'),(14,1,'q = 14: the two cubic characters mod 7')]):
    G=[r for r in range(1,q) if math.gcd(r,q)==1]; phi=len(G)
    w={r:math.log(abs(math.cos(math.pi*a*r/q))) for r in G}; wb=np.mean(list(w.values())); c={r:w[r]-wb for r in G}
    Nq={r:sum(1 for b in range(q) if b*b%q==r) for r in G}
    mu=-sum(c[r]*Nq[r] for r in G)/phi; var=0; seen=[]
    for chi in chars(q):
        if all(abs(chi[r]-1)<1e-9 for r in G): continue
        A=sum(c[r]*chi[r].conjugate() for r in G)/phi
        if abs(A)<1e-12: continue
        d,vals=primitive(chi,q); seen.append(d); var+=abs(A)**2*B(d,vals)
    pp=pr[np.gcd(pr,q)==1]; cs=np.cumsum(np.array([c[r] for r in pp%q]))
    v=np.array([cs[np.searchsorted(pp,math.exp(u),side='right')-1]*u/math.exp(u/2) for u in us])
    fin=np.array([float(mp.li(math.exp(u/2)))*u/(2*math.exp(u/2)) for u in us])  # ~1+2/log x
    sd=math.sqrt(var)
    ax.plot(us/math.log(10),v,color='#2b6cb0',lw=0.8,label='measured')
    ax.plot(us/math.log(10),mu*fin,color='#c53030',lw=1.4,label='Rubinstein–Sarnak mean')
    ax.fill_between(us/math.log(10),mu*fin-2*sd,mu*fin+2*sd,color='#c53030',alpha=0.1,label='± 2 sd (from L(1,χ), L′(1,χ))')
    ax.axhline(0,color='k',lw=0.5); ax.set_title(lab,loc='left',fontsize=10.5)
    ax.set_xlabel('log₁₀ N'); ax.set_ylabel('H(N) · log N / √N')
    out.append((q,mu,sd,float(v.mean()),float(v.std()),seen))
    ax.legend(fontsize=8)
fig.suptitle('Height of the emerging arcs of the prime subset-sum generating function, minus the prime-number-theorem term',fontsize=12)
fig.tight_layout()
import os; _here=os.path.dirname(os.path.abspath(__file__))       # written next to this script, not in the cwd
fig.savefig(os.path.join(_here,'fig_arc_races.png'),dpi=300); fig.savefig(os.path.join(_here,'fig_arc_races.pdf'))
for o in out: print('q=%d  mu=%.3f sd=%.3f | measured mean %.3f sd %.3f | conductors seen %s'%o)
