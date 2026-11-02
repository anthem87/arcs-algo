"""Arc terms with the Edgeworth correction (order 1/v), tested on exact counts at N = 500."""
import mpmath as mp, numpy as np, math
mp.mp.dps=60
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'arcform.py')).read().split("e=lambda")[0].split("mp.mp.dps=90")[1])
e=lambda x: mp.expj(2*mp.pi*x)
def He(k,z):
    h0,h1=mp.mpf(1),z
    if k==0: return h0
    for j in range(2,k+1): h0,h1=h1,z*h1-(j-1)*h0
    return h1
def arc_cumulants(a,q):
    F=mp.mpc(1); k=[mp.mpc(0)]*5; zero=[]
    for w in W:
        u=e(mp.mpf(w*a)/q)
        if abs(1+u)<mp.mpf(10)**-30:            # vanishing factor: w * d/dT, plus cumulants of e^{iwt/2} sinc(wt/2)
            zero.append(w); k[1]+=mp.mpf(w)/2; k[2]+=mp.mpf(w)**2/12; k[4]+=-mp.mpf(w)**4/120
        else:
            F*=1+u; p=u/(1+u)
            k[1]+=w*p; k[2]+=w**2*p*(1-p); k[3]+=w**3*p*(1-p)*(1-2*p); k[4]+=w**4*p*(1-p)*(1-6*p+6*p*p)
    return F,k,zero
def arc_term(T,F,k,zero,a,q,edge):
    s=mp.sqrt(k[2]); z=(T-k[1])/s; phi=mp.exp(-z*z/2)/mp.sqrt(2*mp.pi)
    c3=k[3]/(6*s**3) if edge else 0; c4=k[4]/(24*s**4) if edge else 0; c6=k[3]**2/(72*s**6) if edge else 0
    if not zero: g=phi/s*(1+c3*He(3,z)+c4*He(4,z)+c6*He(6,z))
    else:       g=-phi/k[2]*(He(1,z)+c3*He(4,z)+c4*He(5,z)+c6*He(7,z))*mp.fprod(zero)   # w * d/dT
    return e(-mp.mpf(T*a)/q)*F*g
H=60
print(f"{'arc':>6}{'T0 offset':>10}{'ratio Gaussian':>16}{'ratio Edgeworth':>17}")
for q,a in [(1,0),(8,1),(6,1),(10,1),(10,3),(4,1),(14,1)]:
    F,k,zero=arc_cumulants(a,q)
    for d in (0,150,-400):
        T0=S//2+d; rng=range(T0-12*H,T0+12*H+1)
        wnd={t:mp.exp(-mp.mpf(t-T0)**2/(2*H*H)) for t in rng}
        Y=mp.fsum(r[t]*e(mp.mpf(a*t)/q)*wnd[t] for t in rng)
        P0=mp.fsum(arc_term(t,F,k,zero,a,q,False)*e(mp.mpf(a*t)/q)*wnd[t] for t in rng)
        P1=mp.fsum(arc_term(t,F,k,zero,a,q,True)*e(mp.mpf(a*t)/q)*wnd[t] for t in rng)
        print(f"{str(a)+'/'+str(q):>6}{d:10d}{mp.nstr(abs(Y/P0),6):>16}{mp.nstr(abs(Y/P1),8):>17}   (arg {float(mp.arg(Y/P1)):+.1e})",flush=True)
