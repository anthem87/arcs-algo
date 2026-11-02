import numpy as np, time
t=np.linspace(1e-3,np.pi/2,200001); L=np.log(np.sin(t)/t)+t**2/6+t**4/180
print("c6 = max |Lambda(t)+t^4/180|/t^6 on (0,pi/2]:", (np.abs(L)/t**6).max(), " sign max:",L.max())
t0=time.time(); worst={}
for M in [2,3,5,16,64,317]:
    mu=(M+1)/2; s2=(M*M-1)/12; sg=np.sqrt(s2); k4=-(M**4-1)/120
    p=np.ones(M)/M; d=np.array([1.0])
    for k in range(1,161):
        d=np.convolve(d,p); v=np.arange(len(d))+k; z=(v-k*mu)/np.sqrt(k*s2)
        g=np.exp(-z*z/2)/np.sqrt(2*np.pi*k*s2)
        ed=g*(1+k4/(24*s2*s2*k)*(z**4-6*z*z+3))
        q=1/(M*np.sin(np.pi/(2*M)))
        e1=np.abs(d-g).max()*sg*k**1.5
        e2=np.abs(d-ed).max()*sg*k**2.5
        bound2=0.34+ (q**(k-2)/np.sqrt(12) + (0.41/k+0.11)*np.exp(-0.308*k))*k**2.5 if k>=2 else np.inf
        worst.setdefault(M,[]).append((k,e1,e2,e2<=bound2))
for M,rows in worst.items():
    sel=[r for r in rows if r[0] in (2,3,5,10,20,40,80,160)]
    print(f"M={M}: C(k)=sigma k^1.5 |P-g|:", [(r[0],round(r[1],4)) for r in sel])
    print(f"      sigma k^2.5 |P-Edgeworth|:", [(r[0],round(r[2],3)) for r in sel], " all within bound:", all(r[3] for r in rows if r[0]>=2))
print(f"[{time.time()-t0:.0f}s]")
