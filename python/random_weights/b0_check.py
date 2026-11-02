import numpy as np, signal, time
signal.alarm(55); t0=time.time()
# (i) L(t)+t^2/6 >= -t^4/90 on 0<t<=pi/2, L(t)=log(sin t/t)
t=np.linspace(1e-4,np.pi/2,200001); g=np.log(np.sin(t)/t)+t**2/6+t**4/90
print("min of L(t)+t^2/6+t^4/90 on (0,pi/2]:",g.min())
# (ii) |f| <= 1/(M sin(pi/(2M))) <= 0.711 for |theta| >= pi/M
print("max over M of 1/(M sin(pi/2M)):",max(1/(M*np.sin(np.pi/(2*M))) for M in range(2,10**5)))
# (iii) B0: sup_v |P(S_k=v)-g_k(v)| * sigma * k^1.5, exact distributions by convolution
worst=(0,None)
for M in [2,3,5,10,31,100,317]:
    mu=(M+1)/2; s2=(M*M-1)/12; p=np.ones(M)/M; dist=np.array([1.0]); off=0
    for k in range(1,61):
        dist=np.convolve(dist,p); off+=1           # support starts at k
        v=np.arange(len(dist))+k
        g=np.exp(-(v-k*mu)**2/(2*k*s2))/np.sqrt(2*np.pi*k*s2)
        e=np.abs(dist-g).max()*np.sqrt(s2)*k**1.5
        if e>worst[0]: worst=(e,(M,k))
print("max of sigma k^{3/2} |P(S_k=v)-g_k(v)| over M<=317, k<=60:",worst, f"[{time.time()-t0:.0f}s]")
