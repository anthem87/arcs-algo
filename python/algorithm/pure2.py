import random, math
from collections import Counter
from hurs_arcs import Arcs
random.seed(3)
def exact_reach(W):
    r=1
    for w in W: r|=r<<w
    return r
def full_spectrum_tail(W,T):
    """all arcs a/q with q = S+1 (complete Fourier basis): r(T) = (1/(S+1)) sum_a e(-Ta/(S+1)) F(e(a/(S+1))) is the exact count.
       Implemented with exact integer arithmetic (equivalent to the inverse DFT, no rounding)."""
    layers=[1]
    for w in W: layers.append(layers[-1]|(layers[-1]<<w))
    if not (layers[-1]>>T)&1: return None
    out=[]
    for j in range(len(W),0,-1):
        if not (layers[j-1]>>T)&1: out.append(W[j-1]); T-=W[j-1]
    return out
def arc_with_full_endgame(A,T,Send):
    W=A.W; out=[]
    for k,w in enumerate(W):
        if A.S[k]<=Send:
            rest=full_spectrum_tail(W[k:],T); return (None,k) if rest is None else (out+rest,k)
        sin=A.score(k+1,T-w); sout=A.score(k+1,T)
        if sin==-math.inf and sout==-math.inf: return None,k
        if sin>=sout: out.append(w); T-=w
    return (out,len(W)) if T==0 else (None,len(W))
print(f"{'n':>4}{'wmax':>7}{'endgame S<=':>12}{'weights in endgame':>20}{'found':>9}")
for n,wmax in [(22,120),(40,500),(60,2000),(80,5000),(120,2000),(150,10**4)]:
    for Send in [500,5000]:
        found=tot=0; ends=[]
        for rep in range(2):
            W=sorted([random.randint(1,wmax) for _ in range(n)],reverse=True); A=Arcs(W); R=exact_reach(W); S=sum(W)
            Ts=[t for t in range(S+1) if (R>>t)&1]; Ts=random.sample(Ts,min(3000,len(Ts)))
            for T in Ts:
                sol,k=arc_with_full_endgame(A,T,Send); tot+=1
                found+= sol is not None and sum(sol)==T and not (Counter(sol)-Counter(W))
            ends.append(sum(1 for k in range(n+1) if A.S[k]<=Send)-1)
        print(f"{n:4d}{wmax:7d}{Send:12d}{sum(ends)/len(ends):20.1f}{100*found/tot:8.2f}%",flush=True)
