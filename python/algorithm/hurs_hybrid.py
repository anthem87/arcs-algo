from hurs_arcs import *
from bisect import bisect_right
def forward_orig(Wasc,Kcap):
    """HURS forward on ORIGINAL weights in ascending order; H[j] = exact R(first j smallest). Stops when K>Kcap."""
    H=[[(0,0)]]
    for w in Wasc:
        cur=H[-1]; sh=[(a+w,b+w) for a,b in cur]; merged=[]
        for a,b in sorted(cur+sh):
            if merged and a<=merged[-1][1]+1: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
            else: merged.append((a,b))
        if len(merged)>Kcap: break
        H.append(merged)
    return H
def member(Hj,v):
    i=bisect_right(Hj,(v,float('inf')))-1
    return i>=0 and Hj[i][0]<=v<=Hj[i][1]
class HursArc:
    def __init__(self,W,Kcap=200000,dens=16.0):
        self.Wd=sorted(W,reverse=True); n=len(W)
        self.H=forward_orig(sorted(W),Kcap)          # H[j]: exact reachability of the j smallest weights
        self.L=len(self.H)-1                          # exact for suffixes with <= L weights
        self.A=Arcs(self.Wd); self.n=n
        self.Mm=mstar(self.Wd,dens=dens)
        self.dummies=augment(W)                       # HURS dummies: only for the forward negative certificate, discarded after
        self.Sp=sum(W)+sum(self.dummies)
    def solve(self,T):
        if T<0 or T>self.Sp: return None,'UNREACHABLE(dummy cert.)'
        Wd=self.Wd; n=self.n; k=0; out=[]
        while True:
            m=n-k                                      # size of remaining suffix
            if m<=self.L:                              # exact HURS backward on originals: never stuck
                Hs=self.H
                if not member(Hs[m],T): return None,'exact-no'
                for j in range(m,0,-1):
                    w=Wd[n-j]
                    if T>=w and member(Hs[j-1],T-w): out.append(w); T-=w
                return out,'arc+hurs'
            if m<=self.Mm:                             # exact MITM on a dense small block
                rest=mitm(Wd[k:],T); return (None,'mitm-no') if rest is None else (out+rest,'arc+mitm')
            w=Wd[k]; sin=self.A.score(k+1,T-w); sout=self.A.score(k+1,T)
            if sin==-math.inf and sout==-math.inf: return None,'arc-no'
            if sin>=sout: out.append(w); T-=w
            k+=1
