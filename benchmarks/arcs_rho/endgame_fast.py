"""The exact endgame (paper §5.6; pseudocode FILTERED-ENDGAME, FILTERED-ROUND, MITM).
   Merging: sorted subset sums by merging L and L+w (Cormen 35.5, MERGE-LISTS): a stable sort of two sorted runs is a
       linear merge (timsort), so the sorted list costs O(2^h) instead of O(h 2^h).
   Filter: the block holds about F solutions (the paper's 𝒵). Keep only the subsets of the first half whose sum is = r (mod P) and of the
       second half = t-r (mod P): a solution survives with probability 1/P. Each filtered list is built by a
       meet-in-the-middle on residues, at cost O(2^{h/2} + 2^h/P) for a half of h weights. With P ~ F/2 one
       round costs O(m 2^{m/4} + m 2^{m/2}/F) (Table 8) and succeeds with probability ~ 1 - e^{-2}; after `tries` rounds it falls back to
       the full exact meet-in-the-middle if m <= fallback_max_m (44), so up to that size no solution is lost with
       respect to the old endgame; beyond it the failure is reported (code -2), also when F < minF.
   Sums are int64: blocks must satisfy m*max(W) < 2^63 (checked).
   Change log (28/10, after BENCH5 v1): uniform prime (rejection sampling), guard also in the F < minF branch,
   one round factored out as filtered_round_idx. BENCH5 v1 ran the previous version
   (benchmarks/bench5_v1/endgame_fast.py). This file differs from benchmarks/bench5_v2/endgame_fast.py only in comments."""
import numpy as np, math, random
from sympy import nextprime, randprime, isprime
I64=np.int64
def sorted_sums(ws):                              # (sums ascending, masks)
    L=np.zeros(1,I64); M=np.zeros(1,I64)
    for j,w in enumerate(ws):
        L2=np.concatenate([L,L+I64(w)]); M2=np.concatenate([M,M|I64(1<<j)])
        p=np.argsort(L2,kind='stable'); L=L2[p]; M=M2[p]
    return L,M
def all_sums(ws):                                 # unsorted, O(2^h)
    L=np.zeros(1,I64); M=np.zeros(1,I64)
    for j,w in enumerate(ws):
        L=np.concatenate([L,L+I64(w)]); M=np.concatenate([M,M|I64(1<<j)])
    return L,M
def _decode(ws,mask): return [ws[b] for b in range(len(ws)) if (int(mask)>>b)&1]
def join(LA,MA,LB,MB,T):                          # any a+b=T with LB sorted
    need=T-LA; pos=np.minimum(np.searchsorted(LB,need),len(LB)-1); hit=np.flatnonzero(LB[pos]==need)
    if len(hit)==0: return None
    i=int(hit[0]); return int(MA[i]),int(MB[pos[i]])
def mitm_merge(W,T):                              # proposal 2 alone
    h=len(W)//2; A,B=W[:h],W[h:]
    LA,MA=all_sums(A); LB,MB=sorted_sums(B)
    r=join(LA,MA,LB,MB,T)
    return None if r is None else _decode(A,r[0])+_decode(B,r[1])
def residue_list(ws,P,r):                         # all subsets of ws with sum = r (mod P): sums, masks
    h1=len(ws)//2; A1,A2=ws[:h1],ws[h1:]
    L1,M1=all_sums(A1); L2,M2=all_sums(A2)
    R2=L2%P; o=np.argsort(R2,kind='stable'); R2s=R2[o]; L2s=L2[o]; M2s=M2[o]
    need=(r-L1)%P; lo=np.searchsorted(R2s,need,'left'); hi=np.searchsorted(R2s,need,'right'); cnt=hi-lo
    tot=int(cnt.sum())
    if tot==0: return np.zeros(0,I64),np.zeros(0,I64)
    i1=np.repeat(np.arange(len(L1)),cnt)
    start=np.repeat(lo-np.concatenate([[0],np.cumsum(cnt)[:-1]]),cnt)
    i2=np.arange(tot)+start
    return L1[i1]+L2s[i2], M1[i1]|(M2s[i2]<<I64(h1))
def uniform_prime(lo,hi,rng):
    """a prime chosen uniformly among the primes of [lo, hi) (rejection sampling; Lemma K). Needs lo >= 2, hi > lo,
       and a prime in the range (Bertrand: always true for hi >= 2*lo)."""
    if lo<2 or hi<=lo: raise ValueError("uniform_prime needs 2 <= lo < hi")
    while True:
        x=rng.randrange(lo,hi)
        if isprime(x): return x
def filtered_round_idx(W,T,P,r):
    """one round of the filtered endgame (paper §5.6) with prime P and residue r: indices into W, or None"""
    m=len(W); h=m//2; A,B=W[:h],W[h:]
    LA,MA=residue_list(A,P,r); LB,MB=residue_list(B,P,(T-r)%P)
    if len(LA)==0 or len(LB)==0: return None
    o=np.argsort(LB); res=join(LA,MA,LB[o],MB[o],T)
    if res is None: return None
    a,b=res
    return [j for j in range(h) if (a>>j)&1]+[h+j for j in range(m-h) if (b>>j)&1]
def filtered_round(W,T,P,r):
    idx=filtered_round_idx(W,T,P,r)
    return None if idx is None else [W[j] for j in idx]
def endgame_mod(W,T,F,rng=random,tries=6,minF=8.0,random_prime=True,fallback_max_m=44):
    """Filtered endgame, with the merged meet-in-the-middle as fallback. F = estimated number of solutions of the block at T.
       random_prime=True: P uniform among the primes of [P0, 2P0), P0 = max(3, F/2), as in Lemma K / Theorem R'' (which needs P0 >= 100)
       (fresh prime and residue at every round); False: P = nextprime(F/2) fixed (first version)."""
    m=len(W)
    if m and m*max(W)>=2**63: raise OverflowError("block sum may exceed int64")
    if F<minF or m<16:
        if m>fallback_max_m: return None,-2         # same guard as below (found by the independent reproduction)
        return mitm_merge(W,T),0
    P0=max(3,int(F/2))                          # Theorem R'' needs P0 >= 100, i.e. F >= 200
    for t in range(1,tries+1):
        if random_prime: P=uniform_prime(P0,2*P0,rng)   # uniform over the primes (v1 of BENCH5 used sympy.randprime)
        else: P=int(nextprime(max(3,int(F/2))))
        res=filtered_round(W,T,P,rng.randrange(P))
        if res is not None: return res,t
    if m>fallback_max_m: return None,-2             # block too large for the full meet-in-the-middle: report failure
    return mitm_merge(W,T),-1                      # fallback: full exact meet-in-the-middle
