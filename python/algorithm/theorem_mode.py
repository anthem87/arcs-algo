"""Theorem mode: the algorithm of Theorem R'' (paper §6.7), with disjoint endgame blocks.
   The practical solver (arcs_solver.arcs_solve + endgame_fast.endgame_mod) repeats its filter rounds on the SAME block;
   those rounds are correlated through the block's weights and are outside Theorem R'' (paper §5.6). This module runs
   the structure that the theorem analyses, so that its hypotheses can be checked on actual runs:
     - R disjoint blocks E_1..E_R of m indices, chosen by a random permutation; G = the remaining indices;
     - round j: the other blocks are taken whole or not by the centre rule on block sums;
       the centre rule of Lemma A on G (weights <= M) leaves |t - S_{E_j}/2| <= M/2;
       ONE filtered round on E_j with P_j uniform among the primes of [P0, 2P0) and r_j uniform in Z/P_j;
     - no fallback: a failed round passes to the next block; after R rounds the answer is FAIL.
   Parameters as in Theorem R'': P0 = floor(rho_m/2), m the least integer with 2^m >= (sigma*sqrt(m))^(4/3).
   Every returned subset is verified. Random weights are the model of the theorem; on other inputs the mode still
   runs, and its answers are still verified, but the bound of the theorem does not apply."""
import math, random
from endgame_fast import filtered_round_idx, uniform_prime
def rho(m,M):
    cM=1/3+1/(2*M)+1/(6*M*M)
    return 2**(m+1)/(M*math.sqrt(2*math.pi*m*cM))
def default_m(M):
    s=math.sqrt((M*M-1)/12); m=2
    while 2**m<(s*math.sqrt(m))**(4/3): m+=1
    return m
def centre_rule(ws,t,extra):
    """Lemma A: process ws in the given order, c = (sum of the unprocessed + extra)/2, take x minimizing |t - c|"""
    R=sum(ws); take=[]
    for i,w in enumerate(ws):
        R-=w; c=(R+extra)/2
        if abs(t-w-c)<=abs(t-c): take.append(i); t-=w
    return take,t
def solve_theorem(W,T,R,m=None,P0=None,rng=None,check=True,M=None):
    """returns (indices or None, info). info records the round that succeeded and whether the hypotheses held.
       M = the range {1..M} of the weight distribution (default: max(W), the sample maximum)."""
    rng=rng or random.Random(0); n=len(W); M=M or max(W)
    m=m or default_m(M); P0=P0 if P0 is not None else int(rho(m,M)//2)
    if R*m>=n: raise ValueError("n must exceed R*m")
    if m*max(W)>=2**63: return None, dict(reason="int64", m=m)   # the 64-bit sums of the filtered round could overflow
    perm=list(range(n)); rng.shuffle(perm)
    blocks=[perm[j*m:(j+1)*m] for j in range(R)]; G=sorted(perm[R*m:],key=lambda i:-W[i])
    SG=sum(W[i] for i in G); SB=[sum(W[i] for i in b) for b in blocks]; S=SG+sum(SB)
    info=dict(m=m,P0=P0,rho_m=rho(m,M),R=R,
              hyp=dict(P0_ge_100=P0>=100, rho_ge_2P0=rho(m,M)>=2*P0, window=abs(T-S/2)<=SG/2-R*m*M))
    for j in range(R):
        others=[k for k in range(R) if k!=j]
        tk,t=centre_rule([SB[k] for k in others],T,SG+SB[j])
        chosen=[i for a in tk for i in blocks[others[a]]]
        tg,t=centre_rule([W[i] for i in G],t,SB[j])
        chosen+= [G[a] for a in tg]
        if t<0 or t>SB[j]: continue
        P=uniform_prime(P0,2*P0,rng) if P0>=2 else 3   # P0 < 2 only far outside the theorem
        E=[W[i] for i in blocks[j]]
        idx=filtered_round_idx(E,t,P,rng.randrange(P))
        if idx is not None:
            X=chosen+[blocks[j][a] for a in idx]
            if check: assert len(set(X))==len(X) and sum(W[i] for i in X)==T
            info.update(round=j+1,P=P,u=2*t-SB[j]); return X,info
    info.update(round=None); return None,info
