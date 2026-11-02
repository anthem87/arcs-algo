"""Paper §8 (Propositions 8.1-8.4): the propagation theory of §7 applied to HURS and to the arc algorithm.
Chain CSP model: x_i in {0,1}, s_0 = 0, s_i := s_{i-1} + w_i x_i (Def), assertion s_n = T (C_comp).
"""
import random, itertools, sys
random.seed(7)

def eval_forward(W):
    H=[{0}]
    for w in W: H.append(H[-1] | {v+w for v in H[-1]})
    return H

def intervals(S):
    s=sorted(S); K=1 if s else 0
    for a,b in zip(s,s[1:]):
        if b!=a+1: K+=1
    return K

def gac_chain(W,T,H,order):
    """Chaotic iteration of the GAC filters on the constraints c_i: s_i = s_{i-1}+w_i x_i, plus s_n={T}.
    Domains: D[s_i] (sets), X[i] (subset of {0,1}). Returns (domains, number of sweeps)."""
    n=len(W); D=[set(h) for h in H]; D[n]&={T}; X=[{0,1} for _ in range(n)]
    rounds=0
    while True:
        rounds+=1; changed=False
        for i in order:  # constraint i (1..n)
            w=W[i-1]; a,b,x=D[i-1],D[i],X[i-1]
            na={v for v in a if (0 in x and v in b) or (1 in x and v+w in b)}
            nb={u for u in b if (0 in x and u in a) or (1 in x and u-w in a)}
            nx={t for t in x if any(v+w*t in b for v in a)}
            if (na,nb,nx)!=(a,b,x): changed=True
            D[i-1],D[i],X[i-1]=na,nb,nx
        if not changed: return D,X,rounds

def brute_proj(W,T):
    n=len(W); P=[set() for _ in range(n+1)]; PX=[set() for _ in range(n)]
    for xs in itertools.product((0,1),repeat=n):
        s=[0]
        for w,x in zip(W,xs): s.append(s[-1]+w*x)
        if s[-1]==T:
            for i,v in enumerate(s): P[i].add(v)
            for i,x in enumerate(xs): PX[i].add(x)
    return P,PX

def greedy_back(W,T,H):
    v=T; I=[]
    for i in range(len(W),0,-1):
        w=W[i-1]
        if v in H[i-1]: continue
        if v-w in H[i-1]: I.append(i-1); v-=w; continue
        return None
    return I if v==0 else None

# ---------- part 1: forward Eval = HURS; fixpoint in 2 sweeps; global consistency; greedy never blocked
err1=dict(eval=0,rounds_bwd=0,gac_vs_brute=0,greedy_stuck=0,greedy_wrong=0); maxr_bad=0; N=0
for trial in range(300):
    n=random.randint(3,11); W=sorted(random.randint(1,40) for _ in range(n))
    H=eval_forward(W)
    S=set(sum(c) for k in range(n+1) for c in itertools.combinations(W,k))
    if H[-1]!=S: err1['eval']+=1
    for T in random.sample(range(0,sum(W)+2),min(6,sum(W)+2)):
        N+=1
        Dg,Xg,r_good=gac_chain(W,T,H,list(range(n,0,-1)))   # backward sweep
        Df,Xf,r_bad=gac_chain(W,T,H,list(range(1,n+1)))     # forward order (unfavourable)
        if r_good>2: err1['rounds_bwd']+=1
        maxr_bad=max(maxr_bad,r_bad)
        P,PX=brute_proj(W,T)
        if T in H[-1]:
            if Dg!=P or Xg!=PX or Df!=P: err1['gac_vs_brute']+=1
            I=greedy_back(W,T,H)
            if I is None: err1['greedy_stuck']+=1
            elif sum(W[i] for i in I)!=T: err1['greedy_wrong']+=1
        else:
            if any(Dg[i] for i in range(n+1)) and Dg[n]: err1['gac_vs_brute']+=1
print("part 1  cases:",N,err1,"max sweeps in the unfavourable order:",maxr_bad)

# ---------- part 2: dummies = a NON-conservative extension
def augment(W):
    W=sorted(W); D=[]; S=0; out=[]
    for w in W:
        while w>S+1: D.append(S+1); out.append(S+1); S+=S+1
        out.append(w); S+=w
    return D
strict=0; stuck=0; tot=0; Kred=[]
for trial in range(300):
    n=random.randint(4,12); W=[random.randint(1,300) for _ in range(n)]
    Dm=augment(W); Wp=sorted(W+Dm)
    RW=eval_forward(sorted(W))[-1]; RWp=eval_forward(Wp)[-1]
    assert RW<=RWp
    o=max(w/(1+sum(Wp[:i])) for i,w in enumerate(Wp)); assert o<=1
    assert intervals(RWp)==1
    if RW!=RWp: strict+=1
    Kred.append(intervals(RW))
    # backward greedy on W' skipping the dummies, on the targets reachable from W
    labels=[(w,0) for w in W]+[(d,1) for d in Dm]; labels.sort()
    Hp=eval_forward([w for w,_ in labels])
    for T in random.sample(sorted(RW),min(5,len(RW))):
        tot+=1; v=T; ok=True
        for i in range(len(labels),0,-1):
            w,isd=labels[i-1]
            if isd: continue
            if v>=w and v-w in Hp[i-1]: v-=w
            elif v not in Hp[i-1]: ok=False; break
        if not ok or v!=0: stuck+=1
print(f"B  R(W) strictly contained in R(W'): {strict}/300; mean K of W without dummies: {sum(Kred)/len(Kred):.1f}; greedy on W' (skipping dummies) fails: {stuck}/{tot}")

# ---------- part 3: arcs = Eval on the quotient mod q
def residues(W,q):
    R={0}
    for w in W: R=R|{(r+w)%q for r in R}
    return R
def counts_mod(W,q):
    N=[0]*q; N[0]=1
    for w in W:
        M=N[:]
        for r in range(q): M[(r+w)%q]+=N[r]
        N=M
    return N
err3=0; sound=0; obs=0; tested=0
for trial in range(200):
    n=random.randint(4,12); base=random.choice([1,2,3,6])
    W=[base*random.randint(1,30) for _ in range(n-1)]+[random.randint(1,30)]
    RW=eval_forward(sorted(W))[-1]
    for q in range(2,13):
        Nq=counts_mod(W,q); Rq=residues(W,q)
        if Rq!={c for c in range(q) if Nq[c]>0}: err3+=1
    for T in range(0,sum(W)+1):
        tested+=1
        blocked=any(T%q not in residues(W,q) for q in range(2,13))
        if blocked:
            obs+=1
            if T in RW: sound+=1
print(f"C  residues of Eval mod q vs N_c(q)>0 (arcs): {err3} discrepancies; obstructions found {obs}/{tested}, false obstructions {sound}")
