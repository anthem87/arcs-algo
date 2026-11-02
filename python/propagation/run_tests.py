import itertools, random, time, math
random.seed(1)
B=(0,1)
# ---------- utilities ----------
def brute(n,cons,doms=None):
    doms=doms or [B]*n
    sols=[]
    for a in itertools.product(*doms):
        if all(c[1](*[a[v] for v in c[0]]) for c in cons): sols.append(a)
    return sols
# ---------- 1. union-find with parity ----------
class UFP:
    def __init__(s,n): s.p=list(range(n)); s.b=[0]*n; s.ok=True
    def find(s,x):
        path=[]
        while s.p[x]!=x: path.append(x); x=s.p[x]
        r=x; acc=0
        for y in reversed(path):      # parity accumulated towards the root
            acc^=s.b[y]; s.b[y]=acc; s.p[y]=r
        return (r, s.b[path[0]] if path else 0) if True else None
    def union(s,x,y,c):            # x xor y = c
        rx,bx=s.find(x); ry,by=s.find(y)
        if rx==ry:
            if bx^by!=c: s.ok=False
            return
        s.p[rx]=ry; s.b[rx]=bx^by^c
def test1(trials=300):
    bad=0
    for _ in range(trials):
        n=random.randint(2,12); m=random.randint(1,14)
        par=[(random.randrange(n),random.randrange(n),random.randint(0,1)) for _ in range(m)]
        uf=UFP(n)
        for x,y,c in par: uf.union(x,y,c)
        cons=[((x,y),(lambda c: lambda a,b: (a^b)==c)(c)) for x,y,c in par]
        S=brute(n,cons)
        if (len(S)>0)!=uf.ok: bad+=1; continue
        if uf.ok:
            for s in S:
                for x in range(n):
                    r,bx=uf.find(x)
                    if s[x]!=s[r]^bx: bad+=1; break
            roots=len({uf.find(x)[0] for x in range(n)})
            if len(S)!=2**roots: bad+=1
    return bad
# ---------- 2. forward evaluation on the complete DAG ----------
OPS={'ite':(3,lambda c,a,b: a if c else b),'and':(2,lambda a,b:a&b),'or':(2,lambda a,b:a|b),'xor':(2,lambda a,b:a^b),'not':(1,lambda a:1-a)}
def rand_circuit(n,k):
    defs={}
    for x in range(k,n):
        op=random.choice(list(OPS)); ar,f=OPS[op]
        defs[x]=(tuple(random.randrange(x) for _ in range(ar)),f)   # every node may read ANY earlier node
    return defs
def Eval(W,defs,order):
    W=[set(w) for w in W]
    for x in order:
        if x in defs:
            pr,f=defs[x]; img={f(*t) for t in itertools.product(*[W[u] for u in pr])}
            W[x]&=img
    return W
def test2(trials=300):
    bad1=bad2=bad3=0
    for _ in range(trials):
        n=random.randint(3,14); k=random.randint(1,min(4,n-1)); defs=rand_circuit(n,k)
        cons=[(pr+(x,),(lambda f: lambda *a: f(*a[:-1])==a[-1])(f)) for x,(pr,f) in defs.items()]
        S=brute(n,cons)
        if len(S)!=2**k: bad1+=1
        inp=tuple(random.randint(0,1) for _ in range(k))
        W=[{inp[i]} for i in range(k)]+[set(B) for _ in range(n-k)]
        W=Eval(W,defs,range(n))
        if any(len(w)!=1 for w in W): bad2+=1
        out=n-1; Sa=[s for s in S if s[out]==1]
        if not len(Sa)<=2**k: bad3+=1
        if k==1 and len(S)>2: bad3+=1
    return bad1,bad2,bad3
# ---------- 3. idempotence of T_struct ----------
def Tstruct(W,n,par,defs):
    uf=UFP(n)
    for x,y,c in par: uf.union(x,y,c)
    if not uf.ok: return None
    W=[set(w) for w in W]
    cls={}
    for x in range(n):
        r,b=uf.find(x); cls.setdefault(r,[]).append((x,b))
    for r,mem in cls.items():
        cell={0,1}
        for x,b in mem: cell&={v^b for v in W[x]}
        for x,b in mem: W[x]={v^b for v in cell}
    return Eval(W,defs,range(n))
def test3(trials=300):
    bad=0
    for _ in range(trials):
        n=random.randint(3,12); k=random.randint(1,min(4,n-1)); defs=rand_circuit(n,k)
        # parities only between inputs, to stay in the shared form after Eval
        par=[(random.randrange(k),random.randrange(k),random.randint(0,1)) for _ in range(random.randint(0,3))]
        W0=[set(random.choice([(0,),(1,),(0,1)])) for _ in range(n)]
        W1=Tstruct(W0,n,par,defs)
        if W1 is None: continue
        W2=Tstruct(W1,n,par,defs)
        if W1!=W2: bad+=1
    return bad
# ---------- 4./5. T_comp: GAC, order, bound mu, closure ----------
def gac(W,c):
    vs,f=c; W=[set(w) for w in W]
    sup={v:set() for v in vs}
    for t in itertools.product(*[W[v] for v in vs]):
        if f(*t):
            for v,a in zip(vs,t): sup[v].add(a)
    for v in vs: W[v]&=sup[v]
    return W
def tcomp(W,cons,order):
    sweeps=0
    while True:
        Wn=W
        for i in order: Wn=gac(Wn,cons[i])
        if Wn==W: return W,sweeps
        W=Wn; sweeps+=1
        if any(len(w)==0 for w in W): return W,sweeps
def rand_cons(n,m,dmax=3):
    cons=[]
    for _ in range(m):
        ar=random.randint(2,3); vs=tuple(random.sample(range(n),ar))
        tab={t:(random.random()<0.6) for t in itertools.product(range(dmax),repeat=ar)}
        cons.append((vs,(lambda tab: lambda *a: tab[a])(tab)))
    return cons
def test45(trials=200):
    bad_order=bad_mu=bad_closure=0
    for _ in range(trials):
        n=random.randint(3,7); d=3; cons=rand_cons(n,random.randint(2,7),d)
        W0=[set(range(d)) for _ in range(n)]
        res=set(); 
        mu=sum(len(w)-1 for w in W0)
        for _ in range(20):
            order=list(range(len(cons))); random.shuffle(order)
            Ws,sw=tcomp(W0,cons,order)
            res.add('FAIL' if any(len(w)==0 for w in Ws) else tuple(tuple(sorted(w)) for w in Ws))
            if sw>mu: bad_mu+=1
        if len(res)!=1: bad_order+=1
        r=res.pop(); S=brute(n,cons,[range(d)]*n)
        if r=='FAIL':
            if S: bad_closure+=1
            continue
        Ws=[set(w) for w in r]
        for s in S:
            if any(s[v] not in Ws[v] for v in range(n)): bad_closure+=1; break
    return bad_order,bad_mu,bad_closure
def chain(k):
    W=[{1}]+[{i-1,i} for i in range(2,k+1)]
    cons=[((i,i+1),lambda a,b:a!=b) for i in range(k-1)]
    W2,sw=tcomp(W,cons,list(range(k-1)))       # order: forward
    W3,sw3=tcomp(W,cons,list(range(k-2,-1,-1)))  # backward
    return sw,sw3
# ---------- 6. cost of an injection ----------
def perf(n,d=500):
    # naive: chain of equalities, worklist propagation after the injection into x0
    doms=[set(range(d)) for _ in range(n)]
    t=time.perf_counter(); doms[0]={3}; work=[0]
    nb={i:[j for j in (i-1,i+1) if 0<=j<n] for i in range(n)}
    while work:
        x=work.pop()
        for y in nb[x]:
            new=doms[y]&doms[x]
            if new!=doms[y]: doms[y]=new; work.append(y)
    tn=time.perf_counter()-t
    # shared: union-find (built once, outside the timer), one cell per class
    uf=UFP(n)
    for i in range(n-1): uf.union(i,i+1,0)
    root=uf.find(0)[0]; cell={root:set(range(d))}
    t=time.perf_counter(); r,b=uf.find(0); cell[r]={3}; ts=time.perf_counter()-t
    assert all(next(iter(doms[i]))==3 for i in range(n))
    return tn,ts
if __name__=="__main__":
    print("1 parity:  errors",test1())
    b1,b2,b3=test2(); print(f"2 Eval on the complete DAG: |S|!=2^k {b1}, non-singletons {b2}, bound |S| <= 2^k violated {b3}")
    print("3 idempotence of T_struct: errors",test3())
    o,m,c=test45(); print(f"4/5 T_comp: different orders -> different W* {o}, steps > mu {m}, solutions lost {c}")
    for k in [5,10,20]: print(f"  chain k={k}: passes (forward) {chain(k)[0]}, (backward) {chain(k)[1]}")
    for n in [10,100,1000,10000]:
        tn,ts=perf(n); print(f"6 n={n:6d}: naive injection {tn*1e6:9.1f} us, shared {ts*1e6:6.2f} us")
