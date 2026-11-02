"""Algorithm Ext (paper §7.5, Table 14): definitional extensions X (Theorem 7.7) built systematically.
Boolean network with constraints: ('xor', vars, b)  [x1 ⊕ ... ⊕ xk = b, k >= 1]
                                  ('def', y, op, args) op in and/or/ite/not
Baseline = T_comp (GAC on every constraint, chaotic iteration).
Ext      = Gaussian elimination over GF(2) (every reduced row = one definitional X) + linearisation of the
           definitions when an input is known (and(a,1)=a, ite(1,a,b)=a, ...) + GAC on the rest,
           up to the fixpoint.
"""
import random, itertools, time
random.seed(11)

def evalc(c, a):
    if c[0]=='xor':
        s=0
        for v in c[1]: s^=a[v]
        return s==c[2]
    _,y,op,args=c; v=[a[x] for x in args]
    if op=='and': r=v[0]&v[1]
    elif op=='or': r=v[0]|v[1]
    elif op=='not': r=1-v[0]
    else: r=v[1] if v[0] else v[2]
    return a[y]==r

def cvars(c): return list(c[1]) if c[0]=='xor' else [c[1]]+list(c[3])

def brute(n,C,fixed):
    sols=[]
    for bits in itertools.product((0,1),repeat=n):
        if any(bits[v]!=b for v,b in fixed.items()): continue
        if all(evalc(c,bits) for c in C): sols.append(bits)
    return sols

def gac(n,C,fixed):
    D=[{0,1} for _ in range(n)]
    for v,b in fixed.items(): D[v]&={b}
    ch=True
    while ch:
        ch=False
        for c in C:
            vs=cvars(c); sup=[set() for _ in vs]
            for vals in itertools.product(*[sorted(D[v]) for v in vs]):
                a=dict(zip(vs,vals))
                if evalc(c,a):
                    for i,x in enumerate(vals): sup[i].add(x)
            for i,v in enumerate(vs):
                nd=D[v]&sup[i]
                if nd!=D[v]: D[v]=nd; ch=True
            if any(not D[v] for v in vs): return None
    return D

def rref(rows,n):
    """rows: list of (mask, b). Returns the reduced basis as a dict pivot->(mask,b), or None if 0=1."""
    piv={}
    for m,b in rows:
        for p,(pm,pb) in piv.items():
            if m>>p&1: m^=pm; b^=pb
        if m==0:
            if b: return None
            continue
        p=m.bit_length()-1
        for q in list(piv):
            qm,qb=piv[q]
            if qm>>p&1: piv[q]=(qm^m,qb^b)
        piv[p]=(m,b)
    return piv

def ext(n,C,fixed):
    known=dict(fixed); D=None
    while True:
        rows=[(1<<v,b) for v,b in known.items()]
        rest=[]
        for c in C:
            if c[0]=='xor':
                m=0
                for v in c[1]: m^=1<<v
                rows.append((m,c[2])); continue
            _,y,op,args=c; k=[known.get(x) for x in args]
            if op=='not': rows.append(((1<<y)^(1<<args[0]),1)); continue
            if op in('and','or'):
                neutral=1 if op=='and' else 0
                if k[0] is not None and k[1] is not None:
                    r=(k[0]&k[1]) if op=='and' else (k[0]|k[1]); rows.append((1<<y,r)); continue
                done=False
                for i in (0,1):
                    if k[i] is not None:
                        if k[i]==neutral: rows.append(((1<<y)^(1<<args[1-i]),0))   # X: y = the other input
                        else: rows.append((1<<y,1-neutral))
                        done=True; break
                if not done: rest.append(c)
                continue
            if k[0] is not None:                                               # ite with a known condition
                rows.append(((1<<y)^(1<<args[1 if k[0] else 2]),0)); continue
            if k[1] is not None and k[2] is not None and k[1]==k[2]: rows.append((1<<y,k[1])); continue
            rest.append(c)
        piv=rref(rows,n)
        if piv is None: return None
        new={p:b for p,(m,b) in piv.items() if m==1<<p}
        D=gac(n,rest,{**known,**new}) if rest else [ {new[v]} if v in new else {0,1} for v in range(n)]
        if D is None: return None
        nk={v:next(iter(D[v])) for v in range(n) if len(D[v])==1}
        nk.update(new)
        if nk==known: return known
        known=nk

def rand_net(n,mix,plant=None):
    C=[]; plant=plant or [random.randint(0,1) for _ in range(n)]
    for _ in range(int(n*mix[0])):
        k=random.choice([2,3,3,4]); vs=random.sample(range(n),k); b=0
        for v in vs: b^=plant[v]
        C.append(('xor',vs,b))
    order=list(range(n)); random.shuffle(order); defined=set()
    for _ in range(int(n*mix[1])):
        i=random.randint(2,n-1); y=order[i]; pre=order[:i]
        if y in defined: continue
        defined.add(y)
        op=random.choice(['and','or','ite','not'])
        ar={'and':2,'or':2,'not':1,'ite':3}[op]
        if len(pre)<ar: continue
        C.append(('def',y,op,random.sample(pre,ar)))
    return C

def experiment(label,mix,trials=150,n=14):
    st=dict(cases=0,unsat=0,forced=0,gac=0,vas=0,err_g=0,err_v=0,miss_unsat_v=0,one_shot=0,one_shot_den=0)
    for _ in range(trials):
        C=rand_net(n,mix)
        allsol=brute(n,C,{})
        if not allsol: continue
        base=random.choice(allsol)
        for kfix in (1,2,3):
            fx={v:base[v] for v in random.sample(range(n),kfix)}
            sols=brute(n,C,fx); st['cases']+=1
            truth={v:sols[0][v] for v in range(n) if len({s[v] for s in sols})==1}
            Dg=gac(n,C,fx); kv=ext(n,C,fx)
            kg={v:next(iter(Dg[v])) for v in range(n) if len(Dg[v])==1}
            st['forced']+=len(truth)-kfix; st['gac']+=len(kg)-kfix; st['vas']+=len(kv)-kfix
            st['err_g']+=sum(1 for v,b in kg.items() if truth.get(v)!=b)
            st['err_v']+=sum(1 for v,b in kv.items() if truth.get(v)!=b)
            if kfix==1:
                st['one_shot_den']+=1
                st['one_shot']+= len(kv)==len(truth)==n
    f=st['forced'] or 1
    print(f"{label:34s} cases {st['cases']:4d} | forced {st['forced']:5d} | GAC {st['gac']/f:6.1%} | Ext {st['vas']/f:6.1%} | errors GAC {st['err_g']} Ext {st['err_v']} | 'solve one, all solved' {st['one_shot']}/{st['one_shot_den']}")
    return st

if __name__=="__main__":
    print("Recall = variables determined / variables forced by brute force (excluding the injected ones)")
    experiment("XOR only",(1.0,0.0))
    experiment("dense XOR",(1.3,0.0))
    experiment("XOR + definitions",(0.6,0.6))
    experiment("definitions + rare XOR",(0.2,0.9))

    # completeness in the affine case (Proposition 7.9): for every pair (A,B), R_AB functional <=> Ext determines B from A
    bad=0; tot=0
    for _ in range(150):
        n=12; C=rand_net(n,(1.0,0.0)); allsol=brute(n,C,{})
        if not allsol: continue
        for A in random.sample(range(n),4):
            for a in (0,1):
                sols=[s for s in allsol if s[A]==a]
                if not sols: continue
                kv=ext(n,C,{A:a})
                for B in range(n):
                    if B==A: continue
                    tot+=1
                    func=len({s[B] for s in sols})==1
                    if func!=(B in kv): bad+=1
    print(f"Proposition 7.9 (affine case): R_AB functional <=> Ext fixes B from A: {bad} discrepancies out of {tot}")

    # scale: XOR with a planted solution, 1% of the variables injected
    for n in (100,400,1000,2000):
        pl=[random.randint(0,1) for _ in range(n)]
        C=rand_net(n,(0.9,0.0),pl); fx={v:pl[v] for v in random.sample(range(n),max(1,n//100))}
        t=time.time(); kv=ext(n,C,fx); tv=time.time()-t
        t=time.time(); Dg=gac(n,C,fx); tg=time.time()-t
        kg=sum(1 for d in Dg if len(d)==1)
        ok=all(pl[v]==b for v,b in kv.items())
        print(f"n={n}: injected {len(fx)} | Ext determines {len(kv)} ({tv*1e3:.0f} ms, consistent with the planted solution: {ok}) | GAC {kg} ({tg*1e3:.0f} ms)")

