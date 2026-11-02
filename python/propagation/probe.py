# Probing (paper §7.5, paragraph "Probing: non-local X", Proposition 7.10): find non-local X := A or X := ¬A
import random, itertools
import ext as V
random.seed(5)
def ext_probe(n,C,fixed):
    C=list(C); known=V.ext(n,C,fixed)
    if known is None: return None,0
    added=0; changed=True
    while changed:
        changed=False; forced={}; links=[]
        for A in range(n):
            if A in known: continue
            r0=V.ext(n,C,{**known,A:0}); r1=V.ext(n,C,{**known,A:1})
            if r0 is None and r1 is None: return None,added
            if r0 is None or r1 is None: forced[A]=1 if r0 is None else 0; continue
            for B in range(A+1,n):
                if B in known or B not in r0 or B not in r1: continue
                links.append(('xor',[B],r0[B]) if r0[B]==r1[B] else ('xor',[A,B],r0[B]))
        if forced or links:
            C+=links; added+=len(links)
            k2=V.ext(n,C,{**known,**forced})
            if k2 is None: return None,added
            if k2!=known or links: changed = k2!=known
            known=k2
    return known,added
for label,mix in [("XOR + definitions",(0.6,0.6)),("definitions + rare XOR",(0.2,0.9))]:
    f=v=p=err=0; links=0; one=0; den=0
    for _ in range(50):
        n=14; C=V.rand_net(n,mix); allsol=V.brute(n,C,{})
        if not allsol: continue
        base=random.choice(allsol)
        for k in (1,2,3):
            fx={x:base[x] for x in random.sample(range(n),k)}
            sols=V.brute(n,C,fx); truth={x:sols[0][x] for x in range(n) if len({s[x] for s in sols})==1}
            kv=V.ext(n,C,fx); kp,a=ext_probe(n,C,fx); links+=a
            f+=len(truth)-k; v+=len(kv)-k; p+=len(kp)-k
            err+=sum(1 for x,b in kp.items() if truth.get(x)!=b)
            if k==1: den+=1; one+= len(kp)==len(truth)==n
    print(f"{label:30s} Ext {v/f:6.1%} | Ext+probing {p/f:6.1%} | errors {err} | X found {links} | 'solve one, all solved' {one}/{den}")
