# Paper §5.4 and Proposition 8.5: the blur is invertible on counts (Z[Z]), not in the Boolean semiring B[Z]
import random, itertools
random.seed(3)
def counts(W):
    S=sum(W); r=[0]*(S+1); r[0]=1
    for w in W:
        for v in range(S,w-1,-1): r[v]+=r[v-w]
    return r
ok=0; tot=0
for t in range(300):
    n=random.randint(3,10); m=random.randint(5,60); W=[random.randint(m,4*m) for _ in range(n)]
    k=(min(W)-1).bit_length(); D=[2**j for j in range(k)]; M=2**k   # dummy 1,2,..,2^{k-1}
    rW=counts(W); rWD=counts(W+D); S=sum(W)
    # r_W(T)-r_W(T-M) = r_WD(T)-r_WD(T-1)  => reconstruction by telescoping
    rec=[0]*(S+1)
    for T in range(S+1):
        rec[T]=(rWD[T]-(rWD[T-1] if T>=1 else 0))+(rec[T-M] if T>=M else 0)
    tot+=1; ok+= rec==rW
print("exact de-blurring in Z:",ok,"/",tot)
# Boolean: same R(W u D) and same D, different R(W)
seen={}; clash=0
for a,b,c in itertools.combinations_with_replacement(range(8,20),3):
    W=[a,b,c]; k=(min(W)-1).bit_length(); D=tuple(2**j for j in range(k))
    RWD=frozenset(i for i,x in enumerate(counts(W+list(D))) if x)
    RW=frozenset(i for i,x in enumerate(counts(W)) if x)
    key=(D,RWD)
    if key in seen and seen[key]!=RW: clash+=1
    seen.setdefault(key,RW)
print("pairs with the same (D, R(W u D)) and different R(W):",clash)
