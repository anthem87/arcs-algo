"""Quick validation of the three changes made after a first run of the fixed-constant solver: the uniform prime, the guard m <= 44 in the F < 8 branch,
   and the theorem mode."""
import random, math, time, collections
from sympy import primerange
from endgame_fast import uniform_prime, endgame_mod, mitm_merge
from theorem_mode import solve_theorem, default_m, rho
rng=random.Random(1)
# 1. uniformity of the prime: chi-square over the primes of [100,200)
ps=list(primerange(100,200)); c=collections.Counter(uniform_prime(100,200,rng) for _ in range(42000))
e=42000/len(ps); chi=sum((c[p]-e)**2/e for p in ps)
print(f"1. uniform_prime: {len(ps)} primes, chi2 = {chi:.1f} (df {len(ps)-1}); outside the primes: {sum(v for k,v in c.items() if k not in ps)}")
import sympy
c2=collections.Counter(int(sympy.randprime(100,200)) for _ in range(42000)); chi2=sum((c2[p]-e)**2/e for p in ps)
print(f"   sympy.randprime for comparison: chi2 = {chi2:.1f}")
# 2. guard: F<8 and m=50 -> no full MITM
W=[rng.randint(1,10**15) for _ in range(50)]
t0=time.time(); r=endgame_mod(W,sum(W)//2,F=1.0,rng=rng); print(f"2. guard F<8, m=50: returns {r[1]} in {time.time()-t0:.3f} s")
W=[rng.randint(1,10**6) for _ in range(24)]; X=rng.sample(W,12); r=endgame_mod(W,sum(X),F=1.0,rng=rng)
print(f"   F<8, m=24: code {r[1]}, sum ok {r[0] is not None and sum(r[0])==sum(X)}")
# 3. theorem mode on random weights, b bits
for b,R in [(24,6),(30,6),(34,6)]:
    M=2**b; m=default_m(M); n=6*R*m; ok=0; rounds=[]; t0=time.time(); hyp=None; nh=0
    for s in range(20):
        r2=random.Random(100*b+s); W=[r2.randint(1,M) for _ in range(n)]; S=sum(W)
        w8=int(0.9*(M*(n-R*m)//4-R*m*M)); T=S//2+r2.randint(-w8,w8)   # inside the window of R'' (S_G ~ |G|M/2)
        X,info=solve_theorem(W,T,R,rng=r2,M=M); hyp=info['hyp']; nh+=all(hyp.values())
        if X is not None: ok+=1; rounds.append(info['round'])
    print(f"3. b={b} n={n} m={m} P0={info['P0']} rho_m={info['rho_m']:.0f} R={R}: found {ok}/20, rounds used {collections.Counter(rounds)}, "
          f"{(time.time()-t0)/20*1e3:.0f} ms/target, hypotheses of R'' hold on {nh}/20")
