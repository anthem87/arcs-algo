# ARCS — pseudocode (CLRS style)

ARCS (Arc-guided, Residue-Certified Search) is the solver of the paper (§5.2–5.7). It has two forms with the same steps:
- **ARCS** (default): every parameter is derived from the instance before the descent (§5.7, *Parameters derived from the
  instance*). The user gives only δ, the accepted probability of FAIL on a YES instance, max_ops, the number of operations
  to wait for, and the memory available. Code: `python/algorithm/arcs_rho.py` (`arcs_solve_rho`), with the scores, the
  exact meet-in-the-middle and the residue scan in `arcs_adaptive.py` and the filtered round in `endgame_fast.py`.
- **ARCS-FIXED**: the same steps with the fixed constants of the reference run BENCH5 v2. Code:
  `python/algorithm/arcs_solver.py` (`arcs_solve`), with `arcs_dyn.py` and `endgame_fast.py`.
The theorem mode of §5.6 and §6.7 is `theorem_mode.py`.

Conventions:
- indices start at 1;
- w[k‥n] is the suffix of the weights from position k;
- "ln" is the natural logarithm;
- 2^e·x is an exact rescaling in floating point;
- λ is the expected number of solutions of a block (the Poisson mean of §5.3); λ* is the threshold of the handover;
- ρ = n/log₂ D, with D = max W − min W + 1, is the density of the weight set.

```
ARCS(W, T; δ, max_ops, mem)                                   ▷ default form
 1  if n > 1020 then return (FAIL, "n>1020")                   ▷ floating class counts need 2^{−n} to be a normal double
 2  if some weight ≤ 0 then return (FAIL, "weights must be positive")
 3  π ← indices of W sorted by decreasing weight;  w[k] ← W[π[k]] for k = 1‥n
 4  ρ ← n / log₂(max W − min W + 1)                            ▷ reported in the certificate
 5  λ* ← max(400, (2.3·n/δ)^{1/3});  R ← ⌈ln(1/δ)/2⌉           ▷ tail Pr(Z = 0) ≈ 2.3·λ⁻³ (§6.6); P₀ ≥ 100 (Theorem R″)
 6  V[n+1] ← 0;  for k ← n downto 1:  V[k] ← V[k+1] + w[k]²/4
 7  k* ← the least k with (n−k+1)·ln 2 − ½·ln(2π·max(V[k], 1)) < ln λ*  (k* ← n+1 if none);  m* ← n − k* + 1
 8  P̂ ← max(3, ⌊peak density at k* / 2⌋)
 9  cost* ← cheapest cost in ENDGAME-OPTIONS(m*, P̂, R, m*·w[k*] < 2⁶³, mem)   (∞ if none)
10  C ← CHOOSE-MODULI(w, δ, min(cost*, max_ops), mem)
11  F ← PREPROCESS(w, C)
12  if T < 0 or T > F.S[1] then return (NO, 0, 0)
13  for each q ∈ F.Sel[1]
14      if F.N_q[1][T mod q] = 0 then return (NO, q, T mod q)
15  if cost* > max_ops then return (FAIL, "predicted cost or memory above the limits")   ▷ with the predicted numbers
16  X ← ∅;  t ← T;  forced ← FALSE
17  for k ← 1 to n
18      r ← SCORE(F, k, t)
19      if r = −∞ then return FAILURE("scored-out")
20      (s, m, v) ← r
21      if m·ln 2 − ½·ln(2π·max(v, 1)) < ln λ*                 ▷ independent of t and of the path: the handover is k* unless forced
22          λ ← e^s;  P₀ ← max(3, ⌊λ/2⌋);  B ← w[k‥n]
23          O ← the options of ENDGAME-OPTIONS(m, P₀, R, m·w[k] < 2⁶³, mem) with cost ≤ max_ops
24          if O = ∅
25              forced ← TRUE                                    ▷ no endgame fits: descend one more weight
26          else
27              J ← ENDGAME(B, t, P₀, R, O)
28              if J ≠ NIL then return (YES, π[X ∪ {k − 1 + j : j ∈ J}])
29              if the endgame was exhaustive and k = 1 then return (NO, −3, −3)   ▷ the block is the whole instance
30              return FAILURE("endgame")                        ▷ the path above the block was a guess: no claim
31      s_in ← SCORE(F, k + 1, t − w[k]);  s_out ← SCORE(F, k + 1, t)
32      if s_in = −∞ and s_out = −∞ then return FAILURE("both-out")
33      if s_in ≥ s_out then X ← X ∪ {k};  t ← t − w[k]
34  if t = 0 then return (YES, π[X]) else return FAILURE("end")

FAILURE(reason)                                                ▷ a run that had to descend past an affordable endgame reports the budget
 1  if forced then return (FAIL, "budget") else return (FAIL, reason)
```

```
ENDGAME-OPTIONS(m, P₀, R, fits64, mem)       ▷ the endgames that fit the memory, with their cost models, cheapest first
 1  O ← ∅
 2  if fits64
 3      if P₀ ≥ 100 then O ← O ∪ {(filter, R·(8m·2^{m/4} + 8m·2^{m/2}/P₀))}    ▷ Table 8; Theorem R″ needs P₀ ≥ 100
 4      if 16·2^{m/2} ≤ mem then O ← O ∪ {(mitm, 8m·2^{m/2})}                    ▷ exhaustive
 5      if 32·2^{m/4} ≤ mem then O ← O ∪ {(scan, 16m·2^{m/2})}                   ▷ exhaustive, memory 2^{m/4}
 6  else if 64·2^{m/2} ≤ mem then O ← O ∪ {(exact, 50·2^{m/2})}                ▷ exact integers, exhaustive
 7  return O sorted by cost

ENDGAME(B, t, P₀, R, O)                      ▷ indices into B, or NIL
 1  if the first option of O is filter
 2      for round ← 1 to R
 3          P ← UNIFORM-PRIME(P₀, 2P₀);  r ← uniform integer in [0, P)       ▷ from the operating system; (P, r) recorded
 4          J ← FILTERED-ROUND(B, t, P, r)
 5          if J ≠ NIL then return J
 6      if O has an exhaustive option then use the cheapest one below, else return NIL
 7  if mitm:  return MITM(B, t)
 8  if scan:  return RESIDUE-SCAN(B, t)
 9  if exact: return MITM over exact integers (B, t)

CHOOSE-MODULI(w, δ, cap, mem)                ▷ the arcs are never paid more than the endgame they shorten
 1  q₀ ← the largest q₀ with 2 + 3 + … + q₀ ≤ n;  C ← {2, …, q₀}
 2  s ← min(n(n−1)/2, ⌈ln δ / ln(3/4)⌉)      ▷ a divisor of at least half of the weights is missed with probability ≤ δ
 3  dcap ← max(2, ⌊min(cap/n, mem/(8(n+1)))⌋) ▷ a modulus d costs n·d operations and 8(n+1)·d bytes
 4  for i ← 1 to s
 5      pick two distinct positions at random (from the operating system), with weights a, b;  g ← gcd(a, b)
 6      C ← C ∪ {d : d | g, q₀ < d ≤ dcap}
 7  return C

RESIDUE-SCAN(B, t)                           ▷ Schroeppel–Shamir in the modular form of Howgrave-Graham–Joux: exact
 1  split B into quarters A₁, A₂, A₃, A₄;  L_i ← ALL-SUMS(A_i)
 2  P ← UNIFORM-PRIME(|L₁|, 2|L₁|)
 3  for r ← 0 to P − 1                        ▷ every solution has exactly one r = (sum of A₁ ∪ A₂) mod P
 4      L ← {a + b : a ∈ L₁, b ∈ L₂, a + b ≡ r};  L′ ← {c + d : c ∈ L₃, d ∈ L₄, c + d ≡ t − r}   (mod P)
 5      if some x ∈ L and y ∈ L′ have x + y = t then return the four masks
 6  return NIL                               ▷ exhaustive: no subset of B sums to t
```

With fixed constants (the reference run BENCH5 v2): λ* = 5·10⁴, CAP = 60, Q₀ = 24, DCAP = 2000, PAIRS = 64, C_EPS = 1, ROUNDS = 6, MMAX = 44, seed 7.

```
ARCS-FIXED(W, T)
 1  π ← indices of W sorted by decreasing weight;  w[k] ← W[π[k]] for k = 1‥n
 2  F ← PREPROCESS(w)
 3  if T < 0 or T > F.S[1]
 4      return (NO, 0, 0)                                   ▷ outside [0, S]
 5  for each q ∈ F.Sel[1]                                   ▷ modular certificate on the whole set
 6      if F.N_q[1][T mod q] = 0
 7          return (NO, q, T mod q)
 8  X ← ∅;  t ← T
 9  for k ← 1 to n
10      r ← SCORE(F, k, t)
11      if r = −∞
12          return (FAIL)
13      (s, m, v) ← r
14      if m ≤ CAP and m·ln 2 − ½·ln(2π·max(v, 1)) < ln λ*    ▷ peak density (independent of t) below the threshold: endgame
15          R ← FILTERED-ENDGAME(w[k‥n], t, e^s)                ▷ e^s = λ, the estimated number of solutions
16          if R = NIL
17              return (FAIL)
18          return (YES, π[X ∪ {k − 1 + j : j ∈ R}])
19      s_in ← SCORE(F, k + 1, t − w[k]);  s_out ← SCORE(F, k + 1, t)
20      if s_in = −∞ and s_out = −∞
21          return (FAIL)
22      if s_in ≥ s_out                                       ▷ compares the first components; −∞ always loses
23          X ← X ∪ {k};  t ← t − w[k]
24  if t = 0 then return (YES, π[X]) else return (FAIL)   ▷ not reached in practice: at m = 1 line 14 always fires
```

```
PREPROCESS(w, C)                                  ▷ w[1‥n] decreasing; ARCS-FIXED builds C at lines 4–7, ARCS passes it
 1  S[n+1] ← 0;  V[n+1] ← 0
 2  for k ← n downto 1
 3      S[k] ← S[k+1] + w[k];  V[k] ← V[k+1] + w[k]²/4
 4  C ← {2, 3, …, Q₀}                                ▷ candidate moduli
 5  for i ← 1 to PAIRS (none if n < 2)               ▷ almost divisors: gcds of random pairs (fixed seed)
 6      pick two distinct positions at random, with weights a, b;  g ← gcd(a, b)
 7      C ← C ∪ {d : d | g, 2 ≤ d ≤ DCAP}
 8  (N, E) ← CLASS-COUNTS(w, C)
 9  for k ← 1 to n + 1                               ▷ dynamic moduli: Sel[k] = the moduli whose arc deviates
10      m ← n − k + 1;  ε ← min(1, C_EPS/m)  (ε ← 1 if m = 0)
11      Sel[k] ← {q ∈ C : max_c |q·N_q[k][c]·2^{E_q[k] − m} − 1| ≥ ε}
12  return (S, V, N, E, Sel)
```

```
CLASS-COUNTS(w, C)          ▷ N_q[k][c] ∝ #{X ⊆ {k‥n} : Σ_X w ≡ c (mod q)}, in floating point
 1  for each q ∈ C
 2      N_q[n+1] ← (1, 0, …, 0);  E_q[n+1] ← 0
 3      for k ← n downto 1
 4          for c ← 0 to q − 1
 5              y[c] ← N_q[k+1][c] + N_q[k+1][(c − w[k]) mod q]   ▷ sums of non-negative numbers only
 6          e ← binary exponent of max_c y[c]
 7          N_q[k] ← 2^{−e}·y;  E_q[k] ← E_q[k+1] + e               ▷ true count = N_q[k][c]·2^{E_q[k]}
 8  return (N, E)
```

```
SCORE(F, k, T)                       ▷ log of the estimated number of subsets of w[k‥n] with sum T
 1  m ← n − k + 1;  S ← F.S[k];  v ← F.V[k]
 2  if T < 0 or T > S
 3      return −∞
 4  if m = 0
 5      if T = 0 then return (0, 0, 0) else return −∞
 6  b ← 0
 7  for each q ∈ F.Sel[k]
 8      x ← F.N_q[k][T mod q]
 9      if x = 0
10          return −∞                                   ▷ empty class: impossible branch
11      b ← max(b, ln q + ln x + (F.E_q[k] − m)·ln 2)   ▷ class correction ln(q·N_c/2^m); the moduli combine by the maximum, not the product
12  return (m·ln 2 − ½·ln(2πv) − (T − S/2)²/(2v) + b, m, v)
```

```
FILTERED-ENDGAME(B, t, λ)            ▷ B[1‥m]; λ = estimated number of solutions; returns indices into B, or NIL
                                     ▷ (the code returns the chosen weights, and arcs_solve maps them back to indices)
 1  m ← |B|
 2  if λ < 8 or m < 16
 3      if m > MMAX then return NIL      ▷ the same guard as line 11
 4      return MITM(B, t)
 5  P₀ ← max(3, ⌊λ/2⌋)
 6  for round ← 1 to ROUNDS
 7      P ← UNIFORM-PRIME(P₀, 2P₀);  r ← uniform integer in [0, P)
 8      J ← FILTERED-ROUND(B, t, P, r)
 9      if J ≠ NIL
10          return J
11  if m > MMAX
12      return NIL                        ▷ block too large for the full meet-in-the-middle
13  return MITM(B, t)
```

```
UNIFORM-PRIME(a, b)                  ▷ a prime uniform among the primes of [a, b) (Lemma K); needs 2 ≤ a < b
 1  repeat
 2      x ← uniform integer in [a, b)
 3  until x is prime
 4  return x

FILTERED-ROUND(B, t, P, r)           ▷ one round of §5.6; the indices of A′ are shifted by ⌊m/2⌋
 1  m ← |B|;  A ← B[1‥⌊m/2⌋];  A′ ← B[⌊m/2⌋+1‥m]
 2  L ← RESIDUE-LIST(A, P, r);  L′ ← RESIDUE-LIST(A′, P, (t − r) mod P)
 3  if L = ∅ or L′ = ∅
 4      return NIL
 5  sort L′ by sum
 6  return JOIN(L, L′, t)
```

```
THEOREM-MODE(W, T, R)                ▷ the algorithm of Theorem R″ (§6.7): disjoint blocks, no fallback
 1  M ← max W (or the M of the distribution);  m ← least integer with 2^m ≥ (σ√m)^{4/3}, σ² = (M² − 1)/12;  P₀ ← ⌊λ_m/2⌋
 2  π ← random permutation of 1‥n;  E_j ← π[(j−1)m+1 ‥ jm] for j = 1‥R;  G ← the rest, decreasing
 3  for j ← 1 to R
 4      (X, t) ← CENTRE-RULE(sums of the blocks E_i, i ≠ j;  T;  extra = S_G + S_{E_j})   ▷ whole blocks or nothing
 5      (Y, t) ← CENTRE-RULE(weights of G;  t;  extra = S_{E_j})                            ▷ Lemma A: |t − S_{E_j}/2| ≤ M/2
 6      if t < 0 or t > S_{E_j}
 7          continue
 8      P ← UNIFORM-PRIME(P₀, 2P₀) (P ← 3 if P₀ < 2);  r ← uniform integer in [0, P)
 9      J ← FILTERED-ROUND(W[E_j], t, P, r)                                              ▷ one round per block
10      if J ≠ NIL
11          check the sum and distinct indices;  return (YES, X ∪ Y ∪ E_j[J])
12  return (FAIL)

CENTRE-RULE(v[1‥k], t, extra)        ▷ Lemma A, in the given order
 1  R ← Σ v;  X ← ∅
 2  for i ← 1 to k
 3      R ← R − v[i];  c ← (R + extra)/2
 4      if |t − v[i] − c| ≤ |t − c|
 5          X ← X ∪ {i};  t ← t − v[i]
 6  return (X, t)
```

```
RESIDUE-LIST(A, P, r)                ▷ all subsets of A with sum ≡ r (mod P), as pairs (sum, mask)
                                     ▷ indices: those of A₂ are shifted by |A₁| (in the code: a shift of the mask)
 1  A₁ ← first half of A;  A₂ ← second half
 2  L₁ ← ALL-SUMS(A₁);  L₂ ← ALL-SUMS(A₂)
 3  sort L₂ by (sum mod P)
 4  out ← ∅
 5  for each (s₁, x₁) ∈ L₁
 6      for each (s₂, x₂) ∈ L₂ with s₂ ≡ r − s₁ (mod P)      ▷ the range is found by two binary searches
 7          out ← out ∪ {(s₁ + s₂, x₁ ∪ x₂)}
 8  return out
```

```
ALL-SUMS(A)                          ▷ the 2^|A| sums with their masks
 1  L ← ⟨(0, ∅)⟩
 2  for each a_j ∈ A
 3      L ← L ∥ ⟨(s + a_j, x ∪ {j}) : (s, x) ∈ L⟩
 4  return L

SORTED-SUMS(A)                       ▷ as ALL-SUMS, but sorted: MERGE-LISTS of [CLRS §35.5]
 1  L ← ⟨(0, ∅)⟩
 2  for each a_j ∈ A
 3      L ← MERGE(L, ⟨(s + a_j, x ∪ {j}) : (s, x) ∈ L⟩)     ▷ merge of two sorted lists, linear time
 4  return L

JOIN(L, L′, t)                       ▷ L′ sorted by sum; the indices of x′ are shifted by the length of the first half
 1  for each (s, x) ∈ L
 2      if BINARY-SEARCH(L′, t − s) finds (s′, x′)
 3          return x ∪ x′
 4  return NIL

MITM(B, t)
 1  L ← ALL-SUMS(B[1‥⌊m/2⌋]);  L′ ← SORTED-SUMS(B[⌊m/2⌋+1‥m])
 2  return JOIN(L, L′, t)
```

## Costs (Table 8 of the paper)
- PREPROCESS: O(n·Σ_{q∈C} q) floating-point operations, plus O(√w_max) per gcd pair for the divisors.
- Descent: O(n + Σ_k |Sel[k]|) per target.
- One round of the endgame: O(m·2^{m/4} + m·2^{m/2}/P).
- Full meet-in-the-middle: O(m·2^{m/2}) time and memory. Residue scan: O(m·2^{m/2}) time, O(2^{m/4}) memory.
- 64-bit sums: in ARCS-FIXED a block must satisfy m·max(w) < 2⁶³ (checked); ARCS switches to exact integers beyond it.
- In ARCS the cost of the endgame on the predicted block m* is computed before the descent (line 9).

## Guarantees
- every YES can be checked (sum and multiset);
- every NO carries a certificate: (q, c), checkable in integer arithmetic; (0, 0) when T is outside [0, S]; or, in ARCS,
  (−3, −3) when an exhaustive endgame ran on the whole instance (checkable by any exact search);
- FAIL asserts nothing, and carries its reason: in ARCS one of "predicted …", budget, scored-out, both-out, end,
  endgame, n>1020, weights must be positive;
- no parameter of ARCS or ARCS-FIXED affects correctness: the parameters decide only how often an answer is reached
  instead of FAIL, and in how long;
- ARCS records its derived parameters and every random draw, so a run is replayable.
