"""Proposition 2.3: the subset sums of the primes up to N, without the weight 1.

For N >= 5 the missing values in [0, Sigma_N] are exactly {1, 4, 6, Sigma_N-6, Sigma_N-4, Sigma_N-1}
(for N = 2, 3: {1} and {1, 4}); for N >= 7 the reachable set has 7 maximal intervals.
Checked for every prime N < LIMIT with an exact bitset (Python big integer):
the full hole set while Sigma_N < FULL, the count of reachable values and both ends beyond.
Also checks the induction margin D_n = Sigma_{n-1} - p_n >= 13 used in the proof.
"""
import sympy

LIMIT, FULL = 20000, 3000

def expected(S):
    return sorted(x for x in {1, 4, 6, S - 6, S - 4, S - 1} if 0 <= x <= S)

mask, S, prev_S, checked = 1, 0, 0, 0
for n, p in enumerate(sympy.primerange(2, LIMIT), 1):
    if n >= 6:
        assert prev_S - p >= 13, (n, p)                 # D_n = Sigma_{n-1} - p_n >= 13 for n >= 6
    prev_S = S + p
    mask |= mask << p
    S += p
    if p < 5:
        continue
    if S < FULL:
        holes = [t for t in range(S + 1) if not (mask >> t) & 1]
        assert holes == expected(S), (p, holes)
    else:
        low, high = mask & ((1 << 60) - 1), mask >> (S - 59)     # one shift each: the two ends
        ends = [t for t in range(60) if not (low >> t) & 1] + \
               [S - 59 + t for t in range(60) if not (high >> t) & 1]
        assert ends == expected(S), (p, ends)
        assert mask.bit_count() == S + 1 - 6, p      # exactly six holes in [0, S]
    if p >= 7 and S < FULL:          # beyond, 7 intervals follow from the six holes at the stated places
        runs = bin(mask)[2:][::-1][:S + 1].split("0")
        assert sum(1 for r in runs if r) == 7, p
    checked += 1
print(f"Proposition 2.3 verified for all {checked} primes 5 <= N < {LIMIT}; D_n >= 13 for 6 <= n.")
