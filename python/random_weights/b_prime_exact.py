"""Proposition B' (§6.3): the second moment of the endgame count against its expansion, computed exactly by convolution.
   Unconditional (on S_E = u mod 2): E Z^2 / (E Z)^2 = 1 + (1 + [u=0])/EZ + kappa/m + c2/m^2 + O(m^-3).
   Conditional on S_E = s (Lemma B'''): E[Z^2|s] / Zbar^2 = 1 + (1 + [u=0])/Zbar + kappa_c/m + gamma z/m^{3/2} + O(m^-2).
   Prints the remainder R after the stated terms, R*m^2 (unconditional and centre) and R*m^{3/2}/z (off centre).
   usage: python3 b_prime_exact.py"""
import numpy as np
from math import lgamma, exp, log, sqrt, comb

def constants(M):
    w = np.arange(1, M + 1, dtype=float); mu = w.mean(); S = w - mu; E2 = (w ** 2).mean(); V = w ** 2 - E2
    css = (S * S).mean(); cvs = (V * S).mean(); cvv = (V * V).mean()
    A = cvv - cvs ** 2 / css; R = V - cvs / css * S; B = (R * R * S).mean() / css
    kappa = cvv / (4 * E2 ** 2); kappa_c = A / (4 * E2 ** 2)
    gamma = sqrt(css) * (B - 2 * cvs / (css * E2) * A) / (4 * E2 ** 2)
    return kappa, kappa_c, gamma

def unconditional(M, ms):
    kappa = constants(M)[0]
    step = np.zeros(2 * M + 1); step[:M] = 1; step[M + 1:] = 1; step /= step.sum()   # law of eps*w, offset M
    P = [np.array([1.0])]
    for k in range(1, max(ms) + 1): P.append(np.convolve(P[-1], step))
    p = lambda k, v: P[k][v + k * M] if 0 <= v + k * M < len(P[k]) else 0.0
    for m in ms:
        for u in (0, 1):
            EZ = 2 ** m * p(m, u) * 2                  # on the event S_E = u (mod 2), of probability 1/2 for M even
            EZ2 = 2 * sum(exp(lgamma(m + 1) - lgamma(k + 1) - lgamma(m - k + 1) + m * log(2)) * p(m - k, u) * p(k, 0) for k in range(m + 1))
            R = EZ2 / EZ ** 2 - 1 - (1 + (u == 0)) / EZ - kappa / m
            print(f"unconditional M={M} m={m} u={u}  R={R:+.3e}  R*m^2={R * m * m:+.3f}")

def conditional(M, m, zs, us):
    kappa, kappa_c, gamma = constants(M)
    step = np.ones(M) / M; P = [np.array([1.0])]
    for k in range(1, m + 1): P.append(np.convolve(P[-1], step))
    pr = lambda k, v: P[k][v - k] if 0 <= v - k < len(P[k]) else 0.0
    lb = lambda n, k: lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)
    def Zc(j, v, t):                                   # E[#eps : sum eps w = v | S_j = t]
        if (t + v) % 2: return 0.0
        pt = pr(j, t)
        if pt == 0: return 0.0
        return sum(exp(lb(j, i)) * pr(i, (t + v) // 2) * pr(j - i, (t - v) // 2) for i in range(j + 1)) / pt
    w = np.arange(1, M + 1); mu = w.mean(); sd = w.std()
    for z in zs:
        for u in us:
            s = int(round(m * mu + z * sd * sqrt(m)))
            if (s - u) % 2: s += 1
            Zb = Zc(m, u, s); ps = pr(m, s); tot = 0.0
            for k in range(m + 1):
                ck = exp(lb(m, k))
                for s1 in range(m - k, (m - k) * M + 1):
                    q = pr(m - k, s1) * pr(k, s - s1)
                    if q: tot += ck * q / ps * Zc(m - k, u, s1) * Zc(k, 0, s - s1)
            R = tot / Zb ** 2 - 1 - (1 + (u == 0)) / Zb - kappa_c / m
            extra = f"R*m^2={R * m * m:+.3f}" if z == 0 else f"R*m^1.5/z={R * m ** 1.5 / z:+.4f} (gamma={gamma:+.4f})"
            print(f"conditional M={M} m={m} z={z} u={u}  R={R:+.3e}  {extra}", flush=True)

for M in (16, 64, 256):
    k, kc, g = constants(M); print(f"M={M}: kappa={k:.5f} kappa_c={kc:.5f} gamma={g:+.5f}")
unconditional(16, [20, 40, 80]); unconditional(64, [20, 40, 80]); unconditional(256, [20, 40])
for m in (28, 40, 56): conditional(16, m, (0.0,), (1,))
for m in (20, 40, 80, 120): conditional(16, m, (1.0, 2.0), (1,))
