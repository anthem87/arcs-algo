"""Proposition C' (§3.4): arc terms with the Edgeworth series to order s^-2, s^-3 and s^-4, tested on the exact counts
   at N = 500 (96 weights) with twisted Gaussian windows of width H at three centres.
   usage: python3 edgeworth_arcs3.py [H]   (default H = 120; at H = 60 the arc 1/8 shows window leakage)"""
import sys, math
import mpmath as mp, numpy as np
mp.mp.dps = 60
H = int(sys.argv[1]) if len(sys.argv) > 1 else 120

def primes(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

W = [1] + primes(500); S = sum(W)
r = [0] * (S + 1); r[0] = 1
for w in W:
    for t in range(S, w - 1, -1): r[t] += r[t - w]
e = lambda x: mp.expj(2 * mp.pi * x)

def He(k, z):
    h0, h1 = mp.mpf(1), z
    if k == 0: return h0
    for j in range(2, k + 1): h0, h1 = h1, z * h1 - (j - 1) * h0
    return h1

def cumulants(a, q):
    """Product of the non-vanishing factors, cumulants k[1..6] of the arc, and the vanishing weights."""
    F = mp.mpc(1); k = [mp.mpc(0)] * 7; zero = []
    for w in W:
        u = e(mp.mpf(w * a) / q)
        if abs(1 + u) < mp.mpf(10) ** -30:          # vanishing factor: w d/dT times e^{iwt/2} sinc(wt/2)
            zero.append(w); k[1] += mp.mpf(w) / 2; k[2] += mp.mpf(w) ** 2 / 12
            k[4] += -mp.mpf(w) ** 4 / 120; k[6] += mp.mpf(w) ** 6 / 252
        else:                                        # w * Bernoulli(p), p = u / (1 + u)
            F *= 1 + u; p = u / (1 + u)
            k[1] += w * p; k[2] += w ** 2 * p * (1 - p); k[3] += w ** 3 * p * (1 - p) * (1 - 2 * p)
            k[4] += w ** 4 * p * (1 - p) * (1 - 6 * p + 6 * p * p)
            k[5] += w ** 5 * p * (1 - p) * (1 - 2 * p) * (1 - 12 * p + 12 * p * p)
            k[6] += w ** 6 * p * (1 - p) * (1 - 30 * p + 150 * p ** 2 - 240 * p ** 3 + 120 * p ** 4)
    return F, k, zero

def term(T, F, k, zero, a, q, order):
    s = mp.sqrt(k[2]); z = (T - k[1]) / s; phi = mp.exp(-z * z / 2) / mp.sqrt(2 * mp.pi); c = {}
    if order >= 1: c[3] = k[3] / (6 * s ** 3); c[4] = k[4] / (24 * s ** 4); c[6] = k[3] ** 2 / (72 * s ** 6)
    if order >= 2: c[5] = k[5] / (120 * s ** 5); c[7] = k[3] * k[4] / (144 * s ** 7); c[9] = k[3] ** 3 / (1296 * s ** 9)
    if order >= 3:
        c[6] = c[6] + k[6] / (720 * s ** 6); c[8] = k[4] ** 2 / (1152 * s ** 8) + k[3] * k[5] / (720 * s ** 8)
        c[10] = k[3] ** 2 * k[4] / (1728 * s ** 10); c[12] = k[3] ** 4 / (31104 * s ** 12)
    if not zero: g = phi / s * (1 + sum(v * He(j, z) for j, v in c.items()))
    else: g = -phi / k[2] * (He(1, z) + sum(v * He(j + 1, z) for j, v in c.items())) * mp.fprod(zero)
    return e(-mp.mpf(T * a) / q) * F * g

print(f"H = {H};  ratio exact / predicted at Edgeworth order 1, 2, 3")
for q, a in [(1, 0), (8, 1), (6, 1), (10, 1), (10, 3), (4, 1), (14, 1)]:
    F, k, zero = cumulants(a, q)
    for d in (0, 150, -400):
        T0 = S // 2 + d; rng = range(T0 - 12 * H, T0 + 12 * H + 1)
        wnd = {t: mp.exp(-mp.mpf(t - T0) ** 2 / (2 * H * H)) for t in rng}
        Y = mp.fsum(r[t] * e(mp.mpf(a * t) / q) * wnd[t] for t in rng)
        R = [abs(Y / mp.fsum(term(t, F, k, zero, a, q, o) * e(mp.mpf(a * t) / q) * wnd[t] for t in rng)) for o in (1, 2, 3)]
        print(f"{a}/{q:<3d} T0 offset {d:5d}  " + "  ".join(f"{float(x):.6f}" for x in R), flush=True)
