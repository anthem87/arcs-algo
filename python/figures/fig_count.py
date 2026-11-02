"""Figure (§3.4, §3.6, Table 3): the count r_N(T) of subsets of W_N = {1} U {p <= N} with sum T, against the
   Gaussian at the lattice scale and the Edgeworth expansion of order 3 in 1/n (as in BENCH5 P4).
   The exact counts come from a floating-point DP with power-of-two rescaling (non-negative sums only).
   usage: python3 fig_count.py [N]"""
import sys, math
import numpy as np, matplotlib.pyplot as plt
from sympy import primerange
from figstyle import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
W = [1] + list(primerange(2, N + 1)); n = len(W); S = sum(W); s = math.sqrt(sum(w * w for w in W) / 4)
def log_counts_all(W, Tmax):
    dp = np.zeros(Tmax + 1); dp[0] = 1.0; E = 0
    for w in W:
        if w <= Tmax: dp[w:] = dp[w:] + dp[:-w]
        e = int(np.frexp(dp.max())[1])
        if e > 900: dp = np.ldexp(dp, -e); E += e
    with np.errstate(divide="ignore"): return np.log(dp) + E * math.log(2)
k4 = -sum(float(w)**4 for w in W) / 8; k6 = sum(float(w)**6 for w in W) / 4; k8 = -17 * sum(float(w)**8 for w in W) / 16
a4, a6, a8 = k4 / 24, k6 / 720, k8 / 40320
C = {4: a4, 6: a6, 8: a4 * a4 / 2 + a8, 10: a4 * a6, 12: a4**3 / 6}
def log_est(T, edge):
    z = (T - S / 2) / s; He = [1.0, z]
    for k in range(2, 13): He.append(z * He[-1] - (k - 1) * He[-2])
    corr = 1.0 + (sum(c * He[k] / s**k for k, c in C.items()) if edge else 0.0)
    return n * math.log(2) - math.log(s) - 0.5 * math.log(2 * math.pi) - z * z / 2 + math.log(corr)
Ts = np.unique(np.linspace(S / 2 - 4.2 * s, S / 2, 400).astype(int))   # symmetric: r(T) = r(S - T)
L = log_counts_all(W, int(Ts.max()))
z = (Ts - S / 2) / s
eg = np.array([abs(math.expm1(log_est(T, False) - L[T])) for T in Ts])
ee = np.array([abs(math.expm1(log_est(T, True) - L[T])) for T in Ts])
setup(); fig, ax = plt.subplots(figsize=(5.4, 3.0))
ax.plot(-z, eg, color=ORANGE, lw=1.4, label="Gaussian")
ax.plot(-z, np.maximum(ee, 1e-16), color=BLUE, lw=1.4, label="Edgeworth, order 3 in 1/n")
ax.set_yscale("log"); ax.set_xlabel("|T − S/2| / σ"); ax.set_ylabel("relative error against the exact count")
ax.set_title(f"Subset sums of {{1}} ∪ {{p ≤ {N}}}: the count r_N(T) is a Gaussian ({n} weights, r up to $2^{{{n}}}$)", loc="left", fontsize=8.5)
ax.legend(loc="upper left")
save(fig, "fig_count")
print(f"at z=0: Gauss {eg[np.argmin(abs(z))]:.1e}, Edgeworth {ee[np.argmin(abs(z))]:.1e}")
