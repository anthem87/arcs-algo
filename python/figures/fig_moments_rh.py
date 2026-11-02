"""Figure (§4.4, Proposition 3_0): E_k(N) = sum_{p<=N} p^k - li(N^{k+1}), normalised by N^{k+1/2}, for k = 0, 1, 2
   (k = 1: the centre, k = 2: the width of the central Gaussian of the prime subset sums). RH is equivalent to a
   one-sided bound E_k(N) <= C_eps N^{k+1/2+eps}, for each k. 25 values of N from 10^2 to 10^8 (log-spaced).
   This is a finite computation; it proves nothing about RH.
   usage: python3 fig_moments_rh.py [Nmax]"""
import sys, math
import numpy as np, matplotlib.pyplot as plt, mpmath as mp
from figstyle import *
Nmax = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**8
sieve = np.ones(Nmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.float64)
cs = {k: np.cumsum(P.astype(np.longdouble) ** k) for k in (0, 1, 2)}
Ns = np.unique(np.round(np.logspace(2, math.log10(Nmax), 25)).astype(np.int64))
mp.mp.dps = 30; rows = []
for Nv in Ns:
    i = np.searchsorted(P, Nv, side="right") - 1
    r = [float((mp.mpf(str(cs[k][i])) - mp.li(mp.mpf(int(Nv)) ** (k + 1))) / mp.mpf(int(Nv)) ** (k + 0.5)) for k in (0, 1, 2)]
    rows.append((int(Nv), *r))
R = np.array(rows)
setup(); fig, ax = plt.subplots(figsize=(5.6, 3.0))
for k, col, lab in [(0, MUTED, "k = 0: π(N) − li N"), (1, ORANGE, "k = 1: centre (Σp − li N²)"), (2, BLUE, "k = 2: width (Σp² − li N³)")]:
    ax.plot(R[:, 0], R[:, k + 1], color=col, marker="o", ms=3, lw=1.4, label=lab)
ax.axhline(0, color=INK2, lw=0.8, ls="--"); ax.set_xscale("log")
ax.set_xlabel("N"); ax.set_ylabel(r"$E_k(N)\,/\,N^{k+1/2}$")
ax.set_title("Moments of the primes against li: all below 0 in the computed range", loc="left", fontsize=8.5)
ax.legend(loc="lower right", fontsize=7.5)
save(fig, "fig_moments_rh")
print("E2/N^2.5 range:", R[:, 3].min(), R[:, 3].max(), " E1:", R[:, 2].min(), R[:, 2].max(), " E0:", R[:, 1].min(), R[:, 1].max())
