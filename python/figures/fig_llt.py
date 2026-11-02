"""Figure (§6.2, Lemma B0'): the local limit theorem uniform in the size of the weights.
   S_k is a sum of k independent weights uniform in {1, ..., M}; the distribution is computed by exact convolution (float64).
   Plotted: the measured constant C(k) = sigma k^(3/2) max_v |Pr(S_k = v) - g_k(v)| against k, for each M,
   with the Edgeworth limit 0.0599 (M -> inf) and 0.0997 = 0.0599 * 5/3 (M = 2), and the proved bound C(k, M) for M = 2 and M = 317.
   usage: python3 fig_llt.py [kmax]"""
import sys
import numpy as np, matplotlib.pyplot as plt
from figstyle import *
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 160
MS = [2, 3, 5, 16, 64, 317]

def measured(M):
    mu, s2 = (M + 1) / 2, (M * M - 1) / 12
    p = np.ones(M) / M; d = np.array([1.0]); out = []
    for k in range(1, KMAX + 1):
        d = np.convolve(d, p)
        if k < 2: continue
        v = np.arange(len(d)) + k; z = (v - k * mu) / np.sqrt(k * s2)
        g = np.exp(-z * z / 2) / np.sqrt(2 * np.pi * k * s2)
        out.append((k, np.abs(d - g).max() * np.sqrt(s2) * k ** 1.5))
    return np.array(out)

def bound(k, M):
    q = 1 / (M * np.sin(np.pi / (2 * M)))
    return 0.0599 * (M * M + 1) / (M * M - 1) + 0.34 / k + k ** 1.5 * (q ** (k - 2) / np.sqrt(12) + (0.41 / k + 0.11) * np.exp(-0.308 * k))

setup()
fig, ax = plt.subplots(figsize=(6.2, 3.4))
shades = [ORANGE, "#c98a5f", AQUA, "#6aa3d9", "#3f8de0", BLUE]
for M, c in zip(MS, shades):
    r = measured(M)
    ax.plot(r[:, 0], r[:, 1], color=c, lw=1.4, label=f"M = {M}")
    print(f"M={M}: C(2)={r[0,1]:.4f}  C({KMAX})={r[-1,1]:.4f}")
ks = np.arange(2, KMAX + 1)
for M, ls in [(2, ":"), (317, "--")]:
    ax.plot(ks, bound(ks, M), color=MUTED, lw=1.0, ls=ls, label=f"bound C(k, M), M = {M}")
ax.axhline(0.0599, color=INK2, lw=0.8); ax.text(KMAX, 0.0599, "0.0599 ", ha="right", va="top", fontsize=8, color=INK2)
ax.axhline(0.0997, color=INK2, lw=0.8); ax.text(KMAX, 0.0997, "0.0997 ", ha="right", va="bottom", fontsize=8, color=INK2)
ax.set_xscale("log"); ax.set_yscale("log"); ax.set_ylim(0.03, 3)
ax.set_xlabel("number of weights k"); ax.set_ylabel("σ k^{3/2} max_v |Pr(S_k = v) − g_k(v)|")
ax.legend(ncol=2, loc="upper right")
ax.set_title("Measured constant of the local limit theorem: it tends to the Edgeworth value, uniformly in M", loc="left")
save(fig, "fig_llt")
