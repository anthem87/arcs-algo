"""Figure (§3, arcs of the prime product): emergence of the arcs as N grows.
   F_N(z) = prod_{w in W_N} (1 + z^w), W_N = {1} U {p <= N}; per-weight level (1/|W_N|) log|F_N(e(theta))| on theta in (0, 1/2].
   For small N the profile is irregular; as N grows the sea settles at a common level and the arcs at a/q with q even
   (dashed: a/q with q = 4, 6, 10; at theta = 1/2 the factor 1 + z of the weight 1 vanishes) separate from it.
   usage: python3 fig_arcs_growth.py [N1 N2 N3 N4]"""
import sys
import numpy as np, matplotlib.pyplot as plt
from figstyle import *
NS = [int(a) for a in sys.argv[1:5]] if len(sys.argv) >= 5 else [30, 200, 1000, 5000]

def primes(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]

grid = np.linspace(2e-4, 0.4998, 40001)
def level(N):
    W = np.concatenate(([1.0], primes(N).astype(np.float64))); out = np.empty(len(grid))
    for i in range(0, len(grid), 2000):
        th = grid[i:i + 2000, None]
        with np.errstate(divide="ignore"):
            out[i:i + 2000] = np.log(np.abs(2 * np.cos(np.pi * ((W[None, :] * th) % 1.0)))).sum(1) / len(W)
    return out, len(W)

marks = [(1, 10), (1, 6), (1, 4), (3, 10)]
setup()
fig, axs = plt.subplots(len(NS), 1, figsize=(6.2, 1.25 * len(NS) + 0.6), sharex=True, gridspec_kw={"hspace": 0.35})
for ax, N in zip(axs, NS):
    y, n = level(N)
    ax.plot(grid, np.maximum(y, -1.2), color=BLUE, lw=0.6)
    for a, q in marks:
        ax.axvline(a / q, color=ORANGE, lw=0.7, ls="--", alpha=0.7)
    ax.set_ylim(-1.2, 0.9); ax.set_yticks([-1, 0, 0.5])
    ax.set_title(f"N = {N}  ({n} weights)", loc="left", fontsize=8.5)
    print(f"N={N}: |W|={n}, median level {np.median(y[np.isfinite(y)]):.3f}")
for a, q in marks:
    axs[0].text(a / q, 0.95, f"{a}/{q}", transform=axs[0].get_xaxis_transform(), ha="center", va="bottom", fontsize=8, color=ORANGE)
axs[-1].set_xlabel("θ"); axs[len(NS) // 2].set_ylabel("(1/|W_N|) log |F_N(e(θ))|")
save(fig, "fig_arcs_growth")
