"""Figure (§3.2, Lemma 1): the levels of the arcs of the prime product F_N(z) = prod_{w in W_N} (1 + z^w),
   W_N = {1} U {p <= N}. Per-weight excess over the sea, (1/|W_N|) sum_w log|2 cos(pi w theta)|:
   grey: on a fine grid of theta (the sea, at level 0); dots: exactly at theta = a/q, q <= 40, with the vanishing
   factor removed (F*), against the level of Lemma 1, Lambda(q/2)/phi(q) for q even, 0 for q odd.
   usage: python3 fig_arc_levels.py [N]"""
import sys, math
import numpy as np, matplotlib.pyplot as plt
from sympy import primerange, totient, factorint
from figstyle import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
W = np.array([1] + list(primerange(2, N + 1)), dtype=np.float64); n = len(W)
def excess(theta):
    out = np.empty(len(theta))
    for i in range(0, len(theta), 4000):
        th = theta[i:i + 4000, None]
        out[i:i + 4000] = np.log(np.abs(2 * np.cos(np.pi * ((W[None, :] * th) % 1.0)))).sum(1) / n
    return out
def Lam(m):
    f = factorint(m); return math.log(next(iter(f))) if len(f) == 1 else 0.0
def level(q): return Lam(q // 2) / int(totient(q)) if q % 2 == 0 else 0.0
grid = np.linspace(1e-4, 0.5, 60001)
with np.errstate(divide="ignore"): ys = excess(grid)
pts = []
for q in range(3, 41):
    for a in range(1, q // 2 + 1):
        if math.gcd(a, q) != 1: continue
        th = a / q; v = 0.0; k = 0
        for w in W:
            c = abs(2 * math.cos(math.pi * ((w * a) % q) / q))
            if c > 1e-12: v += math.log(c); k += 1
        pts.append((th, v / n, level(q), q))
setup(); fig, ax = plt.subplots(figsize=(6.6, 3.0))
ax.plot(grid, np.clip(ys, -1.2, None), color=MUTED, lw=0.3, alpha=0.6, label="fine grid of θ")
em = [p for p in pts if p[2] > 0]; no = [p for p in pts if p[2] == 0]
for x, y, l, q in em: ax.plot([x - 0.006, x + 0.006], [l, l], color=INK2, lw=1.0)
ax.scatter([p[0] for p in em], [p[1] for p in em], s=14, color=BLUE, zorder=3, label=r"$a/q$ with $q = 2^k$ or $2p^j$ (emerging)")
ax.scatter([p[0] for p in no], [p[1] for p in no], s=8, color=ORANGE, zorder=3, label="other a/q, q ≤ 40")
for x, y, l, q in em:
    if q <= 14 and x in (1/4, 1/6, 1/8, 1/10, 1/14, 3/10, 3/8, 3/14, 5/14):
        ax.annotate(f"{round(x*q)}/{q}", (x, y), xytext=(0, 5), textcoords="offset points", ha="center", fontsize=7, color=INK2)
ax.axhline(0, color=INK2, lw=0.8, ls="--")
ax.set_xlim(0, 0.5); ax.set_ylim(-0.25, 0.75)
ax.set_xlabel("θ"); ax.set_ylabel("excess over the sea, per weight")
ax.set_title(f"Arcs of the prime product at N = {N} ({n} weights); ticks: level of Lemma 1, Λ(q/2)/φ(q)", loc="left", fontsize=8.5)
ax.legend(loc="upper right", fontsize=7.5)
save(fig, "fig_arc_levels")
dev = max(abs(y - l) for _, y, l, _ in pts); print(f"max |exact - Lemma 1 level| over a/q, q<=40: {dev:.3f} (O_q(1)/n + height/n)")
