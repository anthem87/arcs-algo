"""Figure: the selection rule of the dynamic moduli (§5.7, Lemma 5.3).
   delta_q(k) = max_c |q N_c / 2^m - 1| along the suffixes, against the threshold eps_k = min(1, 1/m).
   Left: 195 multiples of 1009 + 5 others. Right: 200 random weights. A modulus is read where its curve is above
   the threshold. usage: python3 fig_dynamic_q.py"""
import sys, random
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "algorithm"))
import numpy as np, matplotlib.pyplot as plt
from arcs_dyn import ArcsDyn
from figstyle import *
def deltas(W, qs):
    F = ArcsDyn(W, fixed=qs, C_EPS=0); n = len(W); out = {q: [] for q in qs}; ms = []
    for k in range(n):
        m = n - k; ms.append(m)
        for q in qs:
            sc = float(q) * np.ldexp(1.0, int(F.E[q][k]) - m)
            out[q].append(float(np.max(np.abs(F.N[q][k] * sc - 1.0))))
    return np.array(ms), out
random.seed(4)
A = sorted([1009 * random.randint(1, 10**9) for _ in range(195)] + [random.randint(1, 1009 * 10**9) for _ in range(5)], reverse=True)
B = sorted([random.randint(1, 10**10) for _ in range(200)], reverse=True)
small = list(range(2, 25))
setup(); fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.8), sharey=True)
for ax, W, title, big in [(axs[0], A, "195 multiples of 1009 + 5 others", 1009), (axs[1], B, "200 random weights in [1, 10¹⁰]", None)]:
    qs = small + ([big] if big else []); ms, d = deltas(W, qs)
    floor = 1e-16   # double precision: deviations below this are rounding
    mx = np.maximum(np.max([d[q] for q in small], axis=0), floor)
    if big: ax.plot(ms, np.maximum(d[big], floor), color=BLUE, label="$q = 1009$")
    ax.plot(ms, mx, color=ORANGE, lw=1.4, label="max over $q \\leq 24$")
    ax.plot(ms, np.minimum(1, 1 / ms), color=INK2, lw=1.0, ls="--", label="threshold $\\varepsilon = \\min(1, 1/m)$")
    ax.set_yscale("log"); ax.set_xscale("log"); ax.invert_xaxis(); ax.set_ylim(5e-17, 3e3)
    ax.set_xlabel("suffix size m"); ax.set_title(title, loc="left")
axs[0].set_ylabel(r"deviation $\delta_q$ of the class counts")
fig.legend(*axs[0].get_legend_handles_labels(), loc="lower center", ncol=3, bbox_to_anchor=(0.5, -0.13))
axs[1].text(0.03, 0.97, "no modulus above the threshold\nuntil the last ~15 weights", transform=axs[1].transAxes, ha="left", va="top", fontsize=8, color=INK2)
save(fig, "fig_dynamic_q")
