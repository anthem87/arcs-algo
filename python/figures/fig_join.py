"""Figure (§5.6, the filtered endgame): the intersection, on one run of ARCS (195 multiples of 1009 + 5 others, n = 200).
   The remaining block is split into halves A and B. A round draws a prime P and a residue r and keeps only the sums of A
   that are = r (mod P) (vertical lines) and the sums of B that are = t - r (mod P) (horizontal lines).
   A solution is a vertical and a horizontal line that cross on the line a + b = t.
   Left: the round that finds the crossing, whole plane. Right: zoom around the crossing.
   usage: python3 fig_join.py"""
import matplotlib.pyplot as plt
from figstyle import *
from arcs_trace import run
D = run(); EG = D["endgame"]; t = EG["t"]; R = EG["rounds"][-1]
assert R["pair"] is not None and sum(R["pair"]) == t
XA, YB = sum(EG["A"]), sum(EG["B"])
a0, b0 = R["pair"]

setup()
fig, axs = plt.subplots(1, 2, figsize=(6.4, 3.2), gridspec_kw={"wspace": 0.3})
for j, ax in enumerate(axs):
    for x in R["sumsA"]: ax.axvline(x, color=BLUE, lw=0.5, alpha=0.6)
    for y in R["sumsB"]: ax.axhline(y, color=ORANGE, lw=0.5, alpha=0.6)
    ax.plot([0, XA], [t, t - XA], color=AQUA, lw=1.6)
    ax.scatter([a0], [b0], s=60, facecolors="none", edgecolors=INK, lw=1.4, zorder=5)
    ax.grid(False); ax.set_xlabel("sum from A"); ax.set_ylabel("sum from B" if j == 0 else "")
    ax.ticklabel_format(style="sci", scilimits=(0, 0))
axs[0].set_xlim(0, XA); axs[0].set_ylim(0, YB)
w = 0.03 * XA
axs[1].set_xlim(a0 - w, a0 + w); axs[1].set_ylim(b0 - w, b0 + w)
axs[1].text(a0, b0 + 0.12 * w, "  a + b = t", color=INK, fontsize=8)
axs[0].set_title(f"{len(R['sumsA'])} sums of A ≡ r, {len(R['sumsB'])} sums of B ≡ t − r (mod P)", loc="left", fontsize=8.5)
axs[1].set_title("zoom: the crossing on the line a + b = t", loc="left", fontsize=8.5)
save(fig, "fig_join")
print(f"rounds {len(EG['rounds'])}, P = {R['P']}, filtered {len(R['sumsA'])} + {len(R['sumsB'])}, |A| = {len(EG['A'])}, |B| = {len(EG['B'])}")
