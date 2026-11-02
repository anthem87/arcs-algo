"""Figure (§5, the descent): take or skip, on one run of ARCS (195 multiples of 1009 + 5 others, n = 200).
   Top: a window of consecutive steps of the descent (the window with the most cuts). At step k both branches are
   scored on the suffix (expected number of completions); the larger one is followed (filled). A branch whose class mod 1009 is empty is cut by the arc (x).
   Bottom: log2 of the peak density of the remaining block along the whole descent; the descent hands over to the
   exact endgame when it falls below lambda* (dashed).
   usage: python3 fig_take_skip.py [steps shown]"""
import sys, math
import matplotlib.pyplot as plt
from figstyle import *
from arcs_trace import run, LAMBDA_STAR
RED, PALE = "#e34948", "#d9d8d3"
K = int(sys.argv[1]) if len(sys.argv) > 1 else 24
D = run(); st = D["steps"]; hk = D["hand"]["k"]; L2 = 1 / math.log(2)

setup()
fig, (a1, a2) = plt.subplots(2, 1, figsize=(6.4, 4.6), gridspec_kw={"height_ratios": [1.15, 1], "hspace": 0.45})
iscut = [s["s_in"] is None or s["s_out"] is None for s in st]
k0 = max(range(len(st) - K + 1), key=lambda i: sum(iscut[i:i + K]))
a1.set_xlim(k0 + 0.3, k0 + K + 0.7); a1.set_ylim(-0.6, 1.6); a1.grid(False)
a1.set_yticks([1, 0]); a1.set_yticklabels(["take", "skip"]); a1.tick_params(axis="y", length=0, labelsize=9)
a1.spines["left"].set_visible(False)
for s in st[k0:k0 + K]:
    x = s["k"] + 1
    for y, val, is_take in [(1, s["s_in"], True), (0, s["s_out"], False)]:
        chosen = is_take == s["take"]
        if val is None:
            a1.scatter(x, y, s=95, color=RED, zorder=3); a1.scatter(x, y, s=40, marker="x", color="white", lw=1.6, zorder=4)
        else:
            a1.scatter(x, y, s=95 if chosen else 60, color=BLUE if chosen else PALE, zorder=3)
ncut = sum(1 for s in st if s["s_in"] is None or s["s_out"] is None)
a1.set_xlabel("step k (weights sorted decreasingly)")
a1.set_title(f"Take or skip: follow the larger score; red = branch cut by the arc mod 1009 ({ncut} cuts in {len(st)} steps)", loc="left", fontsize=8.5)

ks = [s["k"] + 1 for s in st]; pk = [s["peak"] * L2 for s in st]
a2.plot(ks, pk, color=BLUE, lw=1.6, label="log₂ peak density of the remaining block")
cut = [(s["k"] + 1, s["peak"] * L2) for s in st if s["s_in"] is None or s["s_out"] is None]
a2.scatter([c[0] for c in cut], [c[1] for c in cut], s=10, color=RED, zorder=3, label="step with a branch cut by the arc")
a2.axhline(math.log2(LAMBDA_STAR), color=ORANGE, lw=1.0, ls="--")
a2.text(2, math.log2(LAMBDA_STAR) + 4, f"λ* = 5·10⁴", color=ORANGE, fontsize=8)
a2.axvline(hk + 1, color=MUTED, lw=0.9, ls=":"); a2.text(hk + 1, max(pk) * 0.55, " endgame:\n last " + str(len(D["W"]) - hk) + " weights", fontsize=7.5, color=INK2)
a2.set_xlabel("step k"); a2.set_ylabel("log₂ density"); a2.legend(loc="upper right")
save(fig, "fig_take_skip")
print(f"steps {len(st)}, cuts {ncut}, handover at k = {hk + 1}")
