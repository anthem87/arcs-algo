"""Figure: the descent (gap between the two branch scores, log scale) of ARCS on one instance with an almost divisor (195 multiples of 1009 + 5 others).
   At each step k the two branches are scored on the suffix; the descent follows the larger score.
   A branch whose class mod 1009 is empty scores -inf (marked at the bottom). The descent hands over to the
   filtered endgame when the peak density of the suffix falls below λ* (vertical line).
   usage: python3 fig_descent.py   (needs arcs_dyn.py on the path)"""
import sys, math, random
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "algorithm"))
import matplotlib.pyplot as plt
from arcs_dyn import ArcsDyn
from figstyle import *
RHO, CAP = 5e4, 60
random.seed(4)
W = [1009 * random.randint(1, 10**9) for _ in range(195)] + [random.randint(1, 1009 * 10**9) for _ in range(5)]
W.sort(reverse=True); T = sum(w for w in W if random.random() < 0.5)
F = ArcsDyn(W); t = T; ks, s_ch, s_rej, blocked, hand = [], [], [], [], None
for k, w in enumerate(W):
    r = F.score(k, t); sc, m, v = r
    if m <= CAP and m * math.log(2) - 0.5 * math.log(2 * math.pi * max(v, 1)) < math.log(RHO): hand = k; break
    si = F.score(k + 1, t - w); so = F.score(k + 1, t)
    si = si[0] if si != -math.inf else -math.inf; so = so[0] if so != -math.inf else -math.inf
    take = si >= so; ch, rej = (si, so) if take else (so, si)
    ks.append(k + 1); s_ch.append(ch); s_rej.append(rej if rej != -math.inf else float("nan"))
    if rej == -math.inf: blocked.append(k + 1)
    if take: t -= w
setup(); fig, ax = plt.subplots(figsize=(6.2, 3.0))
L2 = 1 / math.log(2)
gap = [(c - r) * L2 for c, r in zip(s_ch, s_rej) if r == r]
kg = [k for k, r in zip(ks, s_rej) if r == r]
top = 10 ** math.ceil(math.log10(max(gap)) + 1)
ax.plot(kg, gap, color=BLUE, lw=1.2, marker="o", ms=2.2, label="score gap between the two branches")
ax.scatter(blocked, [top] * len(blocked), marker="x", s=22, color=ORANGE, lw=1.3, zorder=3,
           label="other branch impossible: its class mod 1009 is empty")
ax.set_yscale("log"); ax.set_ylim(min(gap) / 3, top * 4)
ax.axvline(hand + 1, color=MUTED, lw=1.0, ls="--"); ax.text(hand + 1, min(gap) / 2.5, " endgame", color=INK2, va="bottom", fontsize=8)
ax.set_xlabel("step k (weights sorted decreasingly)"); ax.set_ylabel("log₂ (chosen / other)")
ax.legend(loc="upper left", bbox_to_anchor=(0, 0.93))
ax.set_title(f"Descent on 195 multiples of 1009 + 5 others (n = 200): {len(blocked)} branches cut by the arc, endgame on the last {len(W)-hand} weights", loc="left", fontsize=8.5)
save(fig, "fig_descent")
print(f"steps {len(ks)}, blocked branches {len(blocked)}, handover at k = {hand+1}")
