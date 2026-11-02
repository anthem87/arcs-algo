"""Figure: cost of the endgame on one block of m random weights, plain meet-in-the-middle against the filtered
   endgame of §5.6, with the weights' range chosen so that the block holds about Z ~ 200 solutions.
   Times are medians over a few blocks, one core. With Z fixed the prime P ~ Z/2..Z is fixed too, so for large m both
   costs grow like 2^{m/2} and the filter divides the plain cost by about P (dotted line); at small m the 2^{m/4}
   quarter lists and the overhead dominate, and the filter does not pay (as in Table 9''). usage: python3 fig_endgame.py"""
import sys, time, math, random, statistics
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "algorithm"))
import matplotlib.pyplot as plt
from endgame_fast import mitm_merge, endgame_mod
from figstyle import *
import json, os
Z = 200; rng = random.Random(5); rows = []
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig_endgame_rows.json")          # measured times; delete it to measure again
if os.path.exists(CACHE): rows = [tuple(r) for r in json.load(open(CACHE))]
for m in ([] if rows else [20, 24, 28, 32, 36, 40, 44]):
    M = int(2**m / (Z * math.sqrt(2 * math.pi * m / 12)))          # 2^m / (M sqrt(2 pi m/12)) ~ Z
    tp, tf = [], []
    for _ in range(5 if m < 40 else 3):
        W = [rng.randint(1, M) for _ in range(m)]; T = sum(W) // 2 + rng.randint(-M // 2, M // 2)
        t0 = time.time(); a = mitm_merge(W, T); tp.append(time.time() - t0)
        t0 = time.time(); b, _ = endgame_mod(W, T, Z, rng); tf.append(time.time() - t0)
        assert (a is None) == (b is None) or b is not None
    rows.append((m, statistics.median(tp), statistics.median(tf))); print(rows[-1], flush=True)
json.dump(rows, open(CACHE, 'w'))
ms = [r[0] for r in rows]; P = [r[1] * 1e3 for r in rows]; Fl = [r[2] * 1e3 for r in rows]
setup(); fig, ax = plt.subplots(figsize=(5.0, 3.0))
ax.plot(ms, P, color=ORANGE, marker="o", ms=4, label="plain meet-in-the-middle")
ax.plot(ms, Fl, color=BLUE, marker="o", ms=4, label="filtered endgame")
Pm = 1.5 * Z / 2                                                   # P is uniform among the primes of [Z/2, Z): mean about 0.75 Z
ax.plot(ms, [p / Pm for p in P], color=MUTED, lw=1.0, ls=":", label="plain divided by P ≈ 150 (P uniform prime in [λ/2, λ))")
ax.set_yscale("log"); ax.set_xlabel("block size m"); ax.set_ylabel("time per block (ms)")
ax.set_title(f"Endgame on one block holding about {Z} solutions: the filter divides the cost by about P", loc="left", fontsize=8.5); ax.legend(loc="upper left")
save(fig, "fig_endgame")
