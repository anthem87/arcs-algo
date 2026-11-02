"""Figure: outcome of the preregistered benchmark BENCH5 (one panel per problem with a yes/no answer).
   Reads the results file and recomputes every count from the records; the bar is the number of correct answers
   (subsets checked, NO certificates checked by checker5), the label the median time of the correct answers.
   usage: python3 fig_bench5.py [results.json]   (default: benchmarks/bench5_v2/results_v2.json)"""
import sys, json, statistics
import matplotlib.pyplot as plt
from figstyle import *
DEFAULT = __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "..", "benchmarks", "bench5_v2", "results_v2.json")
R = json.load(open(sys.argv[1] if len(sys.argv) > 1 else DEFAULT))
panels = [("P1", "feasible", "P1 reconciliation (n = 800)"), ("P2", "feasible", "P2 change-free wallet (n = 1000)"),
          ("P3", "feasible", "P3 perfect partition (n = 200)"), ("P5", "feasible", "P5 wholesaler, planted (n = 200)"),
          ("P5", "impossible", "P5 wholesaler, impossible")]
def correct(r, I):
    if "impossible" in r["kind"]: return r["answer"] == "NO"          # validity is checked by checker5
    return r["answer"] == "YES" and sum(I["W"][j] for j in r["payload"][0]) == I["T"] and len(set(r["payload"][0])) == len(r["payload"][0])
setup(); fig, axs = plt.subplots(len(panels), 1, figsize=(5.6, 6.4))
for ax, (p, kind, title) in zip(axs, panels):
    P = R["problems"][p]; recs = [r for r in P["records"] if ("impossible" in r["kind"]) == (kind == "impossible")]
    if p == "P1": recs = [r for r in recs if "impossible" not in r["kind"]]
    meths = []; [meths.append(r["method"]) for r in recs if r["method"] not in meths]
    tot = {m: sum(1 for r in recs if r["method"] == m) for m in meths}
    ok = {m: [r["time"] for r in recs if r["method"] == m and correct(r, P["instances"][r["inst"]])] for m in meths}
    y = list(range(len(meths)))[::-1]
    ax.barh(y, [len(ok[m]) for m in meths], color=[BLUE if m == "ARCS" else MUTED for m in meths], height=0.6)
    for yi, m in zip(y, meths):
        lab = f"{len(ok[m])}/{tot[m]}" + (f"   median {statistics.median(ok[m]):.3g} s" if ok[m] else "")
        ax.text(len(ok[m]) + 0.1, yi, lab, va="center", fontsize=7.5, color=INK2)
    ax.set_yticks(y); ax.set_yticklabels(meths); ax.set_xlim(0, max(tot.values()) + 3.2); ax.set_xticks(range(0, max(tot.values()) + 1)); ax.grid(axis="y", visible=False)
    ax.set_title(title, loc="left", fontsize=8.5); ax.tick_params(axis="x", labelsize=7)
axs[-1].set_xlabel("correct answers")
fig.suptitle(f"BENCH5 (criterion sha256 {R['sha256'][:8]}…, one run)", x=0.02, ha="left", fontsize=9.5)
fig.tight_layout(); save(fig, "fig_bench5")
