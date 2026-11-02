"""ARCS, the solver of the paper (§5.2-5.7): arc-guided descent with dynamic moduli, then the filtered endgame.
   The pseudocode is pseudocode/ARCS_pseudocode.md (procedure ARCS). This is the function run by the benchmark
   BENCH5 v2 (benchmarks/bench5_v2/bench5.py, arcs_solve), extracted here unchanged so that the algorithm can be used
   without the benchmark. arcs_dyn.py and endgame_fast.py here differ from the bench5_v2 copies only in comments.
   arcs_solve(W, T, mode) returns ('YES', indices) | ('NO', q, c) | ('FAIL', reason).
   mode: "dynamic" (the paper's rule, §5.7), "qfix" (fixed moduli q = 2..24), anything else: no moduli.
   This is ARCS with the fixed constants of the reference run BENCH5 v2 (ARCS-FIXED in the pseudocode); the default ARCS,
   with every parameter derived from the instance, is arcs_rho.py, and arcs.py chooses between them.
   Limits, reported as FAIL: n > 1020 ("n>1020", floating class counts) and endgame blocks with m·max(W) >= 2^63 ("int64")."""
import math, random
from arcs_dyn import ArcsDyn
from endgame_fast import endgame_mod
RHO, CAP = 5e4, 60
def arcs_solve(W, T, mode="dynamic"):
    """returns ('YES', idx) | ('NO', q, c) | ('FAIL', info)"""
    if len(W) > 1020: return ("FAIL", "n>1020")
    try: return _arcs_solve(W, T, mode)
    except OverflowError: return ("FAIL", "int64")
def _arcs_solve(W, T, mode="dynamic"):
    order = sorted(range(len(W)), key=lambda i: -W[i]); Wd = [W[i] for i in order]
    if mode == "dynamic": F = ArcsDyn(Wd, Q0=24, DCAP=2000, PAIRS=64, C_EPS=1.0, seed=0)
    elif mode == "qfix": F = ArcsDyn(Wd, fixed=range(2, 25), C_EPS=0)
    else: F = ArcsDyn(Wd, fixed=[])
    if T < 0 or T > sum(W): return ("NO", 0, 0)
    for q in F.sel[0]:
        if F.N[q][0, T % q] == 0.0: return ("NO", int(q), int(T % q))
    rng = random.Random(7); out = []; t = T
    for k, w in enumerate(Wd):
        r = F.score(k, t)
        if r == -math.inf: return ("FAIL", "scored-out")
        sc, m, v = r
        if m <= CAP and m * math.log(2) - 0.5 * math.log(2 * math.pi * max(v, 1)) < math.log(RHO):
            rest, _ = endgame_mod(Wd[k:], t, math.exp(sc), rng)
            if rest is None: return ("FAIL", "endgame")
            chosen = out + [order[k + j] for j in _match(Wd[k:], rest)]
            return ("YES", chosen)
        si = F.score(k + 1, t - w); so = F.score(k + 1, t)
        si = si[0] if si != -math.inf else si; so = so[0] if so != -math.inf else so
        if si == -math.inf and so == -math.inf: return ("FAIL", "both-out")
        if si >= so: out.append(order[k]); t -= w
    return ("YES", out) if t == 0 else ("FAIL", "end")
def _match(block, vals):                 # positions in block of the multiset vals
    pos = {}
    for j, x in enumerate(block): pos.setdefault(x, []).append(j)
    res = []
    for x in vals: res.append(pos[x].pop())
    return res
