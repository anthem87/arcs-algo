"""ARCS driven by the instance: density ρ, class counts, predicted cost (mode "rho").

The steps are those of ARCS (§5.2–5.7, pseudocode procedure ARCS):
  1. sort the weights decreasingly;
  2. PREPROCESS: suffix sums S_k and variances V_k; candidate moduli; class counts N_c^{(k)}(q) in floating point;
     selection Q(k) = {q : δ_q(k) ≥ ε_k}, ε_k = min(1, 1/m) (Lemma 5.3);
  3. range NO: T < 0 or T > S gives the certificate (0, 0);
  4. modular NO: an empty class N_{T mod q}^{(1)}(q) = 0 for q ∈ Q(1) gives the certificate (q, T mod q);
  5. descent by the score of §5.2 (Gaussian log-count plus the class correction); an empty class scores −∞;
  6. handover when the peak density 2^m/(√(2π)σ_m) of the remaining block falls below 𝒵*;
  7. endgame: filtered rounds (quarters, residue lists mod a uniform prime P ∈ [P₀, 2P₀), join), then the exhaustive
     meet-in-the-middle, or the full residue scan when memory is short;
  8. FAIL with a declared reason when no answer is reached; every YES is verified, every NO is an exact count.

What changes is where the numbers come from. The user gives two things only:
    delta    accepted probability that a run on a YES instance ends in FAIL;
    max_ops  how many elementary operations the user is willing to wait for (and `memory`, the bytes available).
Everything else is computed from the instance before the descent starts:

 R1 Density.  ρ = n/log₂ D with D = max W − min W + 1 (the density of CPT, Def. 2.1).
 R2 Handover density.  𝒵* = max(400, (2.3·n/δ)^{1/3}): the measured tail Pr(Z = 0) ≈ 2.3·𝒵⁻³ (§6.6) with a union
    bound over the n decisions, and P₀ = ⌊𝒵/2⌋ ≥ 100 at the handover, as Theorem R″ requires.
 R3 Predicted block.  The peak density of each suffix is known before the descent (it depends on V_k only), so the
    suffix k* where it first falls below 𝒵* is computed in O(n): m* = n − k*. For random b-bit weights
    m* ≈ b + log₂(𝒵*·√(2π m*/12)) = n/ρ + O(log n): the block, hence the cost, is set by ρ.
 R4 Predicted cost.  cost(m) is the cheapest endgame that fits the memory, from the models
        filter  R·(8m·2^{m/4} + 8m·2^{m/2}/P₀)     (Table 8; R = ⌈ln(1/δ)/2⌉ rounds, P₀ ≥ 100 only)
        mitm    8m·2^{m/2}, memory 16·2^{m/2}       (exact, exhaustive)
        scan    16m·2^{m/2}, memory 32·2^{m/4}      (exact, exhaustive)
        exact   50·2^{m/2}  (Python integers, blocks beyond int64)
    The predicted cost of the run is cost(m*). If it exceeds max_ops the run stops at once with
    FAIL("predicted 2^x > max_ops"), after the NO certificates of steps 3–4, which cost O(n·ΣQ).
 R5 Moduli.  Small moduli q = 2, …, q₀ with Σq ≤ n, so that their class counts cost O(n²), the order of the pair
    gcds; then the divisors of the gcds of s pairs, s = ⌈ln δ / ln(3/4)⌉, so that a divisor of at least half of the
    weights is missed with probability ≤ δ; a divisor d is kept if its class counts, n·d operations and 8(n+1)d bytes,
    cost no more than the predicted endgame and fit the memory: the arcs are never paid more than what they shorten.
 R6 Rounds.  R = ⌈ln(1/δ)/2⌉: each of the Poisson(𝒵) solutions survives the filter with probability 1/P, P ≈ 𝒵/2.
 R7 Randomness from the operating system; every prime and residue drawn is in the certificate (replayable), and P is
    independent of the weights (Lemma K). No seed.
 R8 Limits declared: n ≤ 1020 (floating class counts), positive weights; beyond int64 the exact endgame is used.

arcs_solve_rho(W, T, delta, max_ops, memory) returns
    ("YES", idx, cert) | ("NO", q, c, cert) | ("FAIL", reason, cert)
with q = 0 (range), q ≥ 2 (empty class mod q) or q = −3 (exhaustive endgame on the whole instance)."""
import math, random
from math import gcd
import numpy as np
from arcs_dyn import _divisors
from arcs_adaptive import Arcs, _mitm_exact, _scan, _idx
from endgame_fast import filtered_round_idx, mitm_merge, uniform_prime

C_TAIL = 2.3
P0_MIN = 100
I64 = 2 ** 63

def endgame_options(m, P0, R, fits64, memory):
    """(name, cost) of the endgames that fit, cheapest first (R4)"""
    o = []
    if fits64:
        if P0 >= P0_MIN: o.append(("filter", R * (8 * m * 2 ** (m / 4) + 8 * m * 2 ** (m / 2) / P0)))
        if 16 * 2 ** (m / 2) <= memory: o.append(("mitm", 8 * m * 2 ** (m / 2)))
        if 32 * 2 ** (m / 4) <= memory: o.append(("scan", 16 * m * 2 ** (m / 2)))
    else:
        if 64 * 2 ** (m / 2) <= memory: o.append(("exact", 50 * 2 ** (m / 2)))
    return sorted(o, key=lambda x: x[1])

def exhaustive_cost(opts):
    ex = [c for nm, c in opts if nm != "filter"]
    return min(ex) if ex else math.inf

def arcs_solve_rho(W, T, delta=1e-3, max_ops=2 ** 34, memory=2 ** 30):
    n = len(W); rng = random.SystemRandom()
    cert = {"delta": delta, "max_ops": max_ops, "memory": memory, "draws": []}
    if n > 1020: return ("FAIL", "n>1020", cert)
    if n == 0: return ("YES", [], cert) if T == 0 else ("NO", 0, 0, cert)
    if min(W) <= 0: return ("FAIL", "weights must be positive", cert)
    # 1. sort
    order = sorted(range(n), key=lambda i: -W[i]); Wd = [W[i] for i in order]
    # R1, R2, R6
    rho = n / math.log2(max(W) - min(W) + 1) if max(W) > min(W) else float("inf")
    Zstar = max(400.0, (C_TAIL * n / delta) ** (1 / 3)); R = max(1, math.ceil(math.log(1 / delta) / 2))
    # R3: predicted block from the suffix variances (known before the descent)
    V = [0.0] * (n + 1)
    for k in range(n - 1, -1, -1): V[k] = V[k + 1] + float(Wd[k]) ** 2 / 4
    kstar = n
    for k in range(n):
        m = n - k
        if m * math.log(2) - 0.5 * math.log(2 * math.pi * max(V[k], 1)) < math.log(Zstar): kstar = k; break
    mstar = n - kstar
    dens_star = math.exp(mstar * math.log(2) - 0.5 * math.log(2 * math.pi * max(V[kstar], 1))) if mstar else 1.0
    fits_star = mstar * (Wd[kstar] if mstar else 0) < I64
    opts_star = endgame_options(mstar, max(3, int(dens_star / 2)), R, fits_star, memory)
    pred = opts_star[0][1] if opts_star else math.inf
    pred_ops = min(8 * mstar * 2 ** (mstar / 2), 50 * 2 ** (mstar / 2)) if mstar else 0   # time model without the memory bound
    pred_mem = 16 * 2 ** (mstar / 2)
    cert.update(rho=rho, Zstar=Zstar, R=R, m_pred=mstar, k_pred=kstar, cost_pred=pred,
                endgame_pred=opts_star[0][0] if opts_star else None)
    # R5: moduli
    q0 = 1; tot = 0
    while tot + (q0 + 1) <= n: q0 += 1; tot += q0
    cand = set(range(2, q0 + 1)) if q0 >= 2 else set()
    s = min(n * (n - 1) // 2, math.ceil(math.log(delta) / math.log(0.75))) if n >= 2 else 0
    cap_cost = min(pred if pred < math.inf else max_ops, max_ops)
    dcap = max(2, int(min(cap_cost / n, memory / (8 * (n + 1)))))
    for _ in range(s):
        a, b = rng.sample(Wd, 2); g = gcd(a, b)
        if g > 1: cand |= {d for d in _divisors(g, dcap) if d > q0}
    cand = sorted(cand); cert.update(q0=q0, pairs=s, dcap=dcap, moduli=len(cand), moduli_large=[q for q in cand if q > q0][:20])
    # 2. PREPROCESS
    F = Arcs(Wd, cand)
    # 3. range NO, 4. modular NO
    if T < 0 or T > F.S[0]: return ("NO", 0, 0, cert)
    for q in F.sel[0]:
        if F.N[q][0, T % q] == 0.0: return ("NO", int(q), int(T % q), cert)
    cert["structure"] = sorted({q for sel in F.sel for q in sel})[:20]
    # R4: refuse at once when the predicted cost exceeds what the user will wait for
    if pred > max_ops:
        if pred == math.inf: return ("FAIL", f"predicted memory 2^{math.log2(pred_mem):.1f} B > memory (time 2^{math.log2(pred_ops):.1f} ops)", cert)
        return ("FAIL", f"predicted 2^{math.log2(pred):.1f} ops > max_ops", cert)
    # 5–7. descent, handover, endgame
    out = []; t = T; forced = False
    def fail(reason): return ("FAIL", "budget" if forced else reason, cert)
    for k, w in enumerate(Wd):
        r = F.score(k, t)
        if r == -math.inf: return fail("scored-out")
        sc, m, v = r
        if m * math.log(2) - 0.5 * math.log(2 * math.pi * max(v, 1)) < math.log(Zstar):
            Z = math.exp(sc); P0 = max(3, int(Z / 2)); blk = Wd[k:]
            opts = [o for o in endgame_options(m, P0, R, m * blk[0] < I64, memory) if o[1] <= max_ops]
            if not opts:
                forced = True; cert.setdefault("forced_at", (k, m));
            else:
                choice = opts[0][0]; cert["handover"] = {"k": k, "m": m, "Z": Z, "P0": P0, "endgame": choice}
                rest = None; exhaustive = False
                if choice == "filter":
                    for rd in range(R):
                        P = int(uniform_prime(P0, 2 * P0, rng)); rr = rng.randrange(P); cert["draws"].append((P, rr))
                        idx = filtered_round_idx(blk, t, P, rr)
                        if idx is not None: rest = idx; cert["rounds"] = rd + 1; break
                    if rest is None:
                        ex = [o for o in opts if o[0] != "filter"]
                        if ex:
                            fb = ex[0][0]; cert["fallback"] = fb; exhaustive = True
                            rest = _idx(mitm_merge(blk, t), blk) if fb == "mitm" else _scan(blk, t, rng, cert)[0]
                elif choice == "mitm": rest = _idx(mitm_merge(blk, t), blk); exhaustive = True
                elif choice == "scan": rest = _scan(blk, t, rng, cert)[0]; exhaustive = True
                else: rest = _mitm_exact(blk, t); exhaustive = True
                if rest is None:
                    if exhaustive and k == 0:
                        cert["no_kind"] = "exhaustive"; return ("NO", -3, -3, cert)
                    return fail("endgame")
                return ("YES", out + [order[k + j] for j in rest], cert)
        si = F.score(k + 1, t - w); so = F.score(k + 1, t)
        si = si[0] if si != -math.inf else si; so = so[0] if so != -math.inf else so
        if si == -math.inf and so == -math.inf: return fail("both-out")
        if si >= so: out.append(order[k]); t -= w
    return ("YES", out, cert) if t == 0 else fail("end")
