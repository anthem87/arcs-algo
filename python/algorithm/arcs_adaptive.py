"""ARCS with derived parameters (mode "adaptive").

Every constant of arcs_solver.arcs_solve (Q0 = 24, DCAP = 2000, PAIRS = 64, λ* = 5·10⁴, CAP = 60, MMAX = 44,
6 rounds, the branch λ < 8 or m < 16, the seed 7) is derived here at run time from the instance and from three
declared resources:
    delta   accepted probability that a run on a YES instance ends in FAIL (default 1e-3);
    budget  elementary operations allowed for the run (default 2^30);
    memory  bytes allowed for the tables (default 2^30).
No parameter affects correctness: every YES is verified, every NO is an exact class count (q, c). The parameters decide
only how often an answer is reached instead of FAIL, and in how long. The cost models below are models, stated so that
every number has a provenance; they are not theorems.

Derivations.
 D1 Moduli. The preprocessing gets min(budget/4, expected cost of the endgame) and all of memory: the arcs are never
    paid more than the endgame they shorten (the expected block m* solves 2^m = λ*·√(2π)·σ with σ ≈ maxw·√(n/12)). The class counts over a set Q of moduli cost about
    n·ΣQ operations and (n+1)·ΣQ·8 bytes. Candidates: q = 2, 3, 4, ... in increasing order, then the divisors of the
    gcds of pairs of weights (all pairs when n(n-1)/2 gcds fit in budget/8 at 64 operations each, otherwise that many
    random pairs), accepted while both bounds hold. The divisor cap is budget/(4n), the cost of one modulus.
 D2 Class threshold eps_k = min(1, 1/m_k): Lemma 5.3 is proved for every eps in (0, 1].
 D3 Handover density λ*. The measured law of the empty branch is Pr(Z = 0) ≈ C·λ^{-3} with C = 2.3 (§6.6: 0.0075,
    0.0011, 1.2·10⁻⁴ at λ = 6.7, 12.7, 24.4). A union bound over the n decisions gives λ* = (C·n/delta)^{1/3}.
    At the handover λ lies in [λ*/2, λ*), and Theorem R″ needs P₀ = ⌊λ/2⌋ ≥ 100, so λ* ≥ 400.
 D4 Endgame sizes from budget/2 and memory. With P₀ = λ*/4 (the smallest P₀ at the handover):
      MMAX = largest m with 2^{m/2}·16 bytes ≤ memory and 8m·2^{m/2} ≤ budget/2   (full meet-in-the-middle, two lists);
      SCAN = largest m with (P₀+1)·(8·2^{m/4}) + 8·2^{m/2} ≤ budget/2     (full residue scan: exact YES or NO, memory 2^{m/4});
      CAP  = largest m with R·(8m·2^{m/4} + 8m·2^{m/2}/P₀) ≤ budget/2     (R filtered rounds).
 D5 Rounds. Model: the block holds Poisson(λ) solutions and each survives the residue filter with probability 1/P,
    so a round is empty with probability exp(-λ/P); R = ⌈ln(1/delta)·P/λ⌉ = ⌈ln(1/delta)/2⌉ for P = λ/2.
 D6 Endgame choice: filtered rounds iff P₀ ≥ 100 (Theorem R″) and m ≤ CAP; else the full meet-in-the-middle if
    m ≤ MMAX; else the full residue scan if m ≤ SCAN; else FAIL("budget"). The descent hands over at the first suffix
    where the peak density 2^m/(√(2π)σ) is below λ* and some endgame fits; if the density is below λ* but no endgame
    fits, the descent continues and the fact is recorded ("forced").
 D7 Randomness from the operating system (random.SystemRandom). Every prime and residue drawn is returned in the
    certificate, so a run is replayable, and P is independent of the weights as Lemma K requires. No seed exists.
 D8 Integers. numpy int64 when m·max(block) < 2^63; otherwise exact Python integers for the meet-in-the-middle
    (about 50 operations per element: m ≤ 2·log₂(budget/100)); otherwise FAIL("int64"), declared.
 D9 n > 1020: the floating class counts need 2^{-m} to be a normal double; FAIL("n>1020"), declared.

arcs_solve_adaptive(W, T, delta, budget, memory) returns
    ("YES", idx, cert) | ("NO", q, c, cert) | ("FAIL", reason, cert),
where cert holds the derived parameters, the path of the descent and the random draws."""
import math, random, os
from math import gcd
import numpy as np
from arcs_dyn import _divisors
from endgame_fast import filtered_round_idx, mitm_merge, uniform_prime, all_sums, I64

def class_counts(W, qs):
    """as arcs_dyn.class_counts, with w reduced mod q in Python integers first (weights beyond int64 allowed)"""
    n = len(W); qs = list(qs); off = np.concatenate([[0], np.cumsum(qs)]).astype(np.int64); L = int(off[-1])
    qof = np.concatenate([[q] * q for q in qs]).astype(np.int64)
    base = np.concatenate([np.full(q, off[i], np.int64) for i, q in enumerate(qs)]); cls = np.arange(L) - base; starts = off[:-1]
    qarr = np.array(qs, dtype=np.int64)
    N = np.zeros((n + 1, L)); E = np.zeros((n + 1, len(qs)), dtype=np.int64); N[n, starts] = 1.0
    for k in range(n - 1, -1, -1):
        wk = np.repeat(np.array([W[k] % q for q in qs], dtype=np.int64), qarr)
        row = N[k + 1] + N[k + 1][base + (cls - wk) % qof]
        e = np.frexp(np.maximum.reduceat(row, starts))[1].astype(np.int64)
        N[k] = np.ldexp(row, -np.repeat(e, qs)); E[k] = E[k + 1] + e
    return N, E, off

class Arcs:
    """arc scores on the suffixes, over a fixed list of moduli, with the class threshold eps_k = min(1, 1/m_k) (D2)"""
    def __init__(self, W, cand):
        n = len(W); self.W = W; self.n = n; self.LN2 = math.log(2)
        self.S = [0] * (n + 1); self.V = [0.0] * (n + 1)
        for k in range(n - 1, -1, -1): self.S[k] = self.S[k + 1] + W[k]; self.V[k] = self.V[k + 1] + float(W[k]) ** 2 / 4
        self.cand = cand
        if not cand: self.sel = [[] for _ in range(n + 1)]; self.N = {}; self.E = {}; return
        N, E, off = class_counts(W, cand)
        self.N = {q: N[:, off[i]:off[i + 1]] for i, q in enumerate(cand)}; self.E = {q: E[:, i] for i, q in enumerate(cand)}
        qarr = np.array(cand, dtype=np.int64); starts = off[:-1]; qcol = np.repeat(qarr, qarr).astype(float)
        self.sel = []
        for k in range(n + 1):                      # deviation of every modulus at once: max over its classes of |q N_c 2^{E-m} - 1|
            m = n - k; eps = 1.0 if m == 0 else min(1.0, 1.0 / m)
            sc = qcol * np.repeat(np.ldexp(1.0, (E[k] - m).astype(np.int64)), qarr)
            dev = np.maximum.reduceat(np.abs(N[k] * sc - 1.0), starts)
            self.sel.append([int(q) for q in qarr[dev >= eps]])
    def score(self, k, T):
        S = self.S[k]; m = self.n - k
        if T < 0 or T > S: return -math.inf
        if m == 0: return (0.0, 0, 0.0) if T == 0 else -math.inf
        best = 0.0
        for q in self.sel[k]:
            x = self.N[q][k, T % q]
            if x == 0.0: return -math.inf
            l = math.log(q) + math.log(x) + (int(self.E[q][k]) - m) * self.LN2
            if l > best: best = l
        v = self.V[k]
        return m * self.LN2 - 0.5 * math.log(2 * math.pi * v) - float(T - S / 2) ** 2 / (2 * v) + best, m, v

C_TAIL = 2.3          # measured constant of Pr(Z = 0) ≈ C λ^-3 (§6.6)
P0_MIN = 100          # hypothesis of Theorem R″

def derive(n, maxw, delta, budget, memory):
    """the parameters of the run, from (n, max weight, delta, budget, memory); all formulas are D1–D6 above"""
    p = {}
    p["Zstar"] = max(400.0, (C_TAIL * n / delta) ** (1 / 3))
    p["R"] = max(1, math.ceil(math.log(1 / delta) / 2))
    P0 = p["Zstar"] / 4
    B_end = budget / 2
    m = 0
    while 2 ** ((m + 1) / 2) * 16 <= memory and 8 * (m + 1) * 2 ** ((m + 1) / 2) <= B_end: m += 1
    p["MMAX"] = m
    m = 0
    while (P0 + 1) * 8 * 2 ** ((m + 1) / 4) + 8 * 2 ** ((m + 1) / 2) <= B_end: m += 1
    p["SCAN"] = m
    m = 0
    while p["R"] * (8 * (m + 1) * 2 ** ((m + 1) / 4) + 8 * (m + 1) * 2 ** ((m + 1) / 2) / P0) <= B_end: m += 1
    p["CAP"] = m
    p["MMAX_exact"] = max(0, int(2 * math.log2(B_end / 50)))
    # D1: moduli. The arcs get at most budget/4, and no more than the expected cost of the endgame itself:
    # at the handover 2^m ≈ λ*·√(2π)·σ, with σ ≈ maxw·√(n/12); the rounds then cost R·cost_round(m*).
    sigma = max(1.0, maxw * math.sqrt(n / 12))
    mstar = max(1, int(math.log2(p["Zstar"] * math.sqrt(2 * math.pi) * sigma)))
    cost_end = p["R"] * (8 * mstar * 2 ** (mstar / 4) + 8 * mstar * 2 ** (mstar / 2) / P0)
    B_pre = min(budget / 4, cost_end); p["mstar"] = mstar; p["B_pre"] = int(B_pre)
    p["DCAP"] = max(2, int(B_pre / max(n, 1)))
    p["PAIRS"] = min(n * (n - 1) // 2, int(budget / 8 / 64))
    p["mem_cols"] = int(memory / (8 * (n + 1)))      # ΣQ allowed by memory
    p["ops_cols"] = int(B_pre / max(n, 1))             # ΣQ allowed by budget/4
    return p

def choose_moduli(W, p, rng):
    """D1: small q first, then divisors of pair gcds, while n·ΣQ ≤ budget/4 and (n+1)·ΣQ·8 ≤ memory"""
    n = len(W); limit = min(p["mem_cols"], p["ops_cols"])
    cand = []; total = 0; q = 2
    while total + q <= limit // 2:                 # half of the room for the small moduli
        cand.append(q); total += q; q += 1
    p["Q0"] = cand[-1] if cand else 1
    divs = set()
    if n >= 2:
        pairs = p["PAIRS"]
        if pairs >= n * (n - 1) // 2:
            for i in range(n):
                for j in range(i + 1, n):
                    g = gcd(W[i], W[j])
                    if g > 1: divs |= _divisors(g, p["DCAP"])
        else:
            for _ in range(pairs):
                a, b = rng.sample(W, 2); g = gcd(a, b)
                if g > 1: divs |= _divisors(g, p["DCAP"])
    for d in sorted(divs):
        if d in cand or d <= p["Q0"]: continue
        if total + d > limit: break
        cand.append(d); total += d
    return sorted(cand)

def _mitm_exact(W, T):
    """full meet-in-the-middle in exact Python integers (D8)"""
    h = len(W) // 2; A, B = W[:h], W[h:]
    sb = {}
    s = [(0, 0)]
    for j, w in enumerate(B):
        s = s + [(x + w, mk | (1 << j)) for x, mk in s]
    for x, mk in s: sb.setdefault(x, mk)
    s = [(0, 0)]
    for j, w in enumerate(A):
        s = s + [(x + w, mk | (1 << j)) for x, mk in s]
    for x, mk in s:
        y = sb.get(T - x)
        if y is not None:
            return [j for j in range(h) if (mk >> j) & 1] + [h + j for j in range(len(B)) if (y >> j) & 1]
    return None

def _scan(W, T, rng, cert):
    """full residue scan (Schroeppel–Shamir in the modular form): exact. Returns (idx or None, certified)"""
    m = len(W); q = [W[k * m // 4:(k + 1) * m // 4] for k in range(4)]
    S = [all_sums(x)[0] for x in q]
    P = int(uniform_prime(max(3, len(S[0])), 2 * max(3, len(S[0])), rng)); cert["draws"].append(("scanP", P))
    def pairs(X, Y, want):
        yr = Y % P; yo = np.argsort(yr, kind="stable"); yr = yr[yo]
        t = (want - X % P) % P; lo = np.searchsorted(yr, t, "left"); hi = np.searchsorted(yr, t, "right"); c = hi - lo
        tot = int(c.sum())
        if tot == 0: return None
        i = np.repeat(np.arange(len(X)), c); off = np.arange(tot) - np.repeat(np.cumsum(c) - c, c)
        j = yo[np.repeat(lo, c) + off]; return i, j, X[i] + Y[j]
    for r in range(P):
        p1 = pairs(S[0], S[1], r)
        if p1 is None: continue
        p2 = pairs(S[2], S[3], (T - r) % P)
        if p2 is None: continue
        _, i1, i2 = np.intersect1d(p1[2], T - p2[2], return_indices=True)
        if len(i1):
            masks = (int(p1[0][i1[0]]), int(p1[1][i1[0]]), int(p2[0][i2[0]]), int(p2[1][i2[0]]))
            idx = []; base = 0
            for mk, blk in zip(masks, q):
                idx += [base + t for t in range(len(blk)) if (mk >> t) & 1]; base += len(blk)
            return idx, True
    return None, True

def arcs_solve_adaptive(W, T, delta=1e-3, budget=2 ** 30, memory=2 ** 30):
    n = len(W); rng = random.SystemRandom()
    cert = {"delta": delta, "budget": budget, "memory": memory, "draws": [], "path": []}
    if n > 1020: return ("FAIL", "n>1020", cert)
    if n and min(W) <= 0: return ("FAIL", "weights must be positive", cert)
    p = derive(n, max(W) if W else 1, delta, budget, memory); cert["params"] = p
    order = sorted(range(n), key=lambda i: -W[i]); Wd = [W[i] for i in order]
    cand = choose_moduli(Wd, p, rng); cert["moduli"] = cand
    F = Arcs(Wd, cand)
    if T < 0 or T > sum(W): return ("NO", 0, 0, cert)
    for q in F.sel[0]:
        if F.N[q][0, T % q] == 0.0: return ("NO", int(q), int(T % q), cert)
    out = []; t = T; forced = False
    def fail(reason): return ("FAIL", "budget" if forced else reason, cert)
    for k, w in enumerate(Wd):
        r = F.score(k, t)
        if r == -math.inf: return fail("scored-out")
        sc, m, v = r
        dens = m * math.log(2) - 0.5 * math.log(2 * math.pi * max(v, 1))
        if dens < math.log(p["Zstar"]):
            Z = math.exp(sc); P0 = max(3, int(Z / 2)); blk = Wd[k:]
            fits64 = m * max(blk) < 2 ** 63
            choice = None
            if fits64 and P0 >= P0_MIN and m <= p["CAP"]: choice = "filter"
            elif fits64 and m <= p["MMAX"]: choice = "mitm"
            elif fits64 and m <= p["SCAN"]: choice = "scan"
            elif not fits64 and m <= p["MMAX_exact"]: choice = "mitm-exact"
            if choice is None:
                if not forced: cert["path"].append(("forced", k, m))
                forced = True
            else:
                cert["handover"] = {"k": k, "m": m, "Z": Z, "P0": P0, "endgame": choice}
                rest = None; exhaustive = False
                if choice == "filter":
                    for rd in range(p["R"]):
                        P = int(uniform_prime(P0, 2 * P0, rng)); rr = rng.randrange(P); cert["draws"].append((P, rr))
                        idx = filtered_round_idx(blk, t, P, rr)
                        if idx is not None: rest = idx; cert["rounds"] = rd + 1; break
                    if rest is None:
                        if m <= p["MMAX"]: rest = _idx(mitm_merge(blk, t), blk); cert["fallback"] = "mitm"; exhaustive = True
                        elif m <= p["SCAN"]: rest, _ = _scan(blk, t, rng, cert); cert["fallback"] = "scan"; exhaustive = True
                elif choice == "mitm": rest = _idx(mitm_merge(blk, t), blk); exhaustive = True
                elif choice == "scan": rest, _ = _scan(blk, t, rng, cert); exhaustive = True
                else: rest = _mitm_exact(blk, t); exhaustive = True
                if rest is None:
                    if exhaustive and k == 0:
                        cert["no_kind"] = "exhaustive"       # the block is the whole instance: no subset sums to T
                        return ("NO", -3, -3, cert)
                    return fail("endgame")                    # the path above the block was a guess: no claim
                return ("YES", out + [order[k + j] for j in rest], cert)
        si = F.score(k + 1, t - w); so = F.score(k + 1, t)
        si = si[0] if si != -math.inf else si; so = so[0] if so != -math.inf else so
        if si == -math.inf and so == -math.inf: return fail("both-out")
        if si >= so: out.append(order[k]); t -= w
    return ("YES", out, cert) if t == 0 else fail("end")

def _idx(vals, block):
    """positions in block of the multiset vals (None stays None)"""
    if vals is None: return None
    pos = {}
    for j, x in enumerate(block): pos.setdefault(x, []).append(j)
    return [pos[x].pop() for x in vals]
