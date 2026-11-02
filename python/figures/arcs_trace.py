"""Records one run of ARCS (dynamic moduli, descent, filtered endgame) for the figures fig_take_skip.py and fig_join.py.
   Instance: 195 multiples of 1009 plus 5 other weights, n = 200, weights up to about 10^12, planted target.
   Phases recorded: candidate moduli, class counts mod 1009, the two branch scores at every step of the descent,
   the handover (peak density of the remaining block below LAMBDA_STAR), and every round of the endgame
   (prime P, residue r, filtered sums of the two halves, the crossing on the line a + b = t).
   usage: from arcs_trace import run; D = run()"""
import os, sys, math, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "algorithm"))
import numpy as np
from arcs_dyn import ArcsDyn
import endgame_fast as E

LAMBDA_STAR, CAP = 5e4, 60

def run(seed=4):
    random.seed(seed)
    W = [1009 * random.randint(1, 10**9) for _ in range(195)] + [random.randint(1, 1009 * 10**9) for _ in range(5)]
    random.shuffle(W)
    T = sum(w for w in W if random.random() < 0.5)
    Wd = sorted(W, reverse=True); n = len(Wd)
    F = ArcsDyn(Wd)
    out = dict(W=Wd, T=T, cand=F.cand)
    t = T; steps = []; hand = None
    for k, w in enumerate(Wd):
        sc, m, v = F.score(k, t)
        peak = m * math.log(2) - 0.5 * math.log(2 * math.pi * max(v, 1))   # log of the peak density of the block
        if m <= CAP and peak < math.log(LAMBDA_STAR):
            hand = dict(k=k, m=m, Z=math.exp(sc), t=t, peak=peak); break
        si = F.score(k + 1, t - w); so = F.score(k + 1, t)
        si = si[0] if si != -math.inf else None; so = so[0] if so != -math.inf else None
        take = (so is None) or (si is not None and si >= so)
        steps.append(dict(k=k, w=w, t=t, s_in=si, s_out=so, take=take, peak=peak))
        if take: t -= w
    out["steps"] = steps; out["hand"] = hand
    # endgame: halves A, B of the remaining block; a round draws a prime P and a residue r, lists the sums of A that are
    # = r (mod P) and the sums of B that are = t - r (mod P), and joins them on a + b = t
    B = Wd[hand["k"]:]; t = hand["t"]; m = len(B); h = m // 2; A, Bh = B[:h], B[h:]
    P0 = max(3, int(hand["Z"] / 2)); rg = random.Random(7); rounds = []
    for _ in range(8):
        while True:
            P = rg.randrange(P0, 2 * P0)
            if E.isprime(P): break
        r = rg.randrange(P)
        LA, MA = E.residue_list(A, P, r); LB, MB = E.residue_list(Bh, P, (t - r) % P)
        res = None
        if len(LA) and len(LB):
            o = np.argsort(LB); res = E.join(LA, MA, LB[o], MB[o], t)
        pair = None
        if res is not None:
            pa = int(sum(A[j] for j in range(h) if (res[0] >> j) & 1)); pair = (pa, int(t - pa))
        rounds.append(dict(P=P, r=r, sumsA=sorted(int(x) for x in LA), sumsB=sorted(int(x) for x in LB), pair=pair))
        if res is not None: break
    out["endgame"] = dict(t=t, A=A, B=Bh, rounds=rounds)
    return out
