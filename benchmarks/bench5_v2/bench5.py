"""Runner of CRITERIO_BENCH5_v2 (one run). usage: python3 bench5.py [--dev]
   --dev: debug pass with a different seed base and reduced limits; its output is NOT the benchmark."""
import sys, json, time, math, random, hashlib, statistics, heapq
from collections import Counter
import numpy as np
from sympy import primerange
DEV = "--dev" in sys.argv
CRIT = open("CRITERIO_BENCH5_v2.md", "rb").read()
SHA = hashlib.sha256(CRIT).hexdigest()
SEED_BASE = 12345 if DEV else int(SHA[:16], 16)
TL = 5.0 if DEV else 60.0                 # time limit for CPSAT / CKK
def seed(P, i): return SEED_BASE + 1000 * P + i

# ---------------- methods ----------------
from arcs_dyn import ArcsDyn
from endgame_fast import endgame_mod
RHO, CAP = 5e4, 60
def arcs_solve(W, T, mode="dynamic"):
    """returns ('YES', idx) | ('NO', q, c) | ('FAIL', info)"""
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
def cpsat_solve(W, T):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel(); x = [m.NewBoolVar("") for _ in W]
    m.Add(sum(int(w) * xi for w, xi in zip(W, x)) == int(T))
    s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = TL
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE): return ("YES", [i for i in range(len(W)) if s.Value(x[i])])
    if st == cp_model.INFEASIBLE: return ("NO", -1, -1)
    return ("FAIL", "time")
def bnb_core(W, T, tries=100000):
    order = sorted(range(len(W)), key=lambda i: -W[i]); v = [W[i] for i in order]
    n = len(v); rem = [0] * (n + 1)
    for i in range(n - 1, -1, -1): rem[i] = rem[i + 1] + v[i]
    sel = [False] * n; cur = 0; i = 0; cnt = 0
    while cnt < tries:
        cnt += 1
        back = False
        if cur + rem[i] < T or cur > T: back = True
        elif cur == T:
            return ("YES", [order[j] for j in range(i) if sel[j]])
        if back:
            # backtrack to the last included item, exclude it
            j = i - 1
            while j >= 0 and not sel[j]: j -= 1
            if j < 0: return ("NO", -2, -2)          # exhausted: no exact match
            sel[j] = False; cur -= v[j]; i = j + 1
            continue
        if i == n:
            j = i - 1
            while j >= 0 and not sel[j]: j -= 1
            if j < 0: return ("NO", -2, -2)
            sel[j] = False; cur -= v[j]; i = j + 1; continue
        sel[i] = True; cur += v[i]; i += 1
    return ("FAIL", "tries")
def kk(W):
    h = [(-w, 1 << i, 0) for i, w in enumerate(W)]; heapq.heapify(h)
    while len(h) > 1:
        a, Aa, Ba = heapq.heappop(h); b, Ab, Bb = heapq.heappop(h)
        heapq.heappush(h, (a - b, Aa | Bb, Ba | Ab))        # -(|a|-|b|): a,b negative
    d, A, B = h[0]; return -d, A
def ckk(W, target_diff):
    t0 = time.time(); S = sum(W); best = [None]
    items = sorted(((w, 1 << i, 0) for i, w in enumerate(W)), reverse=True)
    sys.setrecursionlimit(10000)
    class Done(Exception): pass
    def rec(lst):
        if time.time() - t0 > TL: raise Done()
        if len(lst) == 1:
            if lst[0][0] <= target_diff: best[0] = lst[0]; raise Done()
            return
        a = lst[0]; rest = lst[1:]; srest = sum(x[0] for x in rest)
        if a[0] >= srest:
            if a[0] - srest <= target_diff:
                A = a[1]; B = a[2]
                for x in rest: A |= x[2]; B |= x[1]
                best[0] = (a[0] - srest, A, B); raise Done()
            return
        b = rest[0]; rest2 = rest[1:]
        for new in ((a[0] - b[0], a[1] | b[2], a[2] | b[1]), (a[0] + b[0], a[1] | b[1], a[2] | b[2])):
            l2 = rest2[:];
            # insert keeping descending order
            lo, hi = 0, len(l2)
            while lo < hi:
                mid = (lo + hi) // 2
                if l2[mid][0] > new[0]: lo = mid + 1
                else: hi = mid
            l2.insert(lo, new); rec(l2)
    try: rec(items)
    except Done: pass
    if best[0] is None: return ("FAIL", "time")
    d, A, B = best[0]
    return ("YES", [i for i in range(len(W)) if (A >> i) & 1])
def run(f, *a):
    t = time.time(); r = f(*a); return r, time.time() - t

# ---------------- instances ----------------
def gen_P1():
    out = []
    for i in range(6):
        rnd = random.Random(seed(1, i)); W = [rnd.randint(10**3, 10**9) for _ in range(800)]
        k = rnd.randint(200, 600); S = rnd.sample(range(800), k); out.append(dict(W=W, T=sum(W[j] for j in S), kind="planted"))
    for i in range(2):
        rnd = random.Random(seed(1, 100 + i)); W = [50 * rnd.randint(20, 2 * 10**7) for _ in range(800)]
        T = (sum(W) // 2) // 50 * 50 + 37; out.append(dict(W=W, T=T, kind="impossible-C1"))
    return out
def gen_P2():
    out = []
    for R in (10**8, 10**10):
        for i in range(3):
            rnd = random.Random(seed(2, i + (10 if R == 10**10 else 0))); W = [rnd.randint(1, R) for _ in range(1000)]
            S = rnd.sample(range(1000), 500); out.append(dict(W=W, T=sum(W[j] for j in S), kind=f"planted R={R:.0e}"))
    return out
def gen_P3():
    out = []
    for i in range(6):
        rnd = random.Random(seed(3, i)); W = [rnd.randint(10**4, 10**10) for _ in range(200)]
        if sum(W) % 2: W[-1] += 1
        out.append(dict(W=W, T=sum(W) // 2, kind="partition"))
    return out
def gen_P5():
    out = []
    for i in range(12):
        rnd = random.Random(seed(5, i))
        W = [1009 * rnd.randint(1, 10**9) for _ in range(195)] + [rnd.randint(1, 1009 * 10**9) for _ in range(5)]
        rnd.shuffle(W)
        if i < 6:
            T = sum(w for w in W if rnd.random() < 0.5); kind = "planted"
        else:
            ex = [w for w in W if w % 1009]; reach = {0}
            for w in ex: reach |= {(r + w) % 1009 for r in reach}
            c = rnd.choice([r for r in range(1009) if r not in reach])
            T0 = sum(W) // 2; T = T0 - (T0 % 1009) + c; kind = "impossible"
        out.append(dict(W=W, T=T, kind=kind))
    return out

# ---------------- P4: counting ----------------
def edgeworth_log_count(W, T):
    n = len(W); S = sum(W)
    s2 = sum(w * w for w in W) / 4.0; s = math.sqrt(s2)
    k4 = -sum(float(w)**4 for w in W) / 8; k6 = sum(float(w)**6 for w in W) / 4; k8 = -17 * sum(float(w)**8 for w in W) / 16
    a4, a6, a8 = k4 / 24, k6 / 720, k8 / 40320
    c = {4: a4, 6: a6, 8: a4 * a4 / 2 + a8, 10: a4 * a6, 12: a4**3 / 6}
    z = (T - S / 2) / s
    He = [1.0, z]
    for k in range(2, 13): He.append(z * He[-1] - (k - 1) * He[-2])
    corr = 1.0 + sum(ck * He[k] / s**k for k, ck in c.items())
    return n * math.log(2) - math.log(s) - 0.5 * math.log(2 * math.pi) - z * z / 2 + math.log(corr)
def dp_log_counts(W, Ts):
    Tm = max(Ts); dp = np.zeros(Tm + 1); dp[0] = 1.0; E = 0
    for w in W:
        if w <= Tm: dp[w:] = dp[w:] + dp[:-w]
        mx = dp.max(); e = int(np.frexp(mx)[1])
        if e > 900: dp = np.ldexp(dp, -e); E += e
    return [math.log(dp[T]) + E * math.log(2) for T in Ts]
def P4():
    rows = []
    for N in (2000, 8000, 16000):
        W = [1] + list(primerange(2, N + 1)); S = sum(W); s = math.sqrt(sum(w * w for w in W) / 4)
        Ts = [int(S / 2 + k * s) for k in range(4)]
        t = time.time(); est = [edgeworth_log_count(W, T) for T in Ts]; te = time.time() - t
        t = time.time(); ref = dp_log_counts(W, Ts); tr = time.time() - t
        for k, T, e, r in zip(range(4), Ts, est, ref):
            rows.append(dict(N=N, n=len(W), k=k, T=T, log_ref=r, log_est=e, rel_err=abs(math.expm1(e - r)), t_est=te / 4, t_dp=tr))
        print(f"P4 N={N}: est {te*1e3:.2f} ms, DP {tr:.1f} s, rel err {[f'{x["rel_err"]:.1e}' for x in rows[-4:]]}", flush=True)
    return rows

# ---------------- main ----------------
if __name__ == "__main__":
    res = dict(sha256=SHA, seed_base=SEED_BASE, dev=DEV, TL=TL, problems={})
    def bench(name, insts, methods):
        recs = []
        for j, I in enumerate(insts):
            for mname, f in methods:
                r, dt = run(f, I["W"], I["T"])
                recs.append(dict(inst=j, kind=I["kind"], method=mname, answer=r[0], payload=r[1:] if r[0] != "YES" else [sorted(r[1])], time=dt))
                print(f"{name} #{j} {I['kind']:16s} {mname:6s} {r[0]:4s} {dt:8.3f}s {r[1:] if r[0]!='YES' else ''}", flush=True)
        res["problems"][name] = dict(instances=insts, records=recs)
    cnt = lambda: None
    P1i = gen_P1(); P2i = gen_P2(); P3i = gen_P3(); P5i = gen_P5()
    if DEV: P1i = P1i[:1] + P1i[-1:]; P2i = P2i[:1] + P2i[-1:]; P3i = P3i[:1]; P5i = P5i[:1] + P5i[-1:]
    bench("P1", P1i, [("ARCS", arcs_solve), ("CPSAT", cpsat_solve)])
    bench("P2", P2i, [("ARCS", arcs_solve), ("BNB", bnb_core), ("CPSAT", cpsat_solve)])
    bench("P3", P3i, [("ARCS", arcs_solve), ("KK", lambda W, T: (lambda d: ("YES", [i for i in range(len(W)) if (d[1] >> i) & 1]) if d[0] == 0 else ("FAIL", f"diff={d[0]}"))(kk(W))),
                      ("CKK", lambda W, T: ckk(W, 0)), ("CPSAT", cpsat_solve)])
    bench("P5", P5i, [("ARCS", arcs_solve), ("QFIX", lambda W, T: arcs_solve(W, T, "qfix")), ("NOARC", lambda W, T: arcs_solve(W, T, "noarc")), ("CPSAT", cpsat_solve)])
    # DP feasibility record (n*S bits)
    res["dp_bits"] = {k: [len(I["W"]) * sum(I["W"]) for I in v["instances"]] for k, v in res["problems"].items()}
    # K3 control
    rnd = random.Random(SEED_BASE + 9); Wk = [2 * rnd.randint(1, 10**9) for _ in range(200)]; Tk = sum(Wk) // 2 | 1
    res["K3"] = dict(W=Wk, T=Tk, answer=list(arcs_solve(Wk, Tk))[:3])
    print("K3", res["K3"]["answer"], flush=True)
    res["P4"] = P4() if not DEV else []
    json.dump(res, open("results_dev.json" if DEV else "results_v2.json", "w"))
    print("done", flush=True)
