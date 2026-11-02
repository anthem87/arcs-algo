"""Runner of CRITERION_BENCH7_v1 (one run). usage: python3 bench7.py [--dev]   (run from this folder)"""
import sys, json, time, math, random, hashlib
DEV = "--dev" in sys.argv
CRIT = open("CRITERION_BENCH7_v1.md", "rb").read()
SHA = hashlib.sha256(CRIT).hexdigest()
SEED_BASE = 12345 if DEV else int(SHA[:16], 16)
def seed(P, i): return SEED_BASE + 1000 * P + i
from arcs_rho import arcs_solve_rho
DELTA, MAXOPS, MEMORY = 1e-3, 2 ** 34, 2 ** 30
def rho(W, T, max_ops=MAXOPS):
    r = arcs_solve_rho(W, T, delta=DELTA, max_ops=max_ops, memory=MEMORY)
    cert = dict(r[-1]); cert["draws"] = [list(d) if isinstance(d, tuple) else d for d in cert["draws"]]
    for k in ("cost_pred",):
        if cert.get(k) == math.inf: cert[k] = "inf"
    return tuple(r[:-1]) + (cert,)
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
def gen_P6():
    out = []
    for i in range(12):
        rnd = random.Random(seed(6, i)); W = [rnd.randint(1, 2 ** 50) for _ in range(50)]
        if i < 6: S = rnd.sample(range(50), 25); out.append(dict(W=W, T=sum(W[j] for j in S), kind="planted"))
        else: out.append(dict(W=W, T=rnd.randint(0, sum(W)), kind="random-target"))
    return out
def gen_P7():
    out = []
    for i in range(6):
        rnd = random.Random(seed(7, i)); W = [rnd.randint(1, 2 ** 70) for _ in range(40)]
        S = rnd.sample(range(40), 20); out.append(dict(W=W, T=sum(W[j] for j in S), kind="planted"))
    return out

def gen_P8():
    out = []
    for i in range(12):
        rnd = random.Random(seed(8, i)); W = [rnd.randint(1, 2 ** 60) for _ in range(40)]
        if i < 6: S = rnd.sample(range(40), 20); out.append(dict(W=W, T=sum(W[j] for j in S), kind="planted"))
        else: out.append(dict(W=W, T=rnd.randint(0, sum(W)), kind="random-target"))
    return out
def gen_P9():
    out = []
    for i in range(3):
        rnd = random.Random(seed(9, i)); W = [rnd.randint(1, 2 ** 110) for _ in range(100)]
        S = rnd.sample(range(100), 50); out.append(dict(W=W, T=sum(W[j] for j in S), kind="planted-sparse-large"))
    return out

if __name__ == "__main__":
    res = dict(sha256=SHA, seed_base=SEED_BASE, dev=DEV, params=dict(delta=DELTA, max_ops=MAXOPS, memory=MEMORY), problems={})
    def bench(name, insts):
        recs = []
        for j, I in enumerate(insts):
            r, dt = run(rho, I["W"], I["T"]); c = r[-1]
            payload = [sorted(r[1])] if r[0] == "YES" else list(r[1:-1])
            recs.append(dict(inst=j, kind=I["kind"], method="ARCS-rho", answer=r[0], payload=payload, time=dt, cert=c))
            h = c.get("handover", {})
            print(f"{name} #{j} {I['kind']:20s} {r[0]:4s} {dt:8.3f}s rho={c.get('rho',0):.2f} m_pred={c.get('m_pred')} m={h.get('m','-')} {h.get('endgame','-')} {'' if r[0]=='YES' else str(r[1:3])[:90]}", flush=True)
        res["problems"][name] = dict(instances=[dict(W=[str(w) for w in I["W"]], T=str(I["T"]), kind=I["kind"]) for I in insts], records=recs)
    gens = [("P1", gen_P1), ("P2", gen_P2), ("P3", gen_P3), ("P5", gen_P5), ("P6", gen_P6), ("P7", gen_P7), ("P8", gen_P8), ("P9", gen_P9)]
    for name, g in gens:
        insts = g()
        if DEV: insts = insts[:1] + insts[-1:]
        bench(name, insts)
    rnd = random.Random(SEED_BASE + 9); Wk = [2 * rnd.randint(1, 10**9) for _ in range(200)]; Tk = sum(Wk) // 2 | 1
    r = rho(Wk, Tk); res["K3"] = dict(W=[str(w) for w in Wk], T=str(Tk), answer=list(r[:3]))
    print("K3", res["K3"]["answer"], flush=True)
    I = gen_P6()[0]; r = rho(I["W"], I["T"], max_ops=2 ** 20)
    res["K4"] = dict(inst="P6 #0", max_ops=2 ** 20, answer=list(r[:2]) if r[0] != "YES" else ["YES"])
    print("K4", res["K4"]["answer"], flush=True)
    json.dump(res, open("results_dev.json" if DEV else "results_v1.json", "w"))
    print("done", flush=True)
