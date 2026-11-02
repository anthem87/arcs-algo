"""Independent checker for CRITERIO_BENCH5_v2. Does not import any solver code.
   usage: python3 checker5.py results_v2.json"""
import sys, json, hashlib, statistics
from collections import defaultdict
R = json.load(open(sys.argv[1]))
crit = open("CRITERIO_BENCH5_v2.md", "rb").read()
assert hashlib.sha256(crit).hexdigest() == R["sha256"], "criterion hash mismatch"
def reachable_mod(W, q):
    reach = 1                                      # bitmask over residues 0..q-1
    full = (1 << q) - 1
    for w in W:
        s = w % q
        reach |= ((reach << s) | (reach >> (q - s))) & full if s else 0
    return reach
def check_yes(W, T, idx):
    return len(set(idx)) == len(idx) and all(0 <= i < len(W) for i in idx) and sum(W[i] for i in idx) == T
def check_no(W, T, q, c, method):
    if method == "CPSAT" and q == -1: return "solver-proof"
    if method == "BNB" and q == -2: return "exhaustive-search"
    if q == 0: return T < 0 or T > sum(W)
    return T % q == c and not ((reachable_mod(W, q) >> c) & 1)
out = []; say = lambda s: (print(s), out.append(s))
say(f"criterion sha256 {R['sha256']}  seed_base {R['seed_base']}  dev={R['dev']}  time limit {R['TL']} s")
# K1, K2: the checker must reject corrupted answers
P = R["problems"]["P1"]; I = P["instances"][0]
rec = next(r for r in P["records"] if r["inst"] == 0 and r["answer"] == "YES")
idx = list(rec["payload"][0]); bad = idx[:-1] + [next(i for i in range(len(I["W"])) if i not in idx)]
say(f"K1 corrupted solution rejected: {not check_yes(I['W'], I['T'], bad)}")
W = I["W"]; q = 7; c = I["T"] % 7
say(f"K2 false NO certificate (q=7) rejected: {not check_no(W, I['T'], q, c, 'ARCS')}")
K3 = R["K3"]; say(f"K3 all-even weights, odd target -> ARCS answer {K3['answer'][:3]}; certificate valid: {K3['answer'][0]=='NO' and check_no(K3['W'], K3['T'], K3['answer'][1], K3['answer'][2], 'ARCS')}")
for name, P in R["problems"].items():
    insts = P["instances"]; stats = defaultdict(lambda: dict(solved=0, wrong=0, no=0, fail=0, times=[], times_ok=[]))
    for r in P["records"]:
        I = insts[r["inst"]]; st = stats[(r["method"], "impossible" if "impossible" in r["kind"] else "feasible")]
        st["times"].append(r["time"])
        if r["answer"] == "YES":
            ok = check_yes(I["W"], I["T"], r["payload"][0])
            if ok and "impossible" not in r["kind"]: st["solved"] += 1; st["times_ok"].append(r["time"])
            else: st["wrong"] += 1
        elif r["answer"] == "NO":
            v = check_no(I["W"], I["T"], r["payload"][0], r["payload"][1], r["method"])
            if v and "impossible" in r["kind"]: st["no"] += 1; st["times_ok"].append(r["time"])
            elif v and "impossible" not in r["kind"]: st["wrong"] += 1       # a NO on a planted instance is wrong
            elif not v: st["wrong"] += 1
        else: st["fail"] += 1
    say(f"\n{name}")
    for (m, kind), st in sorted(stats.items(), key=lambda x: (x[0][1], x[0][0])):
        tot = len(st["times"]); med = statistics.median(st["times"]) if st["times"] else float('nan')
        good = st["solved"] if kind == "feasible" else st["no"]
        say(f"  {kind:10s} {m:6s} correct {good}/{tot}  wrong {st['wrong']}  fail {st['fail']}  median time {med:.3f} s")
if R.get("P4"):
    say("\nP4 counting (relative error of ARCS-COUNT against the float DP)")
    for row in R["P4"]:
        say(f"  N={row['N']:5d} k={row['k']} rel.err {row['rel_err']:.2e}  est {row['t_est']*1e3:.3f} ms  DP {row['t_dp']:.2f} s")
say(f"\nDP bitset memory (n*S bits), min over instances: " + ", ".join(f"{k}: {min(v):.1e}" for k, v in R["dp_bits"].items()))
open(sys.argv[1].replace(".json", "_check.txt"), "w").write("\n".join(out) + "\n")
