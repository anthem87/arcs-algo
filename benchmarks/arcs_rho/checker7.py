"""Independent checker for CRITERION_BENCH7_v1. Does not import the solver's code.
   usage: python3 checker7.py results_v1.json   (run from this folder)"""
import sys, json, hashlib, statistics
from collections import defaultdict
R = json.load(open(sys.argv[1]))
assert hashlib.sha256(open("CRITERION_BENCH7_v1.md", "rb").read()).hexdigest() == R["sha256"], "criterion hash mismatch"
DECLARED = ("predicted", "budget", "scored-out", "both-out", "end", "endgame", "n>1020")
def reachable_mod(W, q):
    reach = 1; full = (1 << q) - 1
    for w in W:
        s = w % q
        if s: reach |= ((reach << s) | (reach >> (q - s))) & full
    return reach
def check_yes(W, T, idx): return len(set(idx)) == len(idx) and all(0 <= i < len(W) for i in idx) and sum(W[i] for i in idx) == T
def mitm_exists(W, T):
    h = len(W) // 2; A, B = W[:h], W[h:]
    sb = {0}
    for w in B: sb |= {x + w for x in sb}
    sa = [0]
    for w in A: sa = sa + [x + w for x in sa]
    return any((T - x) in sb for x in sa)
def check_no(W, T, q, c):
    if q == 0: return T < 0 or T > sum(W)
    if q == -3: return not mitm_exists(W, T)
    return q >= 2 and T % q == c and not ((reachable_mod(W, q) >> c) & 1)
out = []; say = lambda s: (print(s, flush=True), out.append(s))
say(f"criterion sha256 {R['sha256']}  seed_base {R['seed_base']}  dev={R['dev']}  params {R['params']}")
P = R["problems"]["P1"]; I = P["instances"][0]; W = [int(x) for x in I["W"]]; T = int(I["T"])
rec = next(r for r in P["records"] if r["inst"] == 0 and r["answer"] == "YES")
idx = list(rec["payload"][0]); bad = idx[:-1] + [next(i for i in range(len(W)) if i not in idx)]
say(f"K1 corrupted solution rejected: {not check_yes(W, T, bad)}")
say(f"K2 false NO certificate (q=7) rejected: {not check_no(W, T, 7, T % 7)}")
K3 = R["K3"]; ok3 = K3["answer"][0] == "NO" and check_no([int(x) for x in K3["W"]], int(K3["T"]), K3["answer"][1], K3["answer"][2])
say(f"K3 all-even weights, odd target: {K3['answer']}; NO with valid certificate: {ok3}")
k4 = R["K4"]["answer"]; say(f"K4 max_ops 2^20 on P6 #0: {k4}; FAIL with prediction: {k4[0] == 'FAIL' and str(k4[1]).startswith('predicted')}")
wrong = 0; undeclared = []; diffs = []
for name, P in R["problems"].items():
    insts = P["instances"]; st = defaultdict(lambda: dict(correct=0, wrong=0, fail=0, times=[], fails=[]))
    for r in P["records"]:
        I = insts[r["inst"]]; W = [int(x) for x in I["W"]]; T = int(I["T"]); s = st[I["kind"]]; s["times"].append(r["time"])
        h = r["cert"].get("handover")
        if h: diffs.append((name, r["cert"]["m_pred"] - h["m"]))
        if r["answer"] == "YES":
            if check_yes(W, T, r["payload"][0]): s["correct"] += 1
            else: s["wrong"] += 1
        elif r["answer"] == "NO":
            ok = check_no(W, T, r["payload"][0], r["payload"][1]) and not I["kind"].startswith("planted") and I["kind"] != "partition"
            if ok: s["correct"] += 1
            else: s["wrong"] += 1
        else:
            s["fail"] += 1; s["fails"].append((r["payload"][0], round(r["time"], 3)))
            if not str(r["payload"][0]).startswith(DECLARED): undeclared.append((name, r["inst"], r["payload"][0]))
    say(f"\n{name}")
    for kind, s in sorted(st.items()):
        wrong += s["wrong"]; tot = len(s["times"])
        say(f"  {kind:22s} correct {s['correct']}/{tot}  wrong {s['wrong']}  fail {s['fail']}  median time {statistics.median(s['times']):.3f} s" + (f"  fails: {s['fails']}" if s["fails"] else ""))
say(f"\nwrong answers: {wrong}")
say(f"undeclared FAIL reasons: {undeclared if undeclared else 'none'}")
ok = sum(1 for _, d in diffs if abs(d) <= 2)
say(f"prediction |m_pred - m| <= 2: {ok}/{len(diffs)} = {100*ok/max(1,len(diffs)):.1f}%  (pass if >= 90%);  differences: " + ", ".join(f"{d:+d}" for _, d in diffs))
open(sys.argv[1].replace(".json", "_check.txt"), "w").write("\n".join(out) + "\n")
