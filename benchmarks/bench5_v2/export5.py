"""Exports every instance and every answer of the run in plain text, so anyone can check them by hand
   or with any tool. Reads results_v2.json; does not run any solver and does not change the run.
   Output folder export_v2/:
     <P>_<i>_instance.csv   one weight per line: index,weight   (header: target and kind)
     <P>_<i>_<METHOD>.csv    answer: YES -> index,weight lines and the sum; NO -> the certificate (q, c); FAIL -> reason
     INDEX.md                one line per (problem, instance, method) with the outcome of the check
     verify_one.py           standalone check: python3 verify_one.py P1_0_instance.csv P1_0_ARCS.csv"""
import json, os, sys, hashlib
R = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "results_v2.json"))
D = "export_v2"; os.makedirs(D, exist_ok=True)
lines = [f"# Export of the BENCH5 v2 run", f"criterion sha256 {R['sha256']}, seed_base {R['seed_base']}", "",
         "| problem | instance | kind | target | method | answer | sum of the chosen weights | check |", "|---|---|---|---|---|---|---|---|"]
def reach_bit(W, q, c):
    r = 1; full = (1 << q) - 1
    for w in W:
        s = w % q
        if s: r |= ((r << s) | (r >> (q - s))) & full
    return (r >> c) & 1
for name, P in R["problems"].items():
    for i, I in enumerate(P["instances"]):
        with open(f"{D}/{name}_{i}_instance.csv", "w") as f:
            f.write(f"# target {I['T']}\n# kind {I['kind']}\n# n {len(I['W'])}\nindex,weight\n")
            for j, w in enumerate(I["W"]): f.write(f"{j},{w}\n")
    for r in P["records"]:
        I = P["instances"][r["inst"]]; fn = f"{D}/{name}_{r['inst']}_{r['method']}.csv"
        with open(fn, "w") as f:
            f.write(f"# answer {r['answer']}\n# time {r['time']:.3f} s\n")
            if r["answer"] == "YES":
                idx = r["payload"][0]; s = sum(I["W"][j] for j in idx)
                f.write(f"# chosen {len(idx)} weights, sum {s}, target {I['T']}\nindex,weight\n")
                for j in idx: f.write(f"{j},{I['W'][j]}\n")
                ok = (s == I["T"] and len(set(idx)) == len(idx)); summ = str(s)
                chk = "sum = target, distinct indices" if ok else "WRONG"
            elif r["answer"] == "NO":
                q, c = r["payload"][0], r["payload"][1]
                if q > 0:
                    f.write(f"# certificate: no subset has sum = {c} (mod {q}); target mod {q} = {I['T'] % q}\n")
                    ok = I["T"] % q == c and not reach_bit(I["W"], q, c)
                    chk = f"certificate mod {q} verified" if ok else "WRONG certificate"
                else:
                    f.write("# infeasibility proof of the solver (CP-SAT INFEASIBLE) or exhaustive search\n"); chk = "solver proof"
                summ = "-"
            else:
                f.write(f"# no answer: {r['payload']}\n"); summ = "-"; chk = "-"
        lines.append(f"| {name} | {r['inst']} | {I['kind']} | {I['T']} | {r['method']} | {r['answer']} | {summ} | {chk} |")
if R.get("P4"):
    with open(f"{D}/P4_counts.csv", "w") as f:
        f.write("# r_N(T) = number of subsets of {1} U {primes <= N} with sum T; natural logs\nN,n,k,T,log_count_DP,log_count_ARCS,relative_error,ms_ARCS,s_DP\n")
        for row in R["P4"]:
            f.write(f"{row['N']},{row['n']},{row['k']},{row['T']},{row['log_ref']:.12f},{row['log_est']:.12f},{row['rel_err']:.3e},{row['t_est']*1e3:.4f},{row['t_dp']:.3f}\n")
    lines.append("\nP4: see P4_counts.csv (DP reference and ARCS estimate for each N, k)")
open(f"{D}/INDEX.md", "w").write("\n".join(lines) + "\n")
open(f"{D}/verify_one.py", "w").write('''"""Standalone check of one answer: python3 verify_one.py <instance.csv> <answer.csv>"""
import sys
def read(fn):
    head, rows = {}, []
    for line in open(fn):
        line = line.strip()
        if line.startswith("#"):
            k, _, v = line[2:].partition(" "); head[k] = v
        elif line and not line.startswith("index"):
            j, w = line.split(","); rows.append((int(j), int(w)))
    return head, rows
hi, inst = read(sys.argv[1]); ha, ans = read(sys.argv[2])
W = dict(inst); T = int(hi["target"])
if ha.get("answer") != "YES": print("not a YES answer:", ha); sys.exit(0)
idx = [j for j, _ in ans]
assert len(set(idx)) == len(idx), "repeated index"
assert all(W[j] == w for j, w in ans), "a weight does not match the instance"
s = sum(w for _, w in ans)
print(f"chosen {len(idx)} weights, sum {s}, target {T}:", "EXACT" if s == T else "NOT EQUAL")
''')
print("exported", len(lines) - 5, "answers to", D)
