"""Standalone check of one answer: python3 verify_one.py <instance.csv> <answer.csv>"""
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
