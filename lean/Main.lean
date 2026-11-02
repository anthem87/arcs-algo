module

public import ArcsAlgo.Checker
public import ArcsAlgo.Exhaustive
public import Lean.Data.Json

set_option autoImplicit false

/-!
# `verify_bench`: checks every answer of a benchmark results file with the certified checker

Usage: `lake exe verify_bench <results.json> [<python_check.txt>]`. The file is either a BENCH5
results file (`benchmarks/bench5_v2`) or the results file of the default
solver (`benchmarks/arcs_rho`, method `ARCS-rho`, weights written as strings).

For each record of `problems.<P>.records`:
* `YES` → `checkYes` on `payload[0]`;
* `NO` with `payload = [q, c]`, `q > 0` → `checkNo`; `q = 0` → `checkRange`;
  `(q, c) = (-3, -3)` → `checkExhaustiveNo` (exact meet-in-the-middle);
  `q = -1` (CPSAT) or `q = -2` (BNB) → solver proof, not checked;
* `FAIL` → no claim.
A YES on an `impossible` instance, or a NO on a planted or partition one, counts as failed even
when the certificate passes. Soundness of the checks is proved in `ArcsAlgo.Checker` and
`ArcsAlgo.Exhaustive`.

With a second argument (the output of the Python checker `checker5.py` or `checker7.py`), the
counts are compared line by line. The exit code is non-zero if an ARCS answer YES/NO does not
pass, if a control K1–K5 does not behave as expected, or if the counts of ARCS differ from those
of the Python checker.
-/

@[expose] public section

open Lean ArcsAlgo

/-- Outcome of the check of one record. -/
inductive Verdict where
  | verified
  | failed
  | unchecked
  | noClaim
  deriving BEq

/-- Counts of the verdicts for one (problem, instance kind, method). -/
structure Counts where
  verified : Nat := 0
  failed : Nat := 0
  unchecked : Nat := 0
  noClaim : Nat := 0

def Counts.add (c : Counts) : Verdict → Counts
  | .verified => { c with verified := c.verified + 1 }
  | .failed => { c with failed := c.failed + 1 }
  | .unchecked => { c with unchecked := c.unchecked + 1 }
  | .noClaim => { c with noClaim := c.noClaim + 1 }

def Counts.total (c : Counts) : Nat := c.verified + c.failed + c.unchecked + c.noClaim

/-- One instance: weights, target and kind. -/
structure Inst where
  W : List Nat
  T : Nat
  kind : String

/-- `e` succeeded with a value satisfying `p`. -/
def okAnd {α : Type} (e : Except String α) (p : α → Bool) : Bool :=
  match e with
  | .ok a => p a
  | .error _ => false

def isImpossible (kind : String) : Bool := (kind.splitOn "impossible").length > 1

/-- A natural number written as a JSON number or as a decimal string (arbitrary precision). -/
def getNatFlex (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => .ok n
  | .error _ => do
    let s ← j.getStr?
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {s}"

def getNatList (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM getNatFlex

def parseInst (j : Json) : Except String Inst := do
  return { W := ← getNatList (← j.getObjVal? "W"), T := ← getNatFlex (← j.getObjVal? "T"),
           kind := ← (← j.getObjVal? "kind").getStr? }

/-- A NO answer is wrong on a planted or partition instance (as in `checker7.py`). -/
def isFeasible (kind : String) : Bool := kind.startsWith "planted" || kind == "partition"

/-- The verdict on one record. With `rho` (results of the default solver), the key is the full
instance kind, as in `checker7.py`; otherwise it is `feasible` or `impossible`, as in
`checker5.py`. -/
def checkRecord (rho : Bool) (insts : Array Inst) (r : Json) :
    Except String (String × String × Verdict) := do
  let i ← getNatFlex (← r.getObjVal? "inst")
  let method ← (← r.getObjVal? "method").getStr?
  let answer ← (← r.getObjVal? "answer").getStr?
  let kind ← (← r.getObjVal? "kind").getStr?
  let some I := insts[i]? | throw s!"instance {i} out of range"
  let imp := isImpossible kind
  let feas := isFeasible kind
  let payload ← r.getObjVal? "payload"
  let v ← match answer with
    | "YES" =>
      let idx ← getNatList (← payload.getArrVal? 0)
      pure (if checkYes I.W I.T idx && !imp then Verdict.verified else Verdict.failed)
    | "NO" =>
      let q ← (← payload.getArrVal? 0).getInt?
      let c ← (← payload.getArrVal? 1).getInt?
      if q > 0 then
        pure (if 0 ≤ c && checkNo I.W I.T q.toNat c.toNat && !feas then .verified else .failed)
      else if q == 0 then
        pure (if checkRange I.W I.T && !feas then .verified else .failed)
      else if q == -3 && c == -3 then
        pure (if checkExhaustiveNo I.W I.T && !feas then .verified else .failed)
      else if (q == -1 && method == "CPSAT") || (q == -2 && method == "BNB") then
        pure .unchecked
      else pure .failed
    | "FAIL" => pure .noClaim
    | a => throw s!"unknown answer {a}"
  return (method, (if rho then kind else if imp then "impossible" else "feasible"), v)

/-- Key of a line of the report: (problem, instance kind, method). -/
abbrev Key := String × String × String

/-- The lines `  <kind> <method> correct a/b  wrong c  fail d ...` of the Python report,
as `((P, kind, method), (a, b, c, d))`. -/
def parsePythonReport (rho : Bool) (txt : String) : List (Key × Nat × Nat × Nat × Nat) := Id.run do
  let mut out := []
  let mut prob := ""
  for line in txt.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    -- `checker7.py` writes `<kind words> correct ...`, `checker5.py` writes `<kind> <method> correct ...`.
    let head := ws.takeWhile (· ≠ "correct")
    let ws := if rho && head.length < ws.length then
      " ".intercalate head :: "ARCS-rho" :: ws.drop head.length else ws
    match ws with
    | [p] => if p.startsWith "P" then prob := p
    | kind :: method :: "correct" :: ab :: "wrong" :: c :: "fail" :: d :: _ =>
      match ab.splitOn "/" with
      | [a, b] =>
        if let (some a, some b, some c, some d) := (a.toNat?, b.toNat?, c.toNat?, d.toNat?) then
          out := out ++ [((prob, kind, method), (a, b, c, d))]
      | _ => pure ()
    | _ => pure ()
  return out

def pad (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- The first YES record on instance `i` of a problem. -/
def findYes (recs : Array Json) (i : Nat) : Option Json :=
  recs.find? fun r =>
    okAnd (r.getObjVal? "inst" >>= getNatFlex) (· == i) &&
      okAnd (r.getObjVal? "answer" >>= Json.getStr?) (· == "YES")

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: verify_bench <results.json> [<check.txt>]"; return 2
  let t0 ← IO.monoMsNow
  let R ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let problems ← IO.ofExcept ((← IO.ofExcept (R.getObjVal? "problems")).getObj?)
  -- The results of the default solver have method `ARCS-rho`.
  let rho := problems.toList.any fun (_, P) =>
    okAnd (P.getObjVal? "records" >>= Json.getArr?) fun recs =>
      recs.any fun r => okAnd (r.getObjVal? "method" >>= Json.getStr?) (· == "ARCS-rho")
  let arcs (m : String) : Bool := m == "ARCS" || m == "ARCS-rho"
  let mut bad := false
  -- Controls K1–K3, as in the Python checker.
  let P1 ← IO.ofExcept (R.getObjVal? "problems" >>= (·.getObjVal? "P1"))
  let insts1 ← IO.ofExcept ((← IO.ofExcept (P1.getObjVal? "instances")).getArr? >>= (·.mapM parseInst))
  let recs1 ← IO.ofExcept ((← IO.ofExcept (P1.getObjVal? "records")).getArr?)
  let some I0 := insts1[0]? | throw (IO.userError "P1 has no instance")
  let some yes0 := findYes recs1 0 | throw (IO.userError "no YES record on P1 instance 0")
  let idx ← IO.ofExcept (yes0.getObjVal? "payload" >>= (·.getArrVal? 0) >>= getNatList)
  let fresh := (List.range I0.W.length).find? (· ∉ idx)
  let k0 := checkYes I0.W I0.T idx
  let k1 := match fresh with
    | some j => !checkYes I0.W I0.T (idx.dropLast ++ [j])
    | none => false
  let k2 := !checkNo I0.W I0.T 7 (I0.T % 7)
  IO.println s!"K0 original YES of P1/0 accepted: {k0}"
  IO.println s!"K1 rejected: {k1}"
  IO.println s!"K2 rejected: {k2}"
  if let .ok K3 := R.getObjVal? "K3" then
    let I3 ← IO.ofExcept (parseInst (Json.mkObj [("W", ← IO.ofExcept (K3.getObjVal? "W")),
      ("T", ← IO.ofExcept (K3.getObjVal? "T")), ("kind", "K3")]))
    let ans ← IO.ofExcept (K3.getObjVal? "answer" >>= Json.getArr?)
    let k3 := match ans.toList with
      | a :: q :: c :: _ =>
        okAnd a.getStr? (· == "NO") &&
          match getNatFlex q, getNatFlex c with
          | .ok q, .ok c => checkNo I3.W I3.T q c
          | _, _ => false
      | _ => false
    IO.println s!"K3 all-even weights, odd target, ARCS NO certificate accepted: {k3}"
    bad := bad || !k3
  if let .ok K4 := R.getObjVal? "K4" then
    let ans ← IO.ofExcept (K4.getObjVal? "answer" >>= Json.getArr?)
    let k4 := match ans.toList with
      | a :: why :: _ => okAnd a.getStr? (· == "FAIL") && okAnd why.getStr? (·.startsWith "predicted")
      | _ => false
    IO.println s!"K4 small max_ops: FAIL with prediction (no claim): {k4}"
    bad := bad || !k4
  -- Control K5: a false exhaustive certificate `(-3, -3)` on instances with a solution.
  -- (a) the first 24 weights of P1/0 with the target given by the weights at even positions;
  let W5 := I0.W.take 24
  let T5 := ((List.range W5.length).filter (· % 2 == 0)).foldl (fun s i => s + W5.getD i 0) 0
  let k5a := !checkExhaustiveNo W5 T5
  IO.println s!"K5a false (-3, -3) on the first {W5.length} weights of P1/0, target = sum at even positions, rejected: {k5a}"
  bad := bad || !k5a
  -- (b) the smallest planted instance with at most 50 weights and a verified YES, if any.
  let mut best : Option (String × Nat × Inst) := none
  for (name, P) in problems.toList do
    let insts ← IO.ofExcept ((← IO.ofExcept (P.getObjVal? "instances")).getArr? >>= (·.mapM parseInst))
    let recs ← IO.ofExcept ((← IO.ofExcept (P.getObjVal? "records")).getArr?)
    for h : i in [0:insts.size] do
      let I := insts[i]
      if I.W.length ≤ 50 && isFeasible I.kind then
        if let some y := findYes recs i then
          if let .ok ix := y.getObjVal? "payload" >>= (·.getArrVal? 0) >>= getNatList then
            let smaller : Bool := match best with
              | some (_, _, J) => decide (I.W.length < J.W.length)
              | none => true
            if checkYes I.W I.T ix && smaller then
              best := some (name, i, I)
  match best with
  | some (name, i, I) =>
    let s5 ← IO.monoMsNow
    let k5b := !checkExhaustiveNo I.W I.T
    IO.println s!"K5b false (-3, -3) on {name}/{i} ({I.kind}, n = {I.W.length}, verified YES), rejected: {k5b}  ({(← IO.monoMsNow) - s5} ms)"
    bad := bad || !k5b
  | none => IO.println "K5b skipped: no planted instance with at most 50 weights"
  bad := bad || !k0 || !k1 || !k2
  -- Records.
  let mut table : List (Key × Counts) := []
  for (name, P) in problems.toList do
    let tp ← IO.monoMsNow
    let insts ← IO.ofExcept ((← IO.ofExcept (P.getObjVal? "instances")).getArr? >>= (·.mapM parseInst))
    let recs ← IO.ofExcept ((← IO.ofExcept (P.getObjVal? "records")).getArr?)
    let mut counts : List (Key × Counts) := []
    let mut maxRec := 0
    let mut nExh := 0
    for r in recs do
      let tr ← IO.monoMsNow
      let (method, kind, v) ← IO.ofExcept (checkRecord rho insts r)
      let dt := (← IO.monoMsNow) - tr
      maxRec := max maxRec dt
      if okAnd (r.getObjVal? "payload" >>= (·.getArrVal? 0) >>= Json.getInt?) (· == -3) then
        nExh := nExh + 1
      if arcs method && v == .failed then
        bad := true
        IO.println s!"FAILED ARCS record on {name}: {r.compress.take 200}"
      let key := (name, kind, method)
      let c := (counts.lookup key).getD {}
      counts := (key, c.add v) :: counts.filter (·.1 != key)
    let sorted := counts.toArray.qsort (fun a b =>
      a.1.2.1 < b.1.2.1 || (a.1.2.1 == b.1.2.1 && a.1.2.2 < b.1.2.2)) |>.toList
    let exh := if nExh > 0 then s!", {nExh} exhaustive NO (-3, -3)" else ""
    IO.println s!"\n{name}  ({recs.size} records{exh}; {(← IO.monoMsNow) - tp} ms, longest record {maxRec} ms)"
    for ((_, kind, method), c) in sorted do
      IO.println s!"  {pad kind 22} {pad method 8} verified {c.verified}/{c.total}  failed {c.failed}  not checked (solver proof) {c.unchecked}  no claim (FAIL) {c.noClaim}"
    table := table ++ sorted
  -- Comparison with the Python checker.
  if let some (pyPath : String) := args[1]? then
    let py := parsePythonReport rho (← IO.FS.readFile ⟨pyPath⟩)
    IO.println s!"\nComparison with {pyPath} (Python 'correct' = verified + solver proofs not checked here)"
    let mut mismatches := 0
    for (key, (a, b, w, f)) in py do
      let (p, kind, method) := key
      match table.lookup key with
      | none => IO.println s!"  {p} {kind} {method}: missing in Lean"; mismatches := mismatches + 1
      | some c =>
        let same := c.verified + c.unchecked == a && c.total == b && c.failed == w && c.noClaim == f
        let tag := if same then "same" else "DIFFERENT"
        IO.println s!"  {p} {pad kind 22} {pad method 8} Python {a}/{b} wrong {w} fail {f}  |  Lean {c.verified}+{c.unchecked}/{c.total} failed {c.failed} no claim {c.noClaim}  {tag}"
        if !same then
          mismatches := mismatches + 1
          if arcs method then bad := true
    if py.length != table.length then
      IO.println s!"  number of lines: Python {py.length}, Lean {table.length}"
      bad := true
    IO.println s!"  mismatches: {mismatches}"
  IO.println s!"\ntotal time {(← IO.monoMsNow) - t0} ms"
  IO.println (if bad then "\nRESULT: FAILURE" else "\nRESULT: all ARCS answers verified")
  return if bad then 1 else 0
