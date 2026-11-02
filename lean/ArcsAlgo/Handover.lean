module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false

/-!
# The handover is known in advance

Paper §5.7: "The handover rule depends on `V_k` only, not on the target or on the path". In the
pseudocode `ARCS` the descent hands over to the endgame at the first step `k` whose triple
`(s, m, v) = SCORE(F, k, t)` passes the peak-density test of line 21,
`m · ln 2 - ½ · ln (2π · max (v, 1)) < ln λ*`; line 7 predicts this step as `k*`, the least `k`
with `(n - k + 1) · ln 2 - ½ · ln (2π · max (V[k], 1)) < ln λ*`.

Model. `w` is the list of the weights in the order of the descent (`w[k]` is `w[k - 1]` in Lean),
`n = w.length`, `S[k]` and `V[k]` are the suffix sums of `w[j]` and of `w[j]² / 4` over `j ≥ k`
(pseudocode `PREPROCESS`, lines 1–3). `SCORE` is modelled in full (pseudocode `SCORE`,
lines 1–12), with abstract selected moduli `Sel k` and class values `N k q c`. The run is any
sequence of include/exclude decisions `d`: `t₁ = T` and `t_{k+1} = t_k - w[k]` if `d k`, else
`t_k` (pseudocode `ARCS`, lines 16–33; the decisions of line 33 are a special case).

* `score_mv`: when `SCORE(F, k, t)` returns a triple, its `m` and `v` are `n - k + 1` and `V[k]`,
  whatever `t`;
* `handover_first`: for every target and every sequence of decisions, the line-21 test fails at
  every step `k < k*` that the run reaches, and holds at `k*` if the run reaches it. So the first
  step at which the test holds is `k*`.

Real arithmetic with `Real.log`; no numerical claim is made.
-/

@[expose] public section

namespace ArcsAlgo

open Real

/-- The peak-density test of pseudocode `ARCS`, lines 7 and 21, as a predicate of `(m, V, λ*)`
only (paper §5.7): `m · ln 2 - ½ · ln (2π · max (V, 1)) < ln λ*`. -/
def handoverTest (m : ℕ) (V lam : ℝ) : Prop :=
  (m : ℝ) * log 2 - 1 / 2 * log (2 * π * max V 1) < log lam

/-- The suffix sum `S[k] = Σ_{j ≥ k} w[j]` (paper §5.7; pseudocode `PREPROCESS`, line 3). -/
def suffixS (w : List ℕ) (k : ℕ) : ℕ := (w.drop (k - 1)).sum

/-- The suffix variance `V[k] = Σ_{j ≥ k} w[j]² / 4` (paper §5.7; pseudocode `ARCS`, line 6, and
`PREPROCESS`, line 3). -/
noncomputable def suffixV (w : List ℕ) (k : ℕ) : ℝ :=
  ((w.drop (k - 1)).map fun x => (x : ℝ) ^ 2 / 4).sum

/-- The data of `SCORE` (pseudocode `PREPROCESS`): the weights in the order of the descent, the
selected moduli `Sel k` and the class values `N k q c`. -/
structure ScoreData where
  /-- The weights `w[1‥n]`, in the order of the descent. -/
  w : List ℕ
  /-- The selected moduli `Sel[k]`. -/
  Sel : ℕ → Finset ℕ
  /-- The class value `N_q[k][c]`. -/
  N : ℕ → ℕ → ℕ → ℝ

/-- The test of pseudocode `ARCS`, line 21, on the triple `(s, m, v)` returned by `SCORE`
(paper §5.7). -/
def lineTest (r : ℝ × ℕ × ℝ) (lam : ℝ) : Prop := handoverTest r.2.1 r.2.2 lam

namespace ScoreData

variable (F : ScoreData)

/-- `SCORE(F, k, t)` of the pseudocode (`SCORE`, lines 1–12; paper §5.2 and §5.7): `none` stands
for `-∞`, otherwise the triple `(s, m, v)`. -/
noncomputable def score (k : ℕ) (t : ℤ) : Option (ℝ × ℕ × ℝ) :=
  open Classical in
  let m := F.w.length + 1 - k
  let S := suffixS F.w k
  let v := suffixV F.w k
  if t < 0 ∨ (S : ℤ) < t then none
  else if m = 0 then (if t = 0 then some (0, 0, 0) else none)
  else if ∃ q ∈ F.Sel k, F.N k q (t % (q : ℤ)).toNat = 0 then none
  else some ((m : ℝ) * log 2 - 1 / 2 * log (2 * π * v) - ((t : ℝ) - S / 2) ^ 2 / (2 * v) +
      (F.Sel k).fold max 0 (fun (q : ℕ) => log ((q : ℝ) * F.N k q (t % (q : ℤ)).toNat / 2 ^ m)), m, v)

/-- The target `t_k` before step `k` of a run with target `T` and decisions `d` (pseudocode
`ARCS`, lines 16–33): `t₁ = T`, `t_{k+1} = t_k - w[k]` if `d k`, else `t_k`. -/
def target (T : ℤ) (d : ℕ → Bool) : ℕ → ℤ
  | 0 => T
  | k + 1 => if k = 0 then T else if d k then target T d k - (F.w.getD (k - 1) 0 : ℤ)
      else target T d k

/-- The predicted handover step `k*` (paper §5.7; pseudocode `ARCS`, line 7): the least
`k ∈ [1, n]` that passes the test on `(n - k + 1, V[k], λ*)`, and `n + 1` if none does. -/
noncomputable def kStar (lam : ℝ) : ℕ :=
  open Classical in
  if h : ∃ k, 1 ≤ k ∧ k ≤ F.w.length ∧ handoverTest (F.w.length + 1 - k) (suffixV F.w k) lam
  then Nat.find h else F.w.length + 1

/-- When `SCORE(F, k, t)` returns a triple, its `m` and `v` are `n - k + 1` and `V[k]`, whatever
the target `t` (paper §5.7, "the handover rule depends on `V_k` only"; pseudocode `SCORE`,
lines 1 and 12, and `ARCS`, line 21). -/
theorem score_mv {k : ℕ} (hkn : k ≤ F.w.length) {t : ℤ} {r : ℝ × ℕ × ℝ}
    (h : F.score k t = some r) : r.2 = (F.w.length + 1 - k, suffixV F.w k) := by
  classical
  unfold score at h
  have hm : F.w.length + 1 - k ≠ 0 := by omega
  simp only [hm, ↓reduceIte] at h
  split_ifs at h
  cases h
  rfl

/-- The test of pseudocode `ARCS`, line 21, does not read the target: on any triple returned by
`SCORE(F, k, t)` it is the test on `(n - k + 1, V[k], λ*)` (paper §5.7). -/
theorem lineTest_iff {k : ℕ} (hkn : k ≤ F.w.length) {t : ℤ} {r : ℝ × ℕ × ℝ}
    (h : F.score k t = some r) (lam : ℝ) :
    lineTest r lam ↔ handoverTest (F.w.length + 1 - k) (suffixV F.w k) lam := by
  unfold lineTest
  rw [F.score_mv hkn h]

/-- The handover is known in advance (paper §5.7, "the handover rule depends on `V_k` only, not
on the target or on the path"; pseudocode `ARCS`, lines 7 and 21): for every target `T` and every
sequence of include/exclude decisions `d`, the test of line 21 fails at every step `k < k*` at
which `SCORE` returns a triple, and holds at `k*` if `k* ≤ n` and `SCORE` returns a triple there.
So the first step at which the test holds is `k*`. -/
theorem handover_first (lam : ℝ) (T : ℤ) (d : ℕ → Bool) :
    (∀ k, 1 ≤ k → k < F.kStar lam → k ≤ F.w.length →
      ∀ r, F.score k (F.target T d k) = some r → ¬ lineTest r lam) ∧
    (F.kStar lam ≤ F.w.length →
      ∀ r, F.score (F.kStar lam) (F.target T d (F.kStar lam)) = some r → lineTest r lam) := by
  classical
  constructor
  · intro k hk hlt hkn r hr ht
    rw [F.lineTest_iff hkn hr] at ht
    have hex : ∃ k, 1 ≤ k ∧ k ≤ F.w.length ∧
        handoverTest (F.w.length + 1 - k) (suffixV F.w k) lam := ⟨k, hk, hkn, ht⟩
    have : F.kStar lam ≤ k := by
      unfold kStar
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      exact Nat.find_min' hex ⟨hk, hkn, ht⟩
    omega
  · intro hle r hr
    have hex : ∃ k, 1 ≤ k ∧ k ≤ F.w.length ∧
        handoverTest (F.w.length + 1 - k) (suffixV F.w k) lam := by
      by_contra hne
      unfold kStar at hle
      rw [dite_eq_right_of_eq_false (eq_false hne)] at hle
      omega
    have hspec := Nat.find_spec hex
    have hk : F.kStar lam = Nat.find hex := by unfold kStar; rw [dite_eq_left_of_eq_true (eq_true hex)]
    rw [hk] at hr
    exact (F.lineTest_iff hspec.2.1 hr lam).2 hspec.2.2

end ScoreData

end ArcsAlgo
