module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Fold
set_option autoImplicit false

/-!
# Pruning of the dynamic moduli, paper Lemma 5.3, parts 1 and 2

Abstract form. `C` is the finite set of candidate moduli. For each `q ∈ C`, `x q ≥ 0` is the
class density `q · N_c / 2^m` at the class of the target, and `δ q ≥ 0` bounds its deviation,
`|x q - 1| ≤ δ q` (`δ q` is the largest deviation over the classes). For `0 < ε ≤ 1` the
retained moduli are `Q = {q ∈ C : δ q ≥ ε}`.

* Part 1 (`pruning_part1`): if `x q = 0` for some `q ∈ C` (the class of the target is empty mod
  `q`, so `q` gives a NO certificate) then `q ∈ Q`: pruning removes no NO answer.
* Part 2 (`pruning_part2`): if `x q > 0` for every `q ∈ C`, the scores
  `b_Q = max (0, max_{q ∈ Q} log x q)` and `b_C = max (0, max_{q ∈ C} log x q)` satisfy
  `0 ≤ b_C - b_Q ≤ log (1 + ε)`.

Part 3 of paper Lemma 5.3, which goes through Lemma C(1), is analytic and is not formalised here.

The second half of the file (`PruningModel`) states parts 1 and 2 in the form of the paper.
-/

@[expose] public section

namespace ArcsAlgo

/-- The data of paper Lemma 5.3: candidate moduli `C`, densities `x`, deviation bounds
`δ` and threshold `ε`, with the standing hypotheses `x ≥ 0`, `δ ≥ 0`, `|x - 1| ≤ δ` on `C`, and
`0 < ε ≤ 1`. -/
structure PruningData (ι : Type*) where
  /-- The candidate moduli. -/
  C : Finset ι
  /-- The class density `q · N_c / 2^m` at the class of the target. -/
  x : ι → ℝ
  /-- The largest deviation of the class densities from `1`. -/
  δ : ι → ℝ
  /-- The pruning threshold. -/
  ε : ℝ
  x_nonneg : ∀ q ∈ C, 0 ≤ x q
  δ_nonneg : ∀ q ∈ C, 0 ≤ δ q
  dev_le : ∀ q ∈ C, |x q - 1| ≤ δ q
  ε_pos : 0 < ε
  ε_le_one : ε ≤ 1

namespace PruningData

variable {ι : Type*} (D : PruningData ι)

/-- The retained moduli `Q = {q ∈ C : δ q ≥ ε}` of paper Lemma 5.3. -/
noncomputable def Q : Finset ι :=
  open Classical in D.C.filter fun q => D.ε ≤ D.δ q

/-- The score `max (0, max_{q ∈ s} log x q)` of paper Lemma 5.3. -/
noncomputable def score (s : Finset ι) : ℝ :=
  s.fold max 0 fun q => Real.log (D.x q)

/-- Membership in the retained set `Q` of paper Lemma 5.3. -/
theorem mem_Q {q : ι} : q ∈ D.Q ↔ q ∈ D.C ∧ D.ε ≤ D.δ q := by
  classical
  unfold Q
  convert Finset.mem_filter

/-- The score of paper Lemma 5.3 is at least `0`. -/
theorem score_nonneg (s : Finset ι) : 0 ≤ D.score s :=
  (Finset.le_fold_max 0).2 (Or.inl le_rfl)

/-- Every `log x q`, `q ∈ s`, is at most the score of `s` (paper Lemma 5.3). -/
theorem log_le_score {s : Finset ι} {q : ι} (hq : q ∈ s) : Real.log (D.x q) ≤ D.score s :=
  (Finset.le_fold_max _).2 (Or.inr ⟨q, hq, le_rfl⟩)

/-- Paper Lemma 5.3, part 1: a modulus `q ∈ C` whose target class is empty (`x q = 0`)
has deviation `δ q ≥ 1 ≥ ε`, so it is retained in `Q`: pruning removes no NO certificate.
Uses `|x - 1| ≤ δ` and `ε ≤ 1`. -/
theorem pruning_part1 {q : ι} (hq : q ∈ D.C) (hx : D.x q = 0) : q ∈ D.Q := by
  refine D.mem_Q.2 ⟨hq, ?_⟩
  have h := D.dev_le q hq
  rw [hx, zero_sub, abs_neg, abs_one] at h
  exact D.ε_le_one.trans h

/-- Paper Lemma 5.3, part 2: if `x q > 0` for every `q ∈ C`, then
`0 ≤ b_C - b_Q ≤ log (1 + ε)`, with `b_s = max (0, max_{q ∈ s} log x q)`.
Uses `|x - 1| ≤ δ` and `ε > 0`; positivity of `x` is only used through `Real.log_le_log`. -/
theorem pruning_part2 (hpos : ∀ q ∈ D.C, 0 < D.x q) :
    0 ≤ D.score D.C - D.score D.Q ∧ D.score D.C - D.score D.Q ≤ Real.log (1 + D.ε) := by
  have hlog : 0 ≤ Real.log (1 + D.ε) := Real.log_nonneg (by linarith [D.ε_pos])
  constructor
  · have : D.score D.Q ≤ D.score D.C :=
      (Finset.fold_max_le _).2 ⟨D.score_nonneg _, fun q hq => D.log_le_score (D.mem_Q.1 hq).1⟩
    linarith
  · have : D.score D.C ≤ D.score D.Q + Real.log (1 + D.ε) := by
      refine (Finset.fold_max_le _).2 ⟨by linarith [D.score_nonneg D.Q], fun q hq => ?_⟩
      by_cases hδ : D.ε ≤ D.δ q
      · linarith [D.log_le_score (D.mem_Q.2 ⟨hq, hδ⟩)]
      · replace hδ := lt_of_not_ge hδ
        have h := D.dev_le q hq
        have hx : D.x q ≤ 1 + D.ε := by linarith [le_abs_self (D.x q - 1)]
        linarith [Real.log_le_log (hpos q hq) hx, D.score_nonneg D.Q]
    linarith

end PruningData

/-! ### Paper Lemma 5.3 in the form of the paper (§5.7)

The model of `PruningData` above is abstract: one target, densities `x q` directly. Here the
statement is the one of the paper. For a suffix of size `m ≥ 1`, `C` is the finite set of
candidate moduli, `x t q ≥ 0` is the class value `N_q[t mod q]` at the class of the target `t`
(`x t q = 0`: the class is empty), and `δ q ≥ 0` is the largest deviation over the classes,
which does not depend on the target; the only property of `δ` used is
`|q · x t q / 2^m - 1| ≤ δ q` for every target. The selected moduli are
`Q ε = {q ∈ C : δ q ≥ ε}`, the class correction is
`b_S = max (0, max_{q ∈ S} ln (q · x t q / 2^m))`, and the score is `s_S = G t + b_S`, or `⊥`
(that is `-∞`, in `WithBot ℝ`) as soon as some `q ∈ S` has an empty class
(pseudocode `SCORE`, lines 6–12).

The range condition `0 ≤ t ≤ S_k` of the paper only makes the Gaussian term `G` finite; in this
model `G t` is a real number, so the condition does not appear.
-/

/-- The model of paper Lemma 5.3 (§5.7) for a suffix of size `m ≥ 1`, over targets `τ`
(pseudocode `PREPROCESS`, lines 9–11, and `SCORE`, lines 6–12). -/
structure PruningModel (τ : Type*) where
  /-- The size of the suffix. -/
  m : ℕ
  one_le_m : 1 ≤ m
  /-- The candidate moduli. -/
  C : Finset ℕ
  /-- The class value `N_q[t mod q]` at the class of the target `t`. -/
  x : τ → ℕ → ℝ
  /-- The largest deviation `max_c |q · N_q[c] / 2^m - 1|` over the classes. -/
  δ : ℕ → ℝ
  /-- The common Gaussian term of the score. -/
  G : τ → ℝ
  x_nonneg : ∀ t, ∀ q ∈ C, 0 ≤ x t q
  δ_nonneg : ∀ q ∈ C, 0 ≤ δ q
  dev_le : ∀ t, ∀ q ∈ C, |(q : ℝ) * x t q / 2 ^ m - 1| ≤ δ q

namespace PruningModel

variable {τ : Type*} (D : PruningModel τ)

/-- The class density `q · x t q / 2^m` (paper §5.7, Lemma 5.3). -/
noncomputable def density (t : τ) (q : ℕ) : ℝ := (q : ℝ) * D.x t q / 2 ^ D.m

/-- The selected moduli `Q = {q ∈ C : δ q ≥ ε}` (paper §5.7, Lemma 5.3; pseudocode `PREPROCESS`,
line 11). -/
noncomputable def Q (ε : ℝ) : Finset ℕ :=
  open Classical in D.C.filter fun q => ε ≤ D.δ q

/-- The class correction `b_S = max (0, max_{q ∈ S} ln (q · x t q / 2^m))` (paper §5.7,
Lemma 5.3; pseudocode `SCORE`, line 11). -/
noncomputable def b (t : τ) (S : Finset ℕ) : ℝ :=
  S.fold max 0 fun q => Real.log (D.density t q)

/-- The score `s_S = G t + b_S`, or `⊥` (`-∞`) if some `q ∈ S` has an empty class (paper §5.7,
Lemma 5.3; pseudocode `SCORE`, lines 9–12). -/
noncomputable def score (t : τ) (S : Finset ℕ) : WithBot ℝ :=
  open Classical in if ∃ q ∈ S, D.x t q = 0 then ⊥ else ((D.G t + D.b t S : ℝ) : WithBot ℝ)

/-- Membership in the selected set `Q` (paper §5.7, Lemma 5.3). -/
theorem mem_Q {ε : ℝ} {q : ℕ} : q ∈ D.Q ε ↔ q ∈ D.C ∧ ε ≤ D.δ q := by
  classical
  unfold Q
  convert Finset.mem_filter

/-- `Q ⊆ C` (paper §5.7, Lemma 5.3). -/
theorem Q_subset (ε : ℝ) : D.Q ε ⊆ D.C := fun _ hq => (D.mem_Q.1 hq).1

/-- An empty class has deviation at least `1` (paper §5.7, Lemma 5.3: an empty class gives
deviation exactly `1`): it follows from `|q · x / 2^m - 1| ≤ δ q` at `x = 0`. -/
theorem one_le_δ_of_empty {t : τ} {q : ℕ} (hq : q ∈ D.C) (hx : D.x t q = 0) : 1 ≤ D.δ q := by
  have h := D.dev_le t q hq
  rwa [hx, mul_zero, zero_div, zero_sub, abs_neg, abs_one] at h

/-- The score is `⊥` iff some modulus of `S` has an empty class (paper §5.7, Lemma 5.3;
pseudocode `SCORE`, lines 9–10). -/
theorem score_eq_bot_iff (t : τ) (S : Finset ℕ) : D.score t S = ⊥ ↔ ∃ q ∈ S, D.x t q = 0 := by
  classical
  unfold score
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' WithBot.coe_ne_bot, fun h' => absurd h' h⟩

/-- Paper Lemma 5.3 (§5.7), part 1: if the class of the target is empty for some `q ∈ C`, then
`q ∈ Q` and `s_Q = s_C = -∞`, for every `ε ≤ 1` (pseudocode `PREPROCESS`, line 11, and `SCORE`,
lines 9–10). -/
theorem pruning_part1_full {ε : ℝ} (hε : ε ≤ 1) {t : τ} {q : ℕ} (hq : q ∈ D.C)
    (hx : D.x t q = 0) : q ∈ D.Q ε ∧ D.score t (D.Q ε) = ⊥ ∧ D.score t D.C = ⊥ := by
  have hQ : q ∈ D.Q ε := D.mem_Q.2 ⟨hq, hε.trans (D.one_le_δ_of_empty hq hx)⟩
  exact ⟨hQ, (D.score_eq_bot_iff _ _).2 ⟨q, hQ, hx⟩, (D.score_eq_bot_iff _ _).2 ⟨q, hq, hx⟩⟩

/-- Corollary of paper Lemma 5.3 (§5.7), part 1: for every target, the NO answers read with the
selected moduli `Q` are exactly those read with `C`, for every `ε ≤ 1` (pseudocode `ARCS`,
lines 13–14, with `Q = Sel[1]`). -/
theorem exists_empty_Q_iff {ε : ℝ} (hε : ε ≤ 1) (t : τ) :
    (∃ q ∈ D.C, D.x t q = 0) ↔ ∃ q ∈ D.Q ε, D.x t q = 0 :=
  ⟨fun ⟨q, hq, hx⟩ => ⟨q, (D.pruning_part1_full hε hq hx).1, hx⟩,
    fun ⟨q, hq, hx⟩ => ⟨q, D.Q_subset ε hq, hx⟩⟩

/-- Corollary of paper Lemma 5.3 (§5.7), part 1, on the scores: `s_Q = -∞ ↔ s_C = -∞`, for every
`ε ≤ 1` and every target. -/
theorem score_Q_eq_bot_iff {ε : ℝ} (hε : ε ≤ 1) (t : τ) :
    D.score t (D.Q ε) = ⊥ ↔ D.score t D.C = ⊥ := by
  rw [D.score_eq_bot_iff, D.score_eq_bot_iff, D.exists_empty_Q_iff hε]

/-- `0 ≤ b_S` (paper §5.7, Lemma 5.3). -/
theorem b_nonneg (t : τ) (S : Finset ℕ) : 0 ≤ D.b t S :=
  (Finset.le_fold_max 0).2 (Or.inl le_rfl)

/-- `ln (q · x t q / 2^m) ≤ b_S` for `q ∈ S` (paper §5.7, Lemma 5.3). -/
theorem log_density_le_b {t : τ} {S : Finset ℕ} {q : ℕ} (hq : q ∈ S) :
    Real.log (D.density t q) ≤ D.b t S :=
  (Finset.le_fold_max _).2 (Or.inr ⟨q, hq, le_rfl⟩)

/-- `0 ≤ b_C - b_Q ≤ ln (1 + ε)` for `ε > 0` (paper §5.7, Lemma 5.3, part 2, on the class
corrections). -/
theorem b_C_sub_b_Q {ε : ℝ} (hε : 0 < ε) (t : τ) :
    0 ≤ D.b t D.C - D.b t (D.Q ε) ∧ D.b t D.C - D.b t (D.Q ε) ≤ Real.log (1 + ε) := by
  have hlog : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  constructor
  · have : D.b t (D.Q ε) ≤ D.b t D.C :=
      (Finset.fold_max_le _).2 ⟨D.b_nonneg _ _, fun q hq => D.log_density_le_b (D.Q_subset ε hq)⟩
    linarith
  · have : D.b t D.C ≤ D.b t (D.Q ε) + Real.log (1 + ε) := by
      refine (Finset.fold_max_le _).2 ⟨by linarith [D.b_nonneg t (D.Q ε)], fun q hq => ?_⟩
      by_cases hδ : ε ≤ D.δ q
      · linarith [D.log_density_le_b (t := t) (D.mem_Q.2 ⟨hq, hδ⟩)]
      · replace hδ := lt_of_not_ge hδ
        have h := D.dev_le t q hq
        have hd : D.density t q ≤ 1 + ε := by
          unfold density; linarith [le_abs_self ((q : ℝ) * D.x t q / 2 ^ D.m - 1)]
        have hd0 : 0 ≤ D.density t q := by
          unfold density; have := D.x_nonneg t q hq; positivity
        rcases hd0.eq_or_lt with h0 | h0
        · rw [← h0, Real.log_zero]; linarith [D.b_nonneg t (D.Q ε)]
        · linarith [Real.log_le_log h0 hd, D.b_nonneg t (D.Q ε)]
    linarith

/-- Paper Lemma 5.3 (§5.7), part 2: if no class of `C` is empty, the scores `s_C` and `s_Q` are
finite and `0 ≤ s_C - s_Q ≤ ln (1 + ε) ≤ ε`. Only `ε > 0` is used; the paper takes
`ε ∈ (0, 1]` (pseudocode `PREPROCESS`, lines 10–11, and `SCORE`, lines 11–12). -/
theorem pruning_part2_full {ε : ℝ} (hε : 0 < ε) (t : τ) (hne : ∀ q ∈ D.C, D.x t q ≠ 0) :
    ∃ sC sQ : ℝ, D.score t D.C = sC ∧ D.score t (D.Q ε) = sQ ∧
      0 ≤ sC - sQ ∧ sC - sQ ≤ Real.log (1 + ε) ∧ Real.log (1 + ε) ≤ ε := by
  classical
  have hC : ¬ ∃ q ∈ D.C, D.x t q = 0 := fun ⟨q, hq, hx⟩ => hne q hq hx
  have hQ : ¬ ∃ q ∈ D.Q ε, D.x t q = 0 := fun ⟨q, hq, hx⟩ => hne q (D.Q_subset ε hq) hx
  obtain ⟨h1, h2⟩ := D.b_C_sub_b_Q hε t
  refine ⟨D.G t + D.b t D.C, D.G t + D.b t (D.Q ε), by simp [score, hC], by simp [score, hQ],
    by linarith, by linarith, ?_⟩
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + ε by linarith)
  linarith

/-- The threshold `ε = min (1, 1/m)` used by the solver lies in `(0, 1]` (paper §5.7; pseudocode
`PREPROCESS`, line 10, with `C_EPS = 1`). -/
theorem solver_ε_mem : 0 < min 1 (1 / (D.m : ℝ)) ∧ min 1 (1 / (D.m : ℝ)) ≤ 1 := by
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.one_le_m
  exact ⟨lt_min one_pos (by positivity), min_le_left _ _⟩

/-- Paper Lemma 5.3 (§5.7), parts 1 and 2, with the threshold `ε = min (1, 1/m)` of the solver
(pseudocode `PREPROCESS`, lines 10–11, with `C_EPS = 1`): an empty class of `C` is seen by `Q`,
and if no class of `C` is empty then `0 ≤ s_C - s_Q ≤ ln (1 + ε) ≤ ε ≤ 1/m`. -/
theorem pruning_solver (t : τ) :
    ((∃ q ∈ D.C, D.x t q = 0) ↔ ∃ q ∈ D.Q (min 1 (1 / (D.m : ℝ))), D.x t q = 0) ∧
    ((∀ q ∈ D.C, D.x t q ≠ 0) →
      ∃ sC sQ : ℝ, D.score t D.C = sC ∧ D.score t (D.Q (min 1 (1 / (D.m : ℝ)))) = sQ ∧
        0 ≤ sC - sQ ∧ sC - sQ ≤ Real.log (1 + min 1 (1 / (D.m : ℝ))) ∧
        Real.log (1 + min 1 (1 / (D.m : ℝ))) ≤ min 1 (1 / (D.m : ℝ)) ∧
        min 1 (1 / (D.m : ℝ)) ≤ 1 / (D.m : ℝ)) := by
  obtain ⟨h0, h1⟩ := D.solver_ε_mem
  refine ⟨D.exists_empty_Q_iff h1 t, fun hne => ?_⟩
  obtain ⟨sC, sQ, hC, hQ, a, b, c⟩ := D.pruning_part2_full h0 t hne
  exact ⟨sC, sQ, hC, hQ, a, b, c, min_le_right _ _⟩

end PruningModel

end ArcsAlgo
