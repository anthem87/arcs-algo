module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
set_option autoImplicit false

/-!
# The centre rule: paper Lemma A (§6.1); pseudocode `CENTRE-RULE`

The descent of §6.1 is written in the doubled form, so that it stays in the integers.
Given weights `w₁, …, w_K` (natural numbers) and an initial error `E₀ ∈ ℤ`, the rule picks at each
step the sign that minimises the absolute value:
`E_k = E_{k-1} - w_k` if `|E_{k-1} - w_k| ≤ |E_{k-1} + w_k|`, and `E_{k-1} + w_k` otherwise.
Here `E_k = 2 t_k - (R_k + S_E)` in the notation of the paper; taking or leaving weight `k`
changes `E` by `∓ w_k`. Ties go to taking the weight, as in `CENTRE-RULE` of the pseudocode
(line 4, `≤`).

* `step_abs`: `|E_k| = | |E_{k-1}| - w_k |`;
* `centre_rule_bound`: `|E_k| ≤ max (|E₀| - Σ_{j ≤ k} w_j) (max_{j ≤ k} w_j)`, with the maximum of
  the empty list equal to `0`;
* `centre_rule_corollary`: if `|E₀| ≤ Σ_{j ≤ K} w_j + max_j w_j` then `|E_K| ≤ max_j w_j`.
  Undoubling, with `S_H = Σ_j w_j`, `w* = max_j w_j` and `E₀ = 2T - S`, `E_K = 2t - S_E`, this is
  the statement of §6.1: if `|T - S/2| ≤ S_H/2 + w*/2` the descent ends with
  `|t - S_E/2| ≤ w*/2`. No extra hypothesis is needed.
-/

@[expose] public section

namespace ArcsAlgo

/-- One step of the centre rule (paper Lemma A (§6.1), doubled form;
pseudocode `CENTRE-RULE`): take the weight
(`E - w`) if this does not increase `|E|` compared to leaving it (`E + w`). -/
def centreStep (E : ℤ) (w : ℕ) : ℤ :=
  if |E - w| ≤ |E + w| then E - w else E + w

/-- The error `E_k` after the first `k` steps of the centre rule
(paper Lemma A (§6.1); pseudocode `CENTRE-RULE`). -/
def centreSeq (E₀ : ℤ) (ws : List ℕ) (k : ℕ) : ℤ :=
  (ws.take k).foldl centreStep E₀

/-- The maximum of a list of natural numbers, `0` for the empty list. -/
def listMax (ws : List ℕ) : ℕ :=
  ws.foldr max 0

/-- One step of the centre rule (paper Lemma A (§6.1); pseudocode `CENTRE-RULE`):
`|E_k| = | |E_{k-1}| - w_k |`. -/
theorem step_abs (E : ℤ) (w : ℕ) : |centreStep E w| = |(|E| - (w : ℤ))| := by
  unfold centreStep
  have hw : (0 : ℤ) ≤ w := Int.natCast_nonneg w
  rcases le_total 0 E with hE | hE
  · rw [abs_of_nonneg hE]
    have h : |E - w| ≤ |E + w| := by
      rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ E + w)]
      exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    simp only [h, ↓reduceIte]
  · rw [abs_of_nonpos hE, show -E - (w : ℤ) = -(E + w) by omega, abs_neg]
    split_ifs with h
    · rw [abs_of_nonpos (by linarith : E - (w : ℤ) ≤ 0)] at h ⊢
      exact le_antisymm h (abs_le.2 ⟨by linarith, by linarith⟩)
    · rfl

/-- The recursion `|E_{k+1}| = | |E_k| - w_{k+1} |` along the sequence
(paper Lemma A (§6.1); pseudocode `CENTRE-RULE`). -/
theorem centreSeq_succ_abs (E₀ : ℤ) (ws : List ℕ) {k : ℕ} (hk : k < ws.length) :
    |centreSeq E₀ ws (k + 1)| = |(|centreSeq E₀ ws k| - (ws[k] : ℤ))| := by
  unfold centreSeq
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, step_abs]

/-- The bound for a whole list of weights (paper Lemma A (§6.1); pseudocode `CENTRE-RULE`):
`|E_K| ≤ max (|E₀| - Σ_j w_j) (max_j w_j)`. -/
theorem centre_fold_bound :
    ∀ (ws : List ℕ) (E : ℤ),
      |ws.foldl centreStep E| ≤ max (|E| - (ws.sum : ℤ)) (listMax ws : ℤ)
  | [], E => by simp [listMax]
  | w :: ws, E => by
    rw [List.foldl_cons]
    refine (centre_fold_bound ws _).trans ?_
    rw [step_abs]
    have hS : (0 : ℤ) ≤ ws.sum := Int.natCast_nonneg _
    have hE : (0 : ℤ) ≤ |E| := abs_nonneg E
    have hmax : listMax (w :: ws) = max w (listMax ws) := rfl
    rw [hmax, List.sum_cons]
    push_cast
    refine max_le ?_ (le_max_of_le_right (le_max_right _ _))
    rcases le_total (w : ℤ) |E| with h | h
    · rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ |E| - w)]
      exact le_max_of_le_left (by linarith)
    · rw [abs_of_nonpos (by linarith : |E| - (w : ℤ) ≤ 0)]
      exact le_max_of_le_right (le_max_of_le_left (by linarith))

/-- The centre rule (paper Lemma A (§6.1); pseudocode `CENTRE-RULE`): for every `k`,
`|E_k| ≤ max (|E₀| - Σ_{j ≤ k} w_j) (max_{j ≤ k} w_j)`, with the maximum of the empty list
equal to `0`. -/
theorem centre_rule_bound (E₀ : ℤ) (ws : List ℕ) (k : ℕ) :
    |centreSeq E₀ ws k| ≤
      max (|E₀| - ((ws.take k).sum : ℤ)) (listMax (ws.take k) : ℤ) :=
  centre_fold_bound (ws.take k) E₀

/-- Corollary of paper Lemma A (§6.1), doubled form (pseudocode `CENTRE-RULE`): if
`|E₀| ≤ S_H + w*`, with `S_H = Σ_j w_j` and `w* = max_j w_j`, then the descent ends with
`|E_K| ≤ w*`. -/
theorem centre_rule_corollary (E₀ : ℤ) (ws : List ℕ)
    (h : |E₀| ≤ (ws.sum : ℤ) + (listMax ws : ℤ)) :
    |ws.foldl centreStep E₀| ≤ listMax ws :=
  (centre_fold_bound ws E₀).trans (max_le (by linarith) le_rfl)

end ArcsAlgo
