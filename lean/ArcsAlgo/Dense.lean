module

public import ArcsAlgo.Chain
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
set_option autoImplicit false

/-!
# Dense instances: the constructor (paper §6.5, Corollary C″)

On a `C_δ`-dense multiset `X` of `n` weights ([BW, Def. 3.1]: `n² ≥ C_δ μ_X max X`, with `μ_X`
the largest multiplicity), the sums are polynomially bounded, `Σ_X ≤ n·max X ≤ n³/(C_δ μ_X)`,
and the table of reachable sums over `[0, Σ_X]` with backtracking constructs a solution.
-/

@[expose] public section

namespace ArcsAlgo

/-- The largest weight of a list (`0` for the empty list). -/
def maxW (X : List ℕ) : ℕ := X.foldr max 0

/-- The largest multiplicity `μ_X` of a multiset of weights. -/
def maxMult (X : List ℕ) : ℕ := (X.map X.count).foldr max 0

theorem le_maxW {X : List ℕ} {x : ℕ} (hx : x ∈ X) : x ≤ maxW X := by
  induction X with
  | nil => simp at hx
  | cons a X ih =>
    simp only [List.mem_cons] at hx
    simp only [maxW, List.foldr_cons] at ih ⊢
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem sum_le_length_mul_maxW (X : List ℕ) : X.sum ≤ X.length * maxW X := by
  have := List.sum_le_length_nsmul X (maxW X) fun x hx => le_maxW hx
  simpa using this

/-- **Corollary C″, size of the table** (paper §6.5): if `X` is `C_δ`-dense,
`n² ≥ C_δ μ_X max X` with `C_δ μ_X > 0`, then `Σ_X ≤ n·max X ≤ n³/(C_δ μ_X)`. -/
theorem dense_sum_bound (X : List ℕ) (Cδ : ℝ) (hpos : 0 < Cδ * maxMult X)
    (hdense : Cδ * maxMult X * maxW X ≤ (X.length : ℝ) ^ 2) :
    (X.sum : ℝ) ≤ X.length * maxW X ∧
      (X.length : ℝ) * maxW X ≤ (X.length : ℝ) ^ 3 / (Cδ * maxMult X) := by
  refine ⟨by exact_mod_cast sum_le_length_mul_maxW X, ?_⟩
  rw [le_div_iff₀ hpos]
  have hn : (0 : ℝ) ≤ X.length := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hdense hn]

/-- Every forward domain lies in `[0, Σ_X]`, so the table of the constructor has at most
`(n + 1)(Σ_X + 1)` cells. -/
theorem fwd_subset_range (X : List ℕ) (i : ℕ) : fwd X i ⊆ Finset.range (X.sum + 1) := by
  intro v hv
  rw [fwd, mem_reach] at hv
  have h1 := le_sum_of_isSubsetSum hv
  have h2 : (X.take i).sum ≤ X.sum := (List.take_sublist i X).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [Finset.mem_range]; omega

/-- **Corollary C″ (constructor on dense instances)** (paper §6.5): if `t` is a subset sum
(which Corollary C′ decides on dense instances), the table of reachable sums with backtracking
returns a sub-multiset of `X` with sum `t`; the table has at most `(n + 1)(Σ_X + 1)` cells, and
`Σ_X ≤ n³/(C_δ μ_X)` by `dense_sum_bound`. -/
theorem dense_constructor (X : List ℕ) (t : ℕ) (ht : IsSubsetSum X t) :
    (greedy X.reverse t).Sublist X ∧ (greedy X.reverse t).sum = t ∧
      ∀ i, (fwd X i).card ≤ X.sum + 1 := by
  obtain ⟨h1, h2⟩ := greedy_spec X t ((mem_reach X t).2 ht)
  refine ⟨h1, h2, fun i => ?_⟩
  simpa using Finset.card_le_card (fwd_subset_range X i)

end ArcsAlgo
