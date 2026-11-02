module

public import ArcsAlgo.Dense
public import ArcsAlgo.Checker
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false

/-!
# Corollary C′ (via Bringmann–Wellnitz) (paper §6.5)

`corC'`: for a `C_δ`-dense multiset `X` (`BWDense`, [BW, Def. 3.1]) and
`(4 + 2C_g)μ_X max X Σ_X/n² ≤ t ≤ Σ_X/2`, `t` is a subset sum iff `r_{d′}(t mod d′) > 0` for
every `d′ ≤ D = ⌊4μ_XΣ_X/n²⌋`. Necessity is clear; sufficiency is [BW, Theorems 4.1, 4.3].
`corC'_compl`: for `t > Σ_X/2`, through complements (`isSubsetSum_compl`, `rD_compl_pos`).

**Hypothesis.** The Bringmann–Wellnitz structure theorem (`BWThm`, cited [BW, SODA 2021]). A
`Prop`, never an axiom.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo

/-- `r_d(c)`: the number of subsets with sum `≡ c (mod d)` (the exact class counts read from the
arcs `a/d`). -/
def rD (X : List ℕ) (d c : ℕ) : ℕ :=
  (univ.filter fun s : Finset (Fin X.length) => (∑ i ∈ s, X.get i) % d = c % d).card

theorem rD_pos_iff (X : List ℕ) (d c : ℕ) :
    0 < rD X d c ↔ ∃ T, IsSubsetSum X T ∧ T % d = c % d := by
  unfold rD
  rw [card_pos]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨_, ⟨s, rfl⟩, (mem_filter.mp hs).2⟩
  · rintro ⟨T, ⟨s, rfl⟩, h⟩; exact ⟨s, mem_filter.mpr ⟨mem_univ _, h⟩⟩

theorem sum_get (X : List ℕ) : ∑ i : Fin X.length, X.get i = X.sum := by
  have := Fin.sum_univ_getElem X
  simpa using this

/-- Complements: `T` is a subset sum iff `Σ_X − T` is. -/
theorem isSubsetSum_compl {X : List ℕ} {T : ℕ} (hT : T ≤ X.sum) :
    IsSubsetSum X T ↔ IsSubsetSum X (X.sum - T) := by
  have key : ∀ s : Finset (Fin X.length), ∑ i ∈ sᶜ, X.get i = X.sum - ∑ i ∈ s, X.get i := by
    intro s
    have := sum_add_sum_compl s fun i => X.get i
    rw [sum_get] at this; omega
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨sᶜ, key s⟩
  · rintro ⟨s, hs⟩; refine ⟨sᶜ, ?_⟩; rw [key, hs]; omega

/-- Complements for the class counts: `r_d(c) > 0` iff `r_d(Σ_X − c) > 0`. -/
theorem rD_compl_pos (X : List ℕ) (d : ℕ) {c : ℕ} (hc : c ≤ X.sum) :
    0 < rD X d c ↔ 0 < rD X d (X.sum - c) := by
  rw [rD_pos_iff, rD_pos_iff]
  have hmod : ∀ T, T ≤ X.sum → (T % d = c % d ↔ (X.sum - T) % d = (X.sum - c) % d) := by
    intro T hT
    constructor
    · intro h
      have h' : Nat.ModEq d (X.sum - T + T) (X.sum - c + T) := by
        rw [show X.sum - T + T = X.sum - c + c by omega]; exact Nat.ModEq.add_left _ (Nat.ModEq.symm h)
      exact Nat.ModEq.add_right_cancel' T h'
    · intro h
      have h' : Nat.ModEq d (X.sum - c + c) (X.sum - c + T) := by
        rw [show X.sum - c + c = X.sum - T + T by omega]; exact Nat.ModEq.add_right T h
      exact Nat.ModEq.symm (Nat.ModEq.add_left_cancel' (X.sum - c) h')
  constructor
  · rintro ⟨T, hT, h⟩
    have hTle : T ≤ X.sum := by obtain ⟨s, rfl⟩ := hT; rw [← sum_get]
                                exact sum_le_sum_of_subset (subset_univ _)
    exact ⟨X.sum - T, (isSubsetSum_compl hTle).mp hT, (hmod T hTle).mp h⟩
  · rintro ⟨T, hT, h⟩
    have hTle : T ≤ X.sum := by obtain ⟨s, rfl⟩ := hT; rw [← sum_get]
                                exact sum_le_sum_of_subset (subset_univ _)
    refine ⟨X.sum - T, (isSubsetSum_compl hTle).mp hT, ?_⟩
    have := (hmod (X.sum - T) (Nat.sub_le _ _)).mpr
    rw [Nat.sub_sub_self hTle] at this
    exact this h

/-- `C_δ = 1 699 200 log(2n) log²(2μ_X)`. -/
noncomputable def Cdelta (n μ : ℕ) : ℝ := 1699200 * log (2 * n) * log (2 * μ) ^ 2

/-- `C_g = 169 920 log(2μ_X)`. -/
noncomputable def Cg (μ : ℕ) : ℝ := 169920 * log (2 * μ)

/-- `C_δ`-density [BW, Def. 3.1]: `n² ≥ C_δ μ_X max X`. -/
def BWDense (X : List ℕ) : Prop :=
  Cdelta X.length (maxMult X) * maxMult X * maxW X ≤ (X.length : ℝ) ^ 2

/-- **The Bringmann–Wellnitz structure theorem** [BW: K. Bringmann, P. Wellnitz, *On Near-Linear-Time
Algorithms for Dense Subset Sum*, SODA 2021, Theorems 4.1 and 4.3]: for a `C_δ`-dense multiset `X`
and `(4 + 2C_g) μ_X max X Σ_X/n² ≤ t ≤ Σ_X/2` there is `d ≤ 4μ_XΣ_X/n²` with
`t ∈ 𝒮_X ⟺ t mod d ∈ 𝒮_X mod d`. An explicit hypothesis, never an axiom. -/
def BWThm : Prop :=
  ∀ (X : List ℕ) (t : ℕ), 1 ≤ X.length → BWDense X →
    (4 + 2 * Cg (maxMult X)) * maxMult X * maxW X * X.sum / (X.length : ℝ) ^ 2 ≤ t →
    (t : ℝ) ≤ X.sum / 2 →
    ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ 4 * maxMult X * X.sum / (X.length : ℝ) ^ 2 ∧
      (IsSubsetSum X t ↔ ∃ T, IsSubsetSum X T ∧ T % d = t % d)

/-- `D = ⌊4μ_XΣ_X/n²⌋`. -/
noncomputable def DBW (X : List ℕ) : ℕ := ⌊4 * maxMult X * X.sum / (X.length : ℝ) ^ 2⌋₊

/-- **Corollary C′ (via Bringmann–Wellnitz)** (paper §6.5), with [BW] as the only (cited)
hypothesis: under `C_δ`-density and `(4 + 2C_g)μ_X max X Σ_X/n² ≤ t ≤ Σ_X/2`, `t` is a subset sum
iff `r_{d′}(t mod d′) > 0` for every `d′ ≤ D`. -/
theorem corC' (hBW : BWThm) {X : List ℕ} {t : ℕ} (hn : 1 ≤ X.length) (hd : BWDense X)
    (h1 : (4 + 2 * Cg (maxMult X)) * maxMult X * maxW X * X.sum / (X.length : ℝ) ^ 2 ≤ t)
    (h2 : (t : ℝ) ≤ X.sum / 2) :
    IsSubsetSum X t ↔ ∀ d' : ℕ, 1 ≤ d' → d' ≤ DBW X → 0 < rD X d' t := by
  constructor
  · intro ht d' _ _
    exact (rD_pos_iff X d' t).mpr ⟨t, ht, rfl⟩
  · intro h
    obtain ⟨d, hd1, hdD, hiff⟩ := hBW X t hn hd h1 h2
    have hdle : d ≤ DBW X := Nat.le_floor hdD
    exact hiff.mpr ((rD_pos_iff X d t).mp (h d hd1 hdle))

/-- **Corollary C′ for `t > Σ_X/2`**, through complements: if `Σ_X − t` satisfies the range
condition, the same decider applies to `t`. -/
theorem corC'_compl (hBW : BWThm) {X : List ℕ} {t : ℕ} (hn : 1 ≤ X.length) (hd : BWDense X)
    (ht : t ≤ X.sum)
    (h1 : (4 + 2 * Cg (maxMult X)) * maxMult X * maxW X * X.sum / (X.length : ℝ) ^ 2 ≤
      ((X.sum - t : ℕ) : ℝ))
    (h2 : ((X.sum - t : ℕ) : ℝ) ≤ X.sum / 2) :
    IsSubsetSum X t ↔ ∀ d' : ℕ, 1 ≤ d' → d' ≤ DBW X → 0 < rD X d' t := by
  rw [isSubsetSum_compl ht, corC' hBW hn hd h1 h2]
  exact forall_congr' fun d' => imp_congr_right fun _ => imp_congr_right fun _ =>
    (rD_compl_pos X d' ht).symm

end ArcsAlgo
