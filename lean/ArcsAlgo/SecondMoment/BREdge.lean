module

public import ArcsAlgo.SecondMoment.BR22
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
set_option autoImplicit false

/-!
# [BR, Theorem 22.1] at every order, as one explicit hypothesis

The cumulants `χ_α` (`cumul`), the cumulant forms as operators `χ_ν(−D)` (`chiOp`) and the
Edgeworth polynomials `P_r(−φ_V : {χ_ν}) = P̃_r(−D)φ_V` (`edgeP`) are defined as in [BR, §6–7];
`BR22Edge` is the local expansion of [BR, Theorem 22.1] for bounded lattice vectors, at every
order `s`. It is a cited classical theorem, used as an explicit hypothesis, never an `axiom`.
`edgeP_zero`: `P_0 = φ_V`; `BR22_of_edge`: the leading-term statement `BR22` is the case `s = 2`.

[BR] R. N. Bhattacharya, R. Ranga Rao, *Normal Approximation and Asymptotic Expansions*, Wiley
(1976); reprinted SIAM Classics in Applied Mathematics 64 (2010).
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

/-- The partial derivative `∂_j f`. -/
noncomputable def pD {d : ℕ} (j : Fin d) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (Pi.single j 1)

/-- `D^α f = ∂_0^{α_0} ⋯ ∂_{d−1}^{α_{d−1}} f`. -/
noncomputable def Dα {d : ℕ} (α : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  (List.finRange d).foldr (fun j g => (pD j)^[α j] g) f

/-- The cumulant generating function `log E e^{⟨t, X⟩}` of `X = ξ(ω)`, `Pr(ω = a) = p a`. -/
noncomputable def cgf {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ)
    (t : Fin d → ℝ) : ℝ :=
  Real.log (∑ a, p a * Real.exp (∑ j, t j * (ξ a j : ℝ)))

/-- The cumulant `χ_α = D^α log E e^{⟨t, X⟩} |_{t=0}` [BR, §6]. For a bounded vector this is
`(−i)^{|α|} D^α log E e^{i⟨t, X⟩} |_{t=0}`, the book's definition. -/
noncomputable def cumul {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ)
    (α : Fin d → ℕ) : ℝ :=
  Dα α (cgf p ξ) 0

/-- `α! = α_0! ⋯ α_{d−1}!`. -/
def mfact {d : ℕ} (α : Fin d → ℕ) : ℕ := ∏ j, (α j).factorial

/-- `χ_ν(−D)`, where `χ_ν(z) = ν! Σ_{|α| = ν} χ_α z^α / α!` is the `ν`-th cumulant form [BR, (7.3)],
as a differential operator: `(χ_ν(−D) f)(x) = ν! Σ_{|α| = ν} χ_α (−1)^ν (D^α f)(x) / α!`. -/
noncomputable def chiOp {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ) (ν : ℕ)
    (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => ∑ α ∈ Finset.Nat.antidiagonalTuple d ν,
    ((ν.factorial : ℝ) / mfact α) * cumul p ξ α * (-1) ^ ν * Dα α f x

/-- **The Edgeworth polynomials** `P_r(−φ_V : {χ_ν}) = P̃_r(−D) φ_V` [BR, (7.3), (7.11)], with
`P̃_r(z) = Σ_{k=1}^{r} (1/k!) Σ_{j_1 + ⋯ + j_k = r, j_i ≥ 1} Π_i χ_{j_i+2}(z)/(j_i+2)!`: the sum runs over
the compositions `(j_1, …, j_k)` of `r`, and `P̃_0 = 1`. The product of the cumulant forms in `−D` is
the composition of the commuting operators `χ_{j_i+2}(−D)`. -/
noncomputable def edgeP {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ) (r : ℕ) :
    (Fin d → ℝ) → ℝ :=
  fun x => ∑ c : Composition r, (1 / (c.length.factorial : ℝ)) *
    (c.blocks.foldr (fun j g => fun y => (1 / ((j + 2).factorial : ℝ)) * chiOp p ξ (j + 2) g y)
      (gaussDens (vcov p ξ))) x

/-- **The local expansion for sums of independent lattice vectors** [BR, Theorem 22.1], at every
order, for bounded vectors.

R. N. Bhattacharya, R. Ranga Rao, *Normal Approximation and Asymptotic Expansions*, Wiley (1976),
§22, Theorem 22.1. Let `X₁, X₂, …` be independent copies of a random vector `X` of `ℤ^d` with
finite support, covariance `V` non-singular, mean `μ`, cumulants `χ_ν`, and minimal lattice `L`
(`X ∈ x₀ + L` almost surely). Then for every `s ≥ 2`, uniformly in `x ∈ n x₀ + L`,
`n^{d/2} Pr(X₁ + ⋯ + X_n = x) = det(L) Σ_{r=0}^{s−2} n^{−r/2} P_r(−φ_V : {χ_ν})((x − nμ)/√n) + O(n^{−(s−1)/2})`,
where `det(L)` is the index of `L` in `ℤ^d`. Theorem 22.1 gives the error `o(n^{−(s−2)/2})` under a
finite `s`-th moment; a bounded vector has all moments, so applying it at order `s + 1` and
bounding the term `r = s − 1` (a polynomial times `φ_V`) gives `O(n^{−(s−1)/2})`. This is a cited
classical theorem, used as an explicit hypothesis. -/
def BR22Edge : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (d : ℕ) (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ),
    (∀ a, 0 ≤ p a) → ∑ a, p a = 1 → (vcov p ξ).PosDef → ∀ a₀, 0 < p a₀ → ∀ s : ℕ, 2 ≤ s →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x : Fin d → ℤ, x - n • ξ a₀ ∈ minLat p ξ →
      |√(n : ℝ) ^ d * lawPow p ξ n x - ((minLat p ξ).index : ℝ) * ∑ r ∈ range (s - 1),
          edgeP p ξ r (fun j => ((x j : ℝ) - n * vmean p ξ j) / √(n : ℝ)) / √(n : ℝ) ^ r|
        ≤ C / √(n : ℝ) ^ (s - 1)

/-- `P_0(−φ_V) = φ_V`. -/
theorem edgeP_zero {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ) :
    edgeP p ξ 0 = gaussDens (vcov p ξ) := by
  funext x
  unfold edgeP
  have : (Finset.univ : Finset (Composition 0)) = {Composition.ones 0} := by
    ext c; simp only [mem_univ, mem_singleton, true_iff]
    apply Composition.ext
    have h1 := c.length_le
    have h2 : c.blocks.length = 0 := by unfold Composition.length at h1; omega
    rw [List.length_eq_zero_iff] at h2
    rw [h2]; rfl
  rw [this, sum_singleton]
  simp [Composition.ones, Composition.length]

/-- The leading-term statement `BR22` is the case `s = 2` of `BR22Edge`. -/
theorem BR22_of_edge (h : BR22Edge) : BR22 := by
  intro Ω _ d p ξ hp hs hV a₀ ha₀
  obtain ⟨C, hC⟩ := h Ω d p ξ hp hs hV a₀ ha₀ 2 le_rfl
  refine ⟨C, fun n hn x hx => ?_⟩
  have h1 := hC n hn x hx
  simp only [show (2 : ℕ) - 1 = 1 from rfl, range_one, sum_singleton, edgeP_zero, pow_zero,
    div_one, pow_one] at h1
  have hn0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hd : (0 : ℝ) < √(n : ℝ) ^ d := pow_pos hn0 d
  rw [show lawPow p ξ n x - ((minLat p ξ).index : ℝ) *
      gaussDens (vcov p ξ) (fun j => ((x j : ℝ) - n * vmean p ξ j) / √(n : ℝ)) / √(n : ℝ) ^ d =
      (√(n : ℝ) ^ d * lawPow p ξ n x - ((minLat p ξ).index : ℝ) *
      gaussDens (vcov p ξ) (fun j => ((x j : ℝ) - n * vmean p ξ j) / √(n : ℝ))) / √(n : ℝ) ^ d by
    field_simp]
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, pow_succ, ← mul_comm (√(n : ℝ)), ← div_div,
    div_mul_cancel₀ _ hd.ne']
  exact h1

end ArcsAlgo.LLT
