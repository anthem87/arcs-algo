module

public import ArcsAlgo.Uniform.Riemann
public import ArcsAlgo.LocalLimit.Tails
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false

/-!
# Gaussian sums over a lattice segment

`gauss_sum`: for `a < 0 < a + N`,
`|Σ_{i=0}^N e^{−α(a+i)²} − √(π/α)| ≤ 2 + e^{−αa²}/(2α|a|) + e^{−α(a+N)²}/(2α(a+N))`.
-/

open Finset MeasureTheory intervalIntegral Set

@[expose] public section

namespace ArcsAlgo.LLT

theorem gauss_integrableOn {α : ℝ} (hα : 0 < α) (S : Set ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-α * y ^ 2)) S :=
  (integrable_exp_neg_mul_sq hα).integrableOn

/-- **A Gaussian sum over a lattice segment**: for `a ≤ 0 ≤ a + N`, with `d₁ = −a`, `d₂ = a + N`,
`|Σ_{i=0}^N e^{−α(a+i)²} − √(π/α)| ≤ 2 + e^{−αd₁²}/(2αd₁) + e^{−αd₂²}/(2αd₂)`. -/
theorem gauss_sum {α : ℝ} (hα : 0 < α) (a : ℝ) (N : ℕ) (ha : a < 0) (haN : 0 < a + N) :
    |∑ i ∈ range (N + 1), Real.exp (-α * (a + i) ^ 2) - √(Real.pi / α)| ≤
      2 + Real.exp (-α * (-a) ^ 2) / (2 * α * (-a)) +
        Real.exp (-α * (a + N) ^ 2) / (2 * α * (a + N)) := by
  set f : ℝ → ℝ := fun y => Real.exp (-α * y ^ 2)
  have hf : Continuous f := by fun_prop
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  have hf1 : ∀ y, f y ≤ 1 := fun y => Real.exp_le_one_iff.mpr (by
    have := sq_nonneg y; nlinarith)
  have hmono : MonotoneOn f (Iic 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have : y ^ 2 ≤ x ^ 2 := by nlinarith [mem_Iic.mp hx, mem_Iic.mp hy]
    nlinarith
  have hanti : AntitoneOn f (Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have : x ^ 2 ≤ y ^ 2 := by nlinarith [mem_Ici.mp hx, mem_Ici.mp hy]
    nlinarith
  have hR := sum_unimodal hf hf0 hf1 hmono hanti a N ha.le haN.le
  have htot : ∫ y, f y = √(Real.pi / α) := integral_gaussian α
  have hsplit : ∫ y, f y = (∫ y in Iic a, f y) + (∫ y in a..a + N, f y) + ∫ y in Ioi (a + N), f y := by
    have e1 := integral_Iic_add_Ioi (f := f) (b := a + N) (μ := volume)
      (gauss_integrableOn hα _) (gauss_integrableOn hα _)
    have e2 := integral_Iic_sub_Iic (f := f) (a := a) (b := a + N) (μ := volume)
      (gauss_integrableOn hα _) (gauss_integrableOn hα _)
    linarith
  have hleft : ∫ y in Iic a, f y ≤ Real.exp (-α * (-a) ^ 2) / (2 * α * (-a)) := by
    have : ∫ y in Iic a, f y = ∫ y in Ioi (-a), f y := by
      have h := integral_comp_neg_Ioi (-a) f
      rw [neg_neg] at h
      rw [← h]; simp [f]
    rw [this]; exact integral_Ioi_exp_le hα (by linarith)
  have hright : ∫ y in Ioi (a + N), f y ≤ Real.exp (-α * (a + N) ^ 2) / (2 * α * (a + N)) :=
    integral_Ioi_exp_le hα haN
  have hl0 : 0 ≤ ∫ y in Iic a, f y := setIntegral_nonneg measurableSet_Iic fun y _ => hf0 y
  have hr0 : 0 ≤ ∫ y in Ioi (a + N), f y := setIntegral_nonneg measurableSet_Ioi fun y _ => hf0 y
  rw [← htot, hsplit]
  rw [abs_le] at hR ⊢
  constructor <;> linarith [hR.1, hR.2]

end ArcsAlgo.LLT
