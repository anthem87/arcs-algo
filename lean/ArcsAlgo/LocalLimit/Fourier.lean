module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.BigOperators.Pi
set_option autoImplicit false

/-!
# Fourier inversion for sums of uniform weights (paper §6.2, proof of Lemma B0′)

`lawS M k v = #{w ∈ {1,…,M}^k : Σ wᵢ = v} / M^k` is `Pr(S_k = v)` for independent uniform
weights. With `φ(θ) = M⁻¹ Σ_{j=1}^M e^{ijθ}`, `lawS_eq_integral` gives
`Pr(S_k = v) = (2π)⁻¹ ∫_{−π}^{π} φ(θ)^k e^{−ivθ} dθ`.
-/

open Real Complex Finset MeasureTheory intervalIntegral

@[expose] public section

namespace ArcsAlgo.LLT

/-- The law of `S_k = w₁ + … + w_k` for independent uniform `w_i ∈ {1, …, M}`:
`Pr(S_k = v) = #{w ∈ {1,…,M}^k : Σ w_i = v} / M^k`. -/
noncomputable def lawS (M k : ℕ) (v : ℤ) : ℝ :=
  ((univ.filter fun w : Fin k → Fin M => ∑ i, ((w i : ℤ) + 1) = v).card : ℝ) / (M : ℝ) ^ k

/-- `∫_{−π}^{π} e^{inθ} dθ = 2π·[n = 0]`. -/
lemma integral_exp_int (n : ℤ) :
    ∫ θ in (-π)..π, cexp (I * n * θ) = if n = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hn
  · subst hn; simp; ring
  · have hc : I * (n : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hn)
    have := integral_exp_mul_complex (a := -π) (b := π) hc
    rw [this]
    have h1 : cexp (I * n * π) = cexp (I * n * (-π : ℝ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨n, ?_⟩; push_cast; ring
    push_cast at h1 ⊢
    rw [h1, sub_self, zero_div]

/-- The characteristic function of a uniform weight, `φ(θ) = M⁻¹ Σ_{j=1}^M e^{ijθ}`. -/
noncomputable def phiW (M : ℕ) (θ : ℝ) : ℂ :=
  (1 / (M : ℂ)) * ∑ j : Fin M, cexp (I * (((j : ℕ) : ℂ) + 1) * θ)

lemma phiW_pow (M k : ℕ) (θ : ℝ) :
    phiW M θ ^ k = (1 / (M : ℂ)) ^ k *
      ∑ w : Fin k → Fin M, cexp (I * ((∑ i, (((w i : ℕ) : ℤ) + 1) : ℤ) : ℂ) * θ) := by
  rw [phiW, mul_pow, ← Fin.prod_const k (∑ j : Fin M, _), Finset.prod_univ_sum]
  congr 1
  apply sum_congr rfl; intro w _
  rw [← Complex.exp_sum]; congr 1
  push_cast; rw [Finset.mul_sum, Finset.sum_mul]

/-- Fourier inversion: `Pr(S_k = v) = (2π)⁻¹ ∫_{−π}^{π} φ(θ)^k e^{−ivθ} dθ`. -/
theorem lawS_eq_integral {M : ℕ} (hM : 0 < M) (k : ℕ) (v : ℤ) :
    ((lawS M k v : ℝ) : ℂ) = (1 / (2 * π)) * ∫ θ in (-π)..π, phiW M θ ^ k * cexp (-(I * v * θ)) := by
  have hint : ∀ w : Fin k → Fin M, IntervalIntegrable
      (fun θ : ℝ => cexp (I * ((∑ i, (((w i : ℕ) : ℤ) + 1) - v : ℤ) : ℂ) * θ)) volume (-π) π :=
    fun w => by apply Continuous.intervalIntegrable; fun_prop
  have e : ∀ θ : ℝ, phiW M θ ^ k * cexp (-(I * v * θ)) = (1 / (M : ℂ)) ^ k *
      ∑ w : Fin k → Fin M, cexp (I * ((∑ i, (((w i : ℕ) : ℤ) + 1) - v : ℤ) : ℂ) * θ) := by
    intro θ
    rw [phiW_pow, mul_assoc, Finset.sum_mul]; congr 1
    apply sum_congr rfl; intro w _
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun w _ => hint w)]
  simp_rw [integral_exp_int, sub_eq_zero]
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, lawS]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  simp only [nsmul_eq_mul]
  field_simp
  rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hM'), mul_one]

end ArcsAlgo.LLT
