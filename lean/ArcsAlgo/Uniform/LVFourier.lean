module

public import ArcsAlgo.Uniform.FirstId
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# Theorem LV: the Fourier representation of the count (paper §6.6)

When `S_E ≡ u (mod 2)`, `Z(u) = 2^m ∫_{−1/2}^{1/2} cos(πuθ) Π_i cos(πw_iθ) dθ` (`Zc_integral`).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `P_w(θ) = Π_i cos(π w_i θ)`, so that `F(θ) = 2^m e(θS_E/2) P_w(θ)`. -/
noncomputable def Pw (w : Fin m → Fin M) (θ : ℝ) : ℝ := ∏ i, Real.cos (π * (((w i : ℕ) : ℝ) + 1) * θ)

theorem Pw_neg (w : Fin m → Fin M) (θ : ℝ) : Pw w (-θ) = Pw w θ := by
  simp only [Pw, mul_neg, Real.cos_neg]

theorem continuous_Pw (w : Fin m → Fin M) : Continuous (Pw w) := by
  unfold Pw; fun_prop

theorem abs_Pw_le (w : Fin m → Fin M) (θ : ℝ) : |Pw w θ| ≤ 1 := by
  unfold Pw; rw [abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_cos_le_one _

/-- `Π_i 2cos(πw_iθ) = Σ_ε cos(πθ Σ_i ε_i w_i)`. -/
theorem prod_two_cos (w : Fin m → Fin M) (θ : ℝ) :
    2 ^ m * Pw w θ = ∑ ε : Fin m → Bool, Real.cos (π * θ * (Tsg w ε : ℝ)) := by
  have hC : ((2 ^ m * Pw w θ : ℝ) : ℂ) =
      ∑ ε : Fin m → Bool, Complex.exp (Complex.I * (π * θ * (Tsg w ε : ℝ) : ℝ)) := by
    have h1 : ((2 ^ m * Pw w θ : ℝ) : ℂ) = ∏ i : Fin m, ∑ b : Bool,
        Complex.exp (Complex.I * ((sg b : ℝ) * (π * (((w i : ℕ) : ℝ) + 1) * θ) : ℝ)) := by
      unfold Pw
      push_cast
      rw [← Fin.prod_const, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [Fintype.sum_bool]
      simp only [sg, if_true, Bool.false_eq_true, if_false]
      push_cast
      rw [Complex.cos.eq_1]
      ring_nf
    rw [h1, Fintype.prod_sum]
    refine sum_congr rfl fun ε _ => ?_
    rw [← Complex.exp_sum, ← mul_sum]
    congr 2
    unfold Tsg
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  have := congrArg Complex.re hC
  rw [Complex.ofReal_re, Complex.re_sum] at this
  rw [this]
  refine sum_congr rfl fun ε _ => ?_
  rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]

/-- `∫_{−1/2}^{1/2} cos(πnθ) dθ = 1[n = 0]` for even `n`. -/
theorem integral_cos_even (k : ℤ) :
    ∫ θ in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (π * θ * ((2 * k : ℤ) : ℝ)) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; norm_num
  · have hc : (2 * π * k : ℝ) ≠ 0 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    have e : ∀ θ : ℝ, π * θ * ((2 * k : ℤ) : ℝ) = (2 * π * k) * θ := fun θ => by push_cast; ring
    simp only [e]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have h1 : Real.sin (2 * π * k * (1 / 2)) = 0 := by
      rw [show 2 * π * k * (1 / 2) = (k : ℝ) * π by ring]; exact Real.sin_int_mul_pi k
    have h2 : Real.sin (2 * π * k * (-(1 / 2))) = 0 := by
      rw [show 2 * π * k * (-(1 / 2)) = ((-k : ℤ) : ℝ) * π by push_cast; ring]
      exact Real.sin_int_mul_pi _
    rw [h1, h2]; simp

/-- `∫_{−1/2}^{1/2} cos(πTθ)cos(πuθ) dθ = (1[T = u] + 1[T = −u])/2` for `T ≡ u (mod 2)`. -/
theorem integral_cos_cos {T u : ℤ} (h : ∃ a, T + u = 2 * a) :
    ∫ θ in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (π * θ * (T : ℝ)) * Real.cos (π * u * θ) =
      ((if T = u then 1 else 0) + (if T = -u then 1 else 0)) / 2 := by
  obtain ⟨a, ha⟩ := h
  have e : ∀ θ : ℝ, Real.cos (π * θ * (T : ℝ)) * Real.cos (π * u * θ) =
      Real.cos (π * θ * ((2 * (T - a) : ℤ) : ℝ)) / 2 + Real.cos (π * θ * ((2 * a : ℤ) : ℝ)) / 2 := by
    intro θ
    have h1 : ((2 * (T - a) : ℤ) : ℝ) = (T : ℝ) - u := by
      have : (2 * (T - a) : ℤ) = T - u := by omega
      rw [this]; push_cast; ring
    have h2 : ((2 * a : ℤ) : ℝ) = (T : ℝ) + u := by
      have : (2 * a : ℤ) = T + u := by omega
      rw [this]; push_cast; ring
    rw [h1, h2, show π * θ * ((T : ℝ) - u) = π * θ * T - π * u * θ by ring,
      show π * θ * ((T : ℝ) + u) = π * θ * T + π * u * θ by ring, Real.cos_sub, Real.cos_add]
    ring
  simp only [e]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_div, intervalIntegral.integral_div, integral_cos_even, integral_cos_even]
  have c1 : (T - a = 0) ↔ T = u := by omega
  have c2 : (a = 0) ↔ T = -u := by omega
  simp only [c1, c2]; ring

theorem Tsg_not (w : Fin m → Fin M) (ε : Fin m → Bool) : Tsg w (fun i => !ε i) = -Tsg w ε := by
  unfold Tsg; rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : ε i = true <;> simp [sg, h]

theorem Zc_neg (w : Fin m → Fin M) (u : ℤ) : Zc w (-u) = Zc w u := by
  unfold Zc
  refine card_bij (fun ε _ => fun i => !ε i) (fun ε hε => ?_) (fun ε _ ε' _ h => ?_) (fun ε hε => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hε ⊢
    rw [Tsg_not, hε, neg_neg]
  · funext i; have := congrFun h i; simpa using this
  · refine ⟨fun i => !ε i, ?_, by funext i; simp⟩
    simp only [mem_filter, mem_univ, true_and] at hε ⊢
    rw [Tsg_not, hε]

/-- **The Fourier representation of the count** (paper §6.6, proof of Theorem LV): when
`S_E ≡ u (mod 2)`, `Z(u) = 2^m ∫_{−1/2}^{1/2} cos(πuθ) Π_i cos(πw_iθ) dθ`. -/
theorem Zc_integral (w : Fin m → Fin M) (u : ℤ) (h : ∃ a, 2 * a = Sw w + u) :
    (Zc w u : ℝ) = 2 ^ m * ∫ θ in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (π * u * θ) * Pw w θ := by
  obtain ⟨a, ha⟩ := h
  rw [← intervalIntegral.integral_const_mul]
  have e : ∀ θ : ℝ, 2 ^ m * (Real.cos (π * u * θ) * Pw w θ) =
      ∑ ε : Fin m → Bool, Real.cos (π * θ * (Tsg w ε : ℝ)) * Real.cos (π * u * θ) := by
    intro θ
    rw [mul_left_comm, prod_two_cos, mul_sum]
    refine sum_congr rfl fun ε _ => by ring
  simp only [e]
  rw [intervalIntegral.integral_finsetSum (fun ε _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  have hpar : ∀ ε : Fin m → Bool, ∃ b, Tsg w ε + u = 2 * b := by
    intro ε
    refine ⟨a - Sw w + SJ (signEquiv m ε) w, ?_⟩
    have e1 := Sw_eq w (signEquiv m ε)
    have e2 := Tsg_eq w ε
    omega
  simp only [fun ε => integral_cos_cos (hpar ε)]
  rw [← sum_div, sum_add_distrib]
  have z1 : ∑ ε : Fin m → Bool, (if Tsg w ε = u then (1 : ℝ) else 0) = Zc w u := by
    unfold Zc; rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]; simp
  have z2 : ∑ ε : Fin m → Bool, (if Tsg w ε = -u then (1 : ℝ) else 0) = Zc w u := by
    rw [← Zc_neg w u]
    unfold Zc; rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]; simp
  rw [z1, z2]; ring

end ArcsAlgo.LLT
