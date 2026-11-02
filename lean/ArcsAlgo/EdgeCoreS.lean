module

public import ArcsAlgo.EdgeCoreV
set_option autoImplicit false

/-!
# The core with a large tilt (paper §3.5, Remark (the formula of Proposition C))

* `tilt_le`: completing the square, `−yσ − s²σ²/2 ≤ y²/(2(s² − s₁²)) − s₁²σ²/2` for `s₁ < s`.
* `core_intS`: the core integral with the weight `A + B(−iσ)` differs from `A·mainEC + B·mainEC′` by
  `(2π)^{−1}(E(aE_I(s₁) + bE_I′(s₁)) + e^{−s²τ²/8}(aT_I′ + bT_I″))`, `E = e^{(Im κ₁)²/(2(s² − s₁²))}`, for any
  `0 < s₁ < s`, uniformly in `T`. Only `|Im κ₁| ≤ s²τ/4` is needed, not `|Im κ₁|τ ≤ 1`.

No hypothesis.
-/

open Finset Complex MeasureTheory Nat
open scoped Real

@[expose] public section

namespace ArcsAlgo.Edge

/-- Completing the square: `−yσ − s²σ²/2 ≤ y²/(2(s² − s₁²)) − s₁²σ²/2` for `s₁ < s`. -/
theorem tilt_le {y s s1 : ℝ} (h : s1 ^ 2 < s ^ 2) (σ : ℝ) :
    -(y * σ) - s ^ 2 * σ ^ 2 / 2 ≤ y ^ 2 / (2 * (s ^ 2 - s1 ^ 2)) + -(s1 ^ 2 * σ ^ 2) / 2 := by
  have hd : 0 < s ^ 2 - s1 ^ 2 := by linarith
  have key : 0 ≤ ((s ^ 2 - s1 ^ 2) * σ + y) ^ 2 / (2 * (s ^ 2 - s1 ^ 2)) := by positivity
  have e : ((s ^ 2 - s1 ^ 2) * σ + y) ^ 2 / (2 * (s ^ 2 - s1 ^ 2)) =
      (s ^ 2 - s1 ^ 2) * σ ^ 2 / 2 + y * σ + y ^ 2 / (2 * (s ^ 2 - s1 ^ 2)) := by
    field_simp; ring
  rw [e] at key; nlinarith

set_option maxHeartbeats 8000000 in
/-- **The core with a large tilt, integrated**: let `f(σ) = exp(Σ_{n≤5} κ_n(iσ)^n/n! + R(σ))` on `|σ| ≤ τ`
with `|R| ≤ ρσ⁶`, `κ₀ = 0`, `κ₁ = k₁ ∈ ℂ`, `κ₂ = s²` real, and let the weight be `A + B(−iσ)` with
`|A| ≤ a`, `|B| ≤ b`. For any `0 < s₁ < s`, with `E = e^{(Im k₁)²/(2(s² − s₁²))}`, uniformly in `T`,
`|(2π)^{−1}∫_{−τ}^{τ} (A + B(−iσ)) f(σ) e^{−iTσ} − (A·mainEC(T) + B·mainEC′(T))|
  ≤ (2π)^{−1}(E(a E_I(s₁) + b E_I′(s₁)) + e^{−s²τ²/8}(a T_I′ + b T_I″))`.
No bound on `|Im k₁|τ` is needed; only `|Im k₁| ≤ s²τ/4`. -/
theorem core_intS (f : ℝ → ℂ) (hf : Continuous f) (κ : ℕ → ℂ) {k1 : ℂ} {s s1 ρ τ a b : ℝ} (A B : ℂ)
    (hs : 0 < s) (hs1 : 0 < s1) (hs1s : s1 < s)
    (hτ0 : 0 < τ) (hρ0 : 0 ≤ ρ) (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) (hk0 : κ 0 = 0) (h1 : κ 1 = k1)
    (h2 : κ 2 = ((s ^ 2 : ℝ) : ℂ))
    (hexp : ∀ σ : ℝ, |σ| ≤ τ → ∃ R : ℂ, ‖R‖ ≤ ρ * σ ^ 6 ∧
      f σ = Complex.exp (∑ n ∈ range 6, κ n * (I * σ) ^ n / (n ! : ℂ) + R))
    (hy : ‖κ 3‖ / 6 * τ ^ 3 + ‖κ 4‖ / 24 * τ ^ 4 + ‖κ 5‖ / 120 * τ ^ 5 + ρ * τ ^ 6 ≤ 1)
    (hyt : |k1.im| ≤ s ^ 2 * τ / 4) (T : ℝ) :
    ‖(1 / (2 * π) : ℂ) * (∫ σ in (-τ)..τ, (A + B * (-(I * σ))) * f σ * Complex.exp (-(I * T * σ))) -
        (A * mainEC k1 s (κ 3) (κ 4) T + B * dmainEC k1 s (κ 3) (κ 4) T)‖ ≤
      1 / (2 * π) * (Real.exp (k1.im ^ 2 / (2 * (s ^ 2 - s1 ^ 2))) *
          (a * EI (‖κ 3‖ / 6) (‖κ 4‖ / 24) (‖κ 5‖ / 120) ρ s1 +
            b * EI1 (‖κ 3‖ / 6) (‖κ 4‖ / 24) (‖κ 5‖ / 120) ρ s1) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (a * TIs (‖κ 3‖ / 6) (‖κ 4‖ / 24) s +
          b * TIs1 (‖κ 3‖ / 6) (‖κ 4‖ / 24) s)) := by
  set κ₃ := κ 3
  set κ₄ := κ 4
  set α3 := ‖κ₃‖ / 6
  set α4 := ‖κ₄‖ / 24
  set α5 := ‖κ 5‖ / 120
  have hα3 : 0 ≤ α3 := by positivity
  have hα4 : 0 ≤ α4 := by positivity
  have hα5 : 0 ≤ α5 := by positivity
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  have hb : 0 ≤ b := (norm_nonneg _).trans hB
  have hss : s1 ^ 2 < s ^ 2 := by nlinarith
  set y := k1.im
  set Ey := Real.exp (y ^ 2 / (2 * (s ^ 2 - s1 ^ 2))) with hEy
  set m : ℝ → ℂ := fun σ => A + B * (-(I * σ)) with hm
  have hnm : ∀ σ : ℝ, ‖m σ‖ ≤ a + b * |σ| := by
    intro σ
    simp only [hm]
    refine (norm_add_le _ _).trans (add_le_add hA ?_)
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  set F : ℝ → ℂ := fun σ => m σ * f σ * Complex.exp (-(I * T * σ)) with hF
  set g : ℝ → ℂ := fun σ => m σ * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) with hg
  have hg_eq : g = fun σ => A * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) +
      B * ((-(I * σ)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)))) := by
    ext σ; simp only [hg, hm]; ring
  have hgi1 := (integrable_edgeIC hs k1 κ₃ κ₄ T).const_mul A
  have hgi2 := (integrable_edgeIC_d hs k1 κ₃ κ₄ T).const_mul B
  have hg_int : Integrable g := by rw [hg_eq]; exact hgi1.add hgi2
  have hmain : (1 / (2 * π) : ℂ) * ∫ σ, g σ = A * mainEC k1 s κ₃ κ₄ T + B * dmainEC k1 s κ₃ κ₄ T := by
    rw [hg_eq, integral_add hgi1 hgi2, integral_const_mul, integral_const_mul]
    have e1 := edge_mainC hs k1 κ₃ κ₄ T
    have e2 := edge_dmainC hs k1 κ₃ κ₄ T
    linear_combination A * e1 + B * e2
  have hF_cont : Continuous F := by rw [hF]; simp only [hm]; fun_prop
  set S := Set.Ioc (-τ) τ
  have hS : MeasurableSet S := measurableSet_Ioc
  have hFS : IntegrableOn F S := (hF_cont.integrableOn_Icc (a := -τ) (b := τ)).mono_set Set.Ioc_subset_Icc_self
  have hint : ∫ σ in (-τ)..τ, (A + B * (-(I * σ))) * f σ * Complex.exp (-(I * T * σ)) = ∫ σ in S, F σ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
  rw [hint, ← hmain, ← integral_add_compl hS hg_int]
  have hsplit : (1 / (2 * π) : ℂ) * (∫ σ in S, F σ) - (1 / (2 * π) : ℂ) * ((∫ σ in S, g σ) + ∫ σ in Sᶜ, g σ) =
      (1 / (2 * π) : ℂ) * ((∫ σ in S, (F σ - g σ)) - ∫ σ in Sᶜ, g σ) := by
    rw [integral_sub hFS hg_int.integrableOn]; ring
  rw [hsplit, norm_mul]
  have h2pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [h2pi]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
  refine add_le_add ?_ ?_
  · -- the core
    set G0 : ℝ → ℝ := fun σ => Real.exp (-(s1 ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|
    set gC : ℝ → ℝ := fun σ => Ey * (a * G0 σ + b * (|σ| * G0 σ))
    have hG0 := integrable_gEb hs1 α3 α4 α5 ρ
    have hG1 := integrable_gEb1 hs1 α3 α4 α5 ρ
    have hgC : Integrable gC := ((hG0.const_mul a).add (hG1.const_mul b)).const_mul Ey
    have hG0nn : ∀ σ, 0 ≤ G0 σ := fun σ => mul_nonneg (Real.exp_pos _).le (by
      rw [Eb_eq]; exact sum_nonneg fun i _ => mul_nonneg (ebC_nonneg hα3 hα4 hα5 hρ0 i) (by positivity))
    have hpt : ∀ᵐ σ ∂(volume.restrict S), ‖F σ - g σ‖ ≤ gC σ := by
      filter_upwards [ae_restrict_mem hS] with σ hσ
      have hσ' : |σ| ≤ τ := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
      obtain ⟨R, hR, hfσ⟩ := hexp σ hσ'
      have hyσ : α3 * |σ| ^ 3 + α4 * σ ^ 4 + α5 * |σ| ^ 5 + ρ * σ ^ 6 ≤ 1 := by
        have e4 : σ ^ 4 = |σ| ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
        have e6 : σ ^ 6 = |σ| ^ 6 := by rw [pow_abs, abs_of_nonneg (by positivity)]
        rw [e4, e6]
        have p3 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 3
        have p4 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 4
        have p5 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 5
        have p6 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 6
        have : α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α5 * |σ| ^ 5 + ρ * |σ| ^ 6 ≤
            α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 := by gcongr
        linarith
      have hc := core_ptC hρ0 hk0 h1 h2 hR hyσ
      rw [← hfσ] at hc
      have hX : ‖Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)‖ ≤
          Ey * Real.exp (-(s1 ^ 2 * σ ^ 2) / 2) := by
        rw [norm_gaussXC, hEy, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (tilt_le hss σ)
      simp only [hF, hg]
      have e : m σ * f σ * Complex.exp (-(I * T * σ)) - m σ * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) =
          m σ * (f σ - edgeIC k1 s κ₃ κ₄ σ) * Complex.exp (-(I * T * σ)) := by ring
      rw [e, norm_mul, norm_mul, norm_cexp_IT, mul_one]
      have hEb0 : 0 ≤ Eb α3 α4 α5 ρ |σ| := by
        rw [Eb_eq]; exact sum_nonneg fun i _ => mul_nonneg (ebC_nonneg hα3 hα4 hα5 hρ0 i) (by positivity)
      calc ‖m σ‖ * ‖f σ - edgeIC k1 s κ₃ κ₄ σ‖
          ≤ (a + b * |σ|) * (Ey * Real.exp (-(s1 ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|) :=
            mul_le_mul (hnm σ) (hc.trans (mul_le_mul_of_nonneg_right hX hEb0)) (norm_nonneg _) (by positivity)
        _ = gC σ := by simp only [gC, G0]; ring
    calc ‖∫ σ in S, (F σ - g σ)‖ ≤ ∫ σ in S, gC σ := norm_integral_le_of_norm_le hgC.integrableOn hpt
      _ ≤ ∫ σ, gC σ := setIntegral_le_integral hgC (Filter.Eventually.of_forall fun σ => by
          simp only [gC]; have := hG0nn σ; positivity)
      _ = Ey * (a * EI α3 α4 α5 ρ s1 + b * EI1 α3 α4 α5 ρ s1) := by
          simp only [gC]
          rw [integral_const_mul, integral_add (hG0.const_mul _) (hG1.const_mul _), integral_const_mul,
            integral_const_mul, integral_gEb hs1, ← integral_gEb1 hs1 α3 α4 α5 ρ]
  · -- the tail of the main term
    set s' := s / 2 with hs'
    have hs'0 : 0 < s' := by positivity
    have hs'2 : s' ^ 2 = s ^ 2 / 4 := by rw [hs']; ring
    obtain ⟨hi0, hv0⟩ := integral_tailpoly hs'0 α3 α4 0
    obtain ⟨hi1, hv1⟩ := integral_tailpoly hs'0 α3 α4 1
    set P : ℝ → ℝ := fun σ => Real.exp (-(s' ^ 2 * σ ^ 2) / 2) * (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)
    set h2 : ℝ → ℝ := fun σ => a * (|σ| ^ 0 * P σ) + b * (|σ| ^ 1 * P σ)
    have hh2 : Integrable h2 := (hi0.const_mul a).add (hi1.const_mul b)
    have hpt : ∀ᵐ σ ∂(volume.restrict Sᶜ), ‖g σ‖ ≤ Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ := by
      filter_upwards [ae_restrict_mem hS.compl] with σ hσ
      have hστ : τ ≤ |σ| := by
        simp only [S, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hσ
        rcases hσ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp only [hg]
      rw [norm_mul, norm_mul, norm_cexp_IT, mul_one]
      unfold edgeIC
      rw [norm_mul, norm_gaussXC]
      have hIσ : ∀ k : ℕ, ‖(I * (σ : ℂ)) ^ k‖ = |σ| ^ k := by
        intro k; rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hpoly : ‖1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ ≤
          1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6 := by
        have n3 : ‖κ₃ * (I * σ) ^ 3 / 6‖ = α3 * |σ| ^ 3 := by
          rw [norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
        have n4 : ‖κ₄ * (I * σ) ^ 4 / 24‖ = α4 * |σ| ^ 4 := by
          rw [norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
        have n6 : ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ = α3 ^ 2 / 2 * |σ| ^ 6 := by
          rw [norm_div, norm_mul, norm_pow, hIσ, Complex.norm_ofNat]; ring
        calc _ ≤ ‖(1 : ℂ) + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24‖ + ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ :=
              norm_add_le _ _
          _ ≤ ‖(1 : ℂ)‖ + ‖κ₃ * (I * σ) ^ 3 / 6‖ + ‖κ₄ * (I * σ) ^ 4 / 24‖ + ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ := by
              gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
          _ = _ := by rw [norm_one, n3, n4, n6]
      have hexp : Real.exp (-(y * σ) - s ^ 2 * σ ^ 2 / 2) ≤
          Real.exp (-(s ^ 2 * τ ^ 2) / 8) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) := by
        rw [← Real.exp_add, hs'2]
        apply Real.exp_le_exp.mpr
        have hyσ : -(y * σ) ≤ s ^ 2 * τ / 4 * |σ| := by
          have := neg_abs_le (y * σ); rw [abs_mul] at this
          have := mul_le_mul_of_nonneg_right hyt (abs_nonneg σ); linarith
        have h1 : τ * |σ| ≤ σ ^ 2 := by
          rw [← sq_abs σ, sq]; exact mul_le_mul_of_nonneg_right hστ (abs_nonneg σ)
        have h2 : τ ^ 2 ≤ σ ^ 2 := by rw [← sq_abs σ]; exact pow_le_pow_left₀ hτ0.le hστ 2
        have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
        nlinarith [mul_le_mul_of_nonneg_left h1 hs2, mul_le_mul_of_nonneg_left h2 hs2]
      calc ‖m σ‖ * (Real.exp (-(y * σ) - s ^ 2 * σ ^ 2 / 2) *
            ‖1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72‖)
          ≤ (a + b * |σ|) * ((Real.exp (-(s ^ 2 * τ ^ 2) / 8) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) *
              (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)) :=
            mul_le_mul (hnm σ) (mul_le_mul hexp hpoly (norm_nonneg _) (by positivity)) (by positivity)
              (by positivity)
        _ = Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ := by simp only [h2, P]; ring
    calc ‖∫ σ in Sᶜ, g σ‖ ≤ ∫ σ in Sᶜ, Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ :=
          norm_integral_le_of_norm_le (hh2.const_mul _).integrableOn hpt
      _ ≤ ∫ σ, Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ :=
          setIntegral_le_integral (hh2.const_mul _) (Filter.Eventually.of_forall fun σ => by
            simp only [h2, P]; positivity)
      _ = Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (a * TIs α3 α4 s + b * TIs1 α3 α4 s) := by
          rw [integral_const_mul]
          simp only [h2]
          rw [integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul, integral_const_mul, hv0, hv1]
          unfold TIs TIs1; rw [← hs']; ring

end ArcsAlgo.Edge
