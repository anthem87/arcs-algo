module

public import ArcsAlgo.LocalLimit.MainRange
public import ArcsAlgo.LocalLimit.Moments
set_option autoImplicit false

/-!
# The constants of Lemma B0′ (paper §6.2)

With `a = kσ²/2`, `B = kκ₄/24`, `β = kσ²(1/2 − δ)` and `θ₀ = π/M`:

* `term_one_le`: `(2π)⁻¹ (B²/2) m₈(a) ≤ 0.146/(σk^{5/2})`, from `κ₄² ≤ 4σ⁸`
  (`abs_kap4_le`) and `105√(2π)/(2304π) ≤ 0.0365`;
* `term_two_le`: `(2π)⁻¹ 65ckσ⁶ m₆(β) ≤ 0.19/(σk^{5/2})`, from `δ ≤ 0.011`;
* `term_mid_le`: `(2π)⁻¹ q_M^{k−2} (2π/M) ≤ q_M^{k−2}/(√12σ)`, since `√12σ = √(M² − 1) ≤ M`;
* `term_tail_le`: the tails of the Gaussian and of the Edgeworth term beyond `θ₀` are
  `≤ (0.41/k + 0.11)e^{−0.308k}/σ`, using `aθ₀² ≥ kπ²/32 ≥ 0.308k`, `M ≤ 4σ` and `σ ≤ 0.2887M`.
-/

open Real

@[expose] public section

namespace ArcsAlgo.LLT

lemma abs_kap4_le {M : ℕ} (hM : 2 ≤ M) : |kap4 M| ≤ 2 * sig2 M ^ 2 := by
  have h2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [abs_of_nonpos (kap4_nonpos hM)]
  unfold kap4 sig2
  have h1 : (0 : ℝ) ≤ (M : ℝ) ^ 2 - 1 := by nlinarith
  have h4 : (0 : ℝ) ≤ (M : ℝ) ^ 2 - 4 := by nlinarith
  nlinarith [mul_nonneg h1 h4]

lemma sqrt_two_pi_le : √(2 * π) ≤ 2.5067 := by
  rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d4]

lemma sqrt_pi_le : √π ≤ 1.7725 := by
  rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d4]

/-- The first error term: `(2π)⁻¹ (B²/2) m₈(a) ≤ 0.146/(σ k^{5/2})`. -/
lemma term_one_le {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) :
    1 / (2 * π) * ((k * kap4 M / 24) ^ 2 / 2 * mom 8 (k * sig2 M / 2)) ≤
      0.146 / (√(sig2 M) * k ^ 2 * √k) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) * sig2 M / 2 := by positivity
  rw [mom_eight ha]
  have hsq : √(π / (k * sig2 M / 2)) = √(2 * π) / (√k * √(sig2 M)) := by
    rw [show π / (k * sig2 M / 2) = 2 * π / (k * sig2 M) by field_simp,
      Real.sqrt_div (by positivity), Real.sqrt_mul hk0.le]
  rw [hsq]
  have hr : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  have hσ : 0 < √(sig2 M) := Real.sqrt_pos.mpr hs
  have hrk : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  have hσs : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hs.le
  have e : 1 / (2 * π) * ((k * kap4 M / 24) ^ 2 / 2 *
      (105 / (16 * (k * sig2 M / 2) ^ 4) * (√(2 * π) / (√k * √(sig2 M))))) =
      (kap4 M ^ 2 / sig2 M ^ 4) * (105 * √(2 * π) / (2304 * π)) /
        (√(sig2 M) * k ^ 2 * √k) := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hK : kap4 M ^ 2 / sig2 M ^ 4 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    have := abs_kap4_le hM
    have h0 := abs_nonneg (kap4 M)
    nlinarith [sq_abs (kap4 M)]
  have hc : 105 * √(2 * π) / (2304 * π) ≤ 0.0365 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sqrt_two_pi_le, Real.pi_gt_d4]
  have h1 : 0 ≤ kap4 M ^ 2 / sig2 M ^ 4 := by positivity
  have h2 : 0 ≤ 105 * √(2 * π) / (2304 * π) := by positivity
  nlinarith [mul_le_mul hK hc h2 (by norm_num)]

lemma deltaL_le : deltaL ≤ 0.011 := by
  unfold deltaL cL
  have : π ^ 4 ≤ 3.1416 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 4
  nlinarith

/-- The second error term: `(2π)⁻¹ 65ckσ⁶ m₆(β) ≤ 0.19/(σ k^{5/2})`. -/
lemma term_two_le {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) :
    1 / (2 * π) * (65 * cL * k * sig2 M ^ 3 * mom 6 (k * sig2 M * (1 / 2 - deltaL))) ≤
      0.19 / (√(sig2 M) * k ^ 2 * √k) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hδ := deltaL_le
  set b := 1 / 2 - deltaL with hbdef
  have hb : 0.489 ≤ b := by rw [hbdef]; linarith
  have hb0 : 0 < b := by linarith
  have hβ : 0 < (k : ℝ) * sig2 M * b := by positivity
  rw [mom_six hβ]
  have hsq : √(π / (k * sig2 M * b)) = √π / (√k * √(sig2 M) * √b) := by
    rw [Real.sqrt_div hπ.le, Real.sqrt_mul (by positivity), Real.sqrt_mul hk0.le]
  rw [hsq]
  have hr : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  have hσ : 0 < √(sig2 M) := Real.sqrt_pos.mpr hs
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb0
  have e : 1 / (2 * π) * (65 * cL * k * sig2 M ^ 3 *
      (15 / (8 * (k * sig2 M * b) ^ 3) * (√π / (√k * √(sig2 M) * √b)))) =
      (65 * cL * 15 * √π / (16 * π * b ^ 3 * √b)) / (√(sig2 M) * k ^ 2 * √k) := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsb' : 0.699 ≤ √b := by
    rw [Real.le_sqrt (by norm_num) hb0.le]; nlinarith
  have hb3 : 0.489 ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
  rw [div_le_iff₀ (by positivity)]
  unfold cL
  have hD : (0.489 : ℝ) ^ 3 * 0.699 ≤ b ^ 3 * √b := mul_le_mul hb3 hsb' (by norm_num) (by positivity)
  have hpi := Real.pi_gt_d4
  have hsp := sqrt_pi_le
  nlinarith [mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 16 * π)]

/-- The middle range: `(2π)⁻¹ q^{k−2} (2π/M) ≤ q^{k−2}/(√12 σ)`. -/
lemma term_mid_le {M : ℕ} (hM : 2 ≤ M) (k : ℕ) :
    1 / (2 * π) * (qM M ^ (k - 2) * (2 * π / M)) ≤ qM M ^ (k - 2) / (√12 * √(sig2 M)) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hq := (qM_pos hM).le
  have e : 1 / (2 * π) * (qM M ^ (k - 2) * (2 * π / M)) = qM M ^ (k - 2) / M := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  rw [← Real.sqrt_mul (by norm_num)]
  rw [Real.sqrt_le_left hM0.le]
  unfold sig2; nlinarith

set_option maxHeartbeats 1000000 in
/-- The Gaussian and Edgeworth tails beyond `π/M`. -/
lemma term_tail_le {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) :
    1 / (2 * π) * (2 * (Real.exp (-(k * sig2 M / 2) * (π / M) ^ 2) /
      (2 * (k * sig2 M / 2) * (π / M)) + |k * kap4 M / 24| *
      (Real.exp (-(k * sig2 M / 2) * (π / M) ^ 2) * ((π / M) ^ 3 / (2 * (k * sig2 M / 2)) +
        3 * (π / M) / (4 * (k * sig2 M / 2) ^ 2) + 3 / (8 * (k * sig2 M / 2) ^ 3 * (π / M)))))) ≤
      (0.41 / k + 0.11) * Real.exp (-0.308 * k) / √(sig2 M) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0' : (0 : ℝ) < k := by linarith
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set σ := √(sig2 M) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hs
  have hσ2 : sig2 M = σ ^ 2 := (Real.sq_sqrt hs.le).symm
  set m := (M : ℝ) with hm
  have hm4 : m ≤ 4 * σ := by
    have := M_sq_le hM
    rw [hσ2] at this
    nlinarith
  have hm12 : 12 * σ ^ 2 ≤ m ^ 2 := by rw [← hσ2]; unfold sig2; linarith
  have hsm : σ ≤ 0.2887 * m := by nlinarith
  have hB : |(k : ℝ) * kap4 M / 24| ≤ k * σ ^ 4 / 12 := by
    rw [abs_div, abs_mul, abs_of_pos hk0', abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    have := abs_kap4_le hM
    rw [hσ2] at this
    have : (k : ℝ) * |kap4 M| ≤ k * (2 * (σ ^ 2) ^ 2) := mul_le_mul_of_nonneg_left this hk0'.le
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  set E := Real.exp (-(k * sig2 M / 2) * (π / m) ^ 2)
  have hE : E ≤ Real.exp (-0.308 * k) := by
    apply Real.exp_le_exp.mpr
    rw [hσ2]
    have hpi2 : (9.86 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_d4]
    have : (k : ℝ) * σ ^ 2 / 2 * (π / m) ^ 2 = k * π ^ 2 / 2 * (σ ^ 2 / m ^ 2) := by
      field_simp
    have hr : 1 / 16 ≤ σ ^ 2 / m ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ k * π ^ 2 / 2)]
  have hE0 : 0 < E := Real.exp_pos _
  set Bb := |(k : ℝ) * kap4 M / 24|
  have hBb0 : 0 ≤ Bb := abs_nonneg _
  rw [hσ2]
  -- the four pieces, each times `1/π`
  have q1 : 1 / π * (1 / (2 * (k * σ ^ 2 / 2) * (π / m))) ≤ 0.41 / (k * σ) := by
    have e : 1 / π * (1 / (2 * (k * σ ^ 2 / 2) * (π / m))) = m / (π ^ 2 * k * σ ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpi2 : (9.86 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_d4]
    have : m * (k * σ) ≤ 4 * σ * (k * σ) := mul_le_mul_of_nonneg_right hm4 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hpi2 (by positivity : (0 : ℝ) ≤ k * σ ^ 2)]
  have q2 : 1 / π * (Bb * ((π / m) ^ 3 / (2 * (k * σ ^ 2 / 2)))) ≤ 0.02 / σ := by
    have e : 1 / π * (Bb * ((π / m) ^ 3 / (2 * (k * σ ^ 2 / 2)))) =
        Bb * π ^ 2 / (k * σ ^ 2 * m ^ 3) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hσ]
    have hpi2 : π ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
    have h3 : σ ^ 3 ≤ 0.2887 ^ 3 * m ^ 3 := by
      have := pow_le_pow_left₀ hσ.le hsm 3; rw [mul_pow] at this; exact this
    have : Bb * π ^ 2 * σ ≤ k * σ ^ 4 / 12 * 9.87 * σ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hB hpi2 (by positivity) (by positivity)) hσ.le
    have hk3 : (0 : ℝ) ≤ k * σ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hk3]
  have q3 : 1 / π * (Bb * (3 * (π / m) / (4 * (k * σ ^ 2 / 2) ^ 2))) ≤ 0.037 / σ := by
    have e : 1 / π * (Bb * (3 * (π / m) / (4 * (k * σ ^ 2 / 2) ^ 2))) =
        3 * Bb / (m * k ^ 2 * σ ^ 4) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hσ]
    have : 3 * Bb * σ ≤ 3 * (k * σ ^ 4 / 12) * σ := by nlinarith
    have h2 : σ ≤ 0.2887 * m := hsm
    have : (k : ℝ) * σ ^ 4 * σ ≤ k * σ ^ 4 * (0.2887 * m) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hk4 : (2 : ℝ) * (k * σ ^ 4 * m) ≤ k * (k * σ ^ 4 * m) :=
      mul_le_mul_of_nonneg_right hk0 (by positivity)
    nlinarith
  have q4 : 1 / π * (Bb * (3 / (8 * (k * σ ^ 2 / 2) ^ 3 * (π / m)))) ≤ 0.026 / σ := by
    have e : 1 / π * (Bb * (3 / (8 * (k * σ ^ 2 / 2) ^ 3 * (π / m)))) =
        3 * Bb * m / (π ^ 2 * k ^ 3 * σ ^ 6) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hσ]
    have hpi2 : (9.86 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_d4]
    have h1 : 3 * Bb * m * σ ≤ 3 * (k * σ ^ 4 / 12) * (4 * σ) * σ := by
      have := mul_le_mul hB hm4 (by positivity) (by positivity)
      nlinarith
    have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hc : (1 : ℝ) ≤ 0.026 * π ^ 2 * k ^ 2 := by nlinarith [mul_le_mul hpi2 hk2 (by norm_num) (by positivity)]
    have h3 : (k : ℝ) * σ ^ 6 ≤ 0.026 * (π ^ 2 * k ^ 3 * σ ^ 6) := by
      have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ k * σ ^ 6)
      calc (k : ℝ) * σ ^ 6 = k * σ ^ 6 * 1 := by ring
        _ ≤ k * σ ^ 6 * (0.026 * π ^ 2 * k ^ 2) := this
        _ = _ := by ring
    calc 3 * Bb * m * σ ≤ 3 * (k * σ ^ 4 / 12) * (4 * σ) * σ := h1
      _ = k * σ ^ 6 := by ring
      _ ≤ _ := h3
  -- combine
  have key : 1 / π * (1 / (2 * (k * σ ^ 2 / 2) * (π / m)) + Bb *
      ((π / m) ^ 3 / (2 * (k * σ ^ 2 / 2)) + 3 * (π / m) / (4 * (k * σ ^ 2 / 2) ^ 2) +
        3 / (8 * (k * σ ^ 2 / 2) ^ 3 * (π / m)))) ≤ (0.41 / k + 0.11) / σ := by
    have e : (0.41 / k + 0.11) / σ = 0.41 / (k * σ) + 0.11 / σ := by rw [add_div, div_div]
    rw [e]
    have : 0.02 / σ + 0.037 / σ + 0.026 / σ ≤ 0.11 / σ := by
      rw [← add_div, ← add_div]; apply div_le_div_of_nonneg_right (by norm_num) hσ.le
    nlinarith [q1, q2, q3, q4]
  have e2 : 1 / (2 * π) * (2 * (E / (2 * (k * σ ^ 2 / 2) * (π / m)) + Bb *
      (E * ((π / m) ^ 3 / (2 * (k * σ ^ 2 / 2)) + 3 * (π / m) / (4 * (k * σ ^ 2 / 2) ^ 2) +
        3 / (8 * (k * σ ^ 2 / 2) ^ 3 * (π / m)))))) =
      E * (1 / π * (1 / (2 * (k * σ ^ 2 / 2) * (π / m)) + Bb *
      ((π / m) ^ 3 / (2 * (k * σ ^ 2 / 2)) + 3 * (π / m) / (4 * (k * σ ^ 2 / 2) ^ 2) +
        3 / (8 * (k * σ ^ 2 / 2) ^ 3 * (π / m))))) := by
    ring
  rw [e2]
  have hQ0 : 0 ≤ (0.41 / k + 0.11) / σ := by positivity
  calc _ ≤ E * ((0.41 / k + 0.11) / σ) := mul_le_mul_of_nonneg_left key hE0.le
    _ ≤ Real.exp (-0.308 * k) * ((0.41 / k + 0.11) / σ) := mul_le_mul_of_nonneg_right hE hQ0
    _ = _ := by ring

end ArcsAlgo.LLT
