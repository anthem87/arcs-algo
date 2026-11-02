module

public import ArcsAlgo.EdgeGaussC
set_option autoImplicit false

/-!
# The Edgeworth bracket with complex `z` (paper §3.5, Remark (the formula of Proposition C))

* `HeC_le`: `|He_k(z)| ≤ c_kR⁶` for `|z| ≤ R`, `R ≥ 1` (`k = 3, 4, 6`).
* `norm_phiC`: `|φ(z)| = e^{((Im z)² − (Re z)²)/2}/√(2π)`.
* `mainEC_ge`: for small normalized cumulants, `|mainEC(T)| ≥ |φ(z)|/(2s)`.

No hypothesis.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge

/-- `|He_k(z)| ≤ c_k R^k` for complex `z`, `‖z‖ ≤ R`, `R ≥ 1` (`k = 3, 4, 6`). -/
theorem HeC_le {z : ℂ} {R : ℝ} (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖HeC 3 z‖ ≤ 4 * R ^ 6 ∧ ‖HeC 4 z‖ ≤ 10 * R ^ 6 ∧ ‖HeC 6 z‖ ≤ 76 * R ^ 6 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hp : ∀ k : ℕ, ‖z‖ ^ k ≤ R ^ 6 → ‖z ^ k‖ ≤ R ^ 6 := fun k h => by rw [norm_pow]; exact h
  have hRk : ∀ k : ℕ, k ≤ 6 → ‖z‖ ^ k ≤ R ^ 6 := fun k hk =>
    (pow_le_pow_left₀ hz0 hz k).trans (pow_le_pow_right₀ hR hk)
  have h1 : ‖z‖ ≤ R ^ 6 := by simpa using hRk 1 (by norm_num)
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  simp only [HeC]
  refine ⟨?_, ?_, ?_⟩
  · calc ‖z ^ 3 - 3 * z‖ ≤ ‖z ^ 3‖ + ‖3 * z‖ := norm_sub_le _ _
      _ ≤ R ^ 6 + 3 * R ^ 6 := by
          rw [norm_mul, Complex.norm_ofNat]; gcongr; exact hp 3 (hRk 3 (by norm_num))
      _ = 4 * R ^ 6 := by ring
  · calc ‖z ^ 4 - 6 * z ^ 2 + 3‖ ≤ ‖z ^ 4‖ + ‖6 * z ^ 2‖ + ‖(3 : ℂ)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ R ^ 6 + 6 * R ^ 6 + 3 * R ^ 6 := by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
          gcongr
          · exact hp 4 (hRk 4 (by norm_num))
          · exact hp 2 (hRk 2 (by norm_num))
          · linarith
      _ = 10 * R ^ 6 := by ring
  · calc ‖z ^ 6 - 15 * z ^ 4 + 45 * z ^ 2 - 15‖ ≤ ‖z ^ 6‖ + ‖15 * z ^ 4‖ + ‖45 * z ^ 2‖ + ‖(15 : ℂ)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
      _ ≤ R ^ 6 + 15 * R ^ 6 + 45 * R ^ 6 + 15 * R ^ 6 := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
          gcongr
          · exact hp 6 (hRk 6 le_rfl)
          · exact hp 4 (hRk 4 (by norm_num))
          · exact hp 2 (hRk 2 (by norm_num))
          · linarith
      _ = 76 * R ^ 6 := by ring

/-- `|φ(z)| = e^{(Im z)²/2 − (Re z)²/2}/√(2π)`. -/
theorem norm_phiC (z : ℂ) : ‖phiC z‖ = Real.exp ((z.im ^ 2 - z.re ^ 2) / 2) / Real.sqrt (2 * π) := by
  unfold phiC
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  congr 2
  simp [sq, Complex.mul_re]

/-- **The Edgeworth bracket is `≥ 1/2`, complex `z`**: if `|κ₃|/(6s³), |κ₄|/(24s⁴) ≤ u`, `u ≤ 1`,
`52R⁶u ≤ 1/2` and `|z| ≤ R`, then `|mainEC(T)| ≥ |φ(z)|/(2s)`. -/
theorem mainEC_ge {k1 : ℂ} {s R u : ℝ} {κ₃ κ₄ : ℂ} (hs : 0 < s) (hR : 1 ≤ R) (T : ℝ)
    (hz : ‖((T : ℂ) - k1) / s‖ ≤ R) (h3 : ‖κ₃‖ / 6 / s ^ 3 ≤ u) (h4 : ‖κ₄‖ / 24 / s ^ 4 ≤ u) (hu1 : u ≤ 1)
    (hu : 52 * R ^ 6 * u ≤ 1 / 2) :
    ‖phiC (((T : ℂ) - k1) / s)‖ / (2 * s) ≤ ‖mainEC k1 s κ₃ κ₄ T‖ := by
  set z := ((T : ℂ) - k1) / s
  obtain ⟨b3, b4, b6⟩ := HeC_le hR hz
  have hu0 : 0 ≤ u := le_trans (by positivity) h3
  unfold mainEC
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hns : ∀ k : ℕ, ‖(s : ℂ) ^ k‖ = s ^ k := fun k => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have n3 : ‖κ₃ * HeC 3 z / (6 * (s : ℂ) ^ 3)‖ ≤ 4 * R ^ 6 * u := by
    rw [norm_div, norm_mul, norm_mul, hns, Complex.norm_ofNat]
    calc ‖κ₃‖ * ‖HeC 3 z‖ / (6 * s ^ 3) = ‖κ₃‖ / 6 / s ^ 3 * ‖HeC 3 z‖ := by ring
      _ ≤ u * (4 * R ^ 6) := mul_le_mul h3 b3 (norm_nonneg _) hu0
      _ = _ := by ring
  have n4 : ‖κ₄ * HeC 4 z / (24 * (s : ℂ) ^ 4)‖ ≤ 10 * R ^ 6 * u := by
    rw [norm_div, norm_mul, norm_mul, hns, Complex.norm_ofNat]
    calc ‖κ₄‖ * ‖HeC 4 z‖ / (24 * s ^ 4) = ‖κ₄‖ / 24 / s ^ 4 * ‖HeC 4 z‖ := by ring
      _ ≤ u * (10 * R ^ 6) := mul_le_mul h4 b4 (norm_nonneg _) hu0
      _ = _ := by ring
  have n6 : ‖κ₃ ^ 2 * HeC 6 z / (72 * (s : ℂ) ^ 6)‖ ≤ 38 * R ^ 6 * u := by
    rw [norm_div, norm_mul, norm_pow, norm_mul, hns, Complex.norm_ofNat]
    have hq : (‖κ₃‖ / 6 / s ^ 3) ^ 2 ≤ u := by
      have := pow_le_pow_left₀ (by positivity) h3 2; nlinarith
    calc ‖κ₃‖ ^ 2 * ‖HeC 6 z‖ / (72 * s ^ 6) = (‖κ₃‖ / 6 / s ^ 3) ^ 2 / 2 * ‖HeC 6 z‖ := by
          field_simp; ring
      _ ≤ u / 2 * (76 * R ^ 6) := mul_le_mul (by linarith) b6 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hb : 1 / 2 ≤ ‖1 + κ₃ * HeC 3 z / (6 * (s : ℂ) ^ 3) + κ₄ * HeC 4 z / (24 * (s : ℂ) ^ 4) +
      κ₃ ^ 2 * HeC 6 z / (72 * (s : ℂ) ^ 6)‖ := by
    set a := κ₃ * HeC 3 z / (6 * (s : ℂ) ^ 3)
    set b := κ₄ * HeC 4 z / (24 * (s : ℂ) ^ 4)
    set c := κ₃ ^ 2 * HeC 6 z / (72 * (s : ℂ) ^ 6)
    have h := norm_sub_norm_le (1 : ℂ) (-(a + b + c))
    rw [sub_neg_eq_add, norm_one, norm_neg] at h
    have := norm_add₃_le (a := a) (b := b) (c := c)
    have e : (1 : ℂ) + (a + b + c) = 1 + a + b + c := by ring
    rw [e] at h
    linarith
  have hφ : 0 ≤ ‖phiC z‖ / s := by positivity
  calc ‖phiC z‖ / (2 * s) = ‖phiC z‖ / s * (1 / 2) := by ring
    _ ≤ ‖phiC z‖ / s * _ := mul_le_mul_of_nonneg_left hb hφ

end ArcsAlgo.Core
