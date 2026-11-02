module

public import ArcsAlgo.SecondMoment.BPMain1
set_option autoImplicit false

/-!
# Proposition B′: bounds on the window

`coef_bounds` (the coefficients of the expansions are bounded for `|z| ≤ g`, `|u| ≤ K`, `0 ≤ h ≤ 1`), lower and
upper bounds for the Gaussian factors, and `rel_of_abs` (from an absolute to a relative error).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The coefficients of the conditional expansion are bounded on the window. -/
theorem coef_bounds (M : ℕ) (g K : ℝ) : ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ h z u : ℝ, 0 ≤ h → h ≤ 1 → |z| ≤ g → |u| ≤ K →
    |FXt1 M z u| ≤ A0 ∧ |FXt2 M z u| ≤ A0 ∧ |FXt3 M z u| ≤ A0 ∧ |FXB M h z u| ≤ A0 ∧
    |FYt1 M z u| ≤ A0 ∧ |FYt2 M z u| ≤ A0 ∧ |FYt3 M z u| ≤ A0 ∧ |FYB M h z u| ≤ A0 ∧
    |FSt2 M z 0| ≤ A0 ∧ |GC M h z u| ≤ A0 := by
  obtain ⟨A0, hA0, hΦ⟩ := bound_on_box (f := fun h z u =>
    |FXt1 M z u| + |FXt2 M z u| + |FXt3 M z u| + |FXB M h z u| +
    |FYt1 M z u| + |FYt2 M z u| + |FYt3 M z u| + |FYB M h z u| +
    |FSt2 M z 0| + |GC M h z u|) (cont_coefs M) g K
  refine ⟨A0, hA0, fun h z u h0 h1 hz hu => ?_⟩
  have hb := hΦ h z u h0 h1 hz hu
  rw [abs_of_nonneg (by positivity)] at hb
  have := abs_nonneg (FXt1 M z u); have := abs_nonneg (FXt2 M z u); have := abs_nonneg (FXt3 M z u)
  have := abs_nonneg (FXB M h z u); have := abs_nonneg (FYt1 M z u); have := abs_nonneg (FYt2 M z u)
  have := abs_nonneg (FYt3 M z u); have := abs_nonneg (FYB M h z u); have := abs_nonneg (FSt2 M z 0)
  have := abs_nonneg (GC M h z u)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem phiX_lb (hM : 2 ≤ M) {g K z y : ℝ} (hz : z ^ 2 ≤ g ^ 2) (hy : y ^ 2 ≤ K ^ 2) :
    Real.exp (-(1 / 2) * (g ^ 2 + 2 * (K ^ 2 / ew2 M))) / (√(2 * Real.pi) ^ 3 * (√(sig2 M) * ew2 M)) ≤
      gaussDens (vcov (pX M) (xiX M)) ![√(sig2 M) * z, y, y] := by
  have he := ew2_pos M
  rw [gaussX_val hM]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : y ^ 2 / ew2 M ≤ K ^ 2 / ew2 M := div_le_div_of_nonneg_right hy he.le
  linarith

theorem phiY_lb (hM : 2 ≤ M) {g K z y : ℝ} (hz : z ^ 2 ≤ g ^ 2) (hy : y ^ 2 ≤ K ^ 2) :
    Real.exp (-(1 / 2) * (g ^ 2 + K ^ 2 / ew2 M)) / (√(2 * Real.pi) ^ 2 * (√(sig2 M) * √(ew2 M))) ≤
      gaussDens (vcov (pY M) (xiY M)) ![√(sig2 M) * z, y] := by
  have he := ew2_pos M
  rw [gaussY_val hM]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : y ^ 2 / ew2 M ≤ K ^ 2 / ew2 M := div_le_div_of_nonneg_right hy he.le
  linarith

theorem phiS_lb (hM : 2 ≤ M) {g z : ℝ} (hz : z ^ 2 ≤ g ^ 2) :
    Real.exp (-(1 / 2) * g ^ 2) / (√(2 * Real.pi) ^ 1 * √(sig2 M)) ≤
      gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * z] := by
  rw [gaussS_val hM]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith

theorem phiS_ub (hM : 2 ≤ M) (z : ℝ) :
    gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * z] ≤ 1 / (√(2 * Real.pi) ^ 1 * √(sig2 M)) := by
  rw [gaussS_val hM]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg z]

/-- From an absolute error to a relative one. -/
theorem rel_of_abs {L φ F E C φm A c : ℝ} (hφm : 0 < φm) (hφ : φm ≤ φ) (hc : 0 < c) (hE : 0 ≤ E)
    (h : |L - c * (φ * F)| ≤ C * E) (hA : C / (c * φm) ≤ A) (hC : 0 ≤ C) :
    L = c * φ * (F + (L - c * (φ * F)) / (c * φ)) ∧ |(L - c * (φ * F)) / (c * φ)| ≤ A * E := by
  have hφ0 : 0 < φ := lt_of_lt_of_le hφm hφ
  refine ⟨by field_simp; ring, ?_⟩
  rw [abs_div, abs_of_pos (by positivity : 0 < c * φ), div_le_iff₀ (by positivity)]
  calc |L - c * (φ * F)| ≤ C * E := h
    _ ≤ (C / (c * φm)) * E * (c * φ) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : 0 ≤ C * E := by positivity
        have : c * φm ≤ c * φ := mul_le_mul_of_nonneg_left hφ hc.le
        nlinarith
    _ ≤ A * E * (c * φ) := by gcongr

end ArcsAlgo.LLT
