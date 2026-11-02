module

public import ArcsAlgo.LocalLimit.CharFun
public import ArcsAlgo.LocalLimit.Gauss
set_option autoImplicit false

/-!
# The main range `|θ| ≤ π/M` (paper §6.2, proof of Lemma B0′)

With `a = kσ²/2`, `B = kκ₄/24` and `D = k(Λ₆(M|θ|/2) − Λ₆(|θ|/2))`,
`f(θ)^k = e^{−aθ²} e^{Bθ⁴ + D}`. Since `Bθ⁴ ≤ 0`, `|e^{A+D} − 1 − A| ≤ A²/2 + |D|e^{|D|}`
(`abs_exp_add_sub_le`). By `abs_lam6_le` and `M ≤ 4σ`, `|D| ≤ 65ckσ⁶θ⁶` and
`|D| ≤ δkσ²θ²` with `δ = 65cπ⁴/256`, so (`main_pointwise`)
`|f^k − e^{−aθ²}(1 + Bθ⁴)| ≤ e^{−aθ²}B²θ⁸/2 + 65ckσ⁶θ⁶e^{−kσ²(1/2 − δ)θ²}`.
-/

open Real Complex MeasureTheory

@[expose] public section

namespace ArcsAlgo.LLT

lemma exp_le_quadratic_of_nonpos {A : ℝ} (hA : A ≤ 0) : Real.exp A ≤ 1 + A + A ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (neg_nonneg.mpr hA)
  have hpos : 0 < 1 + -A + (-A) ^ 2 / 2 := by nlinarith
  have e : Real.exp A = 1 / Real.exp (-A) := by rw [Real.exp_neg, one_div, inv_inv]
  rw [e, div_le_iff₀ (Real.exp_pos _)]
  have : 1 ≤ (1 + A + A ^ 2 / 2) * (1 + -A + (-A) ^ 2 / 2) := by nlinarith [sq_nonneg (A ^ 2)]
  have hq : 0 ≤ 1 + A + A ^ 2 / 2 := by nlinarith [sq_nonneg (A + 1)]
  nlinarith [mul_le_mul_of_nonneg_left h hq]

lemma abs_exp_sub_one_le' (D : ℝ) : |Real.exp D - 1| ≤ |D| * Real.exp |D| := by
  rcases le_or_gt 0 D with hD | hD
  · rw [abs_of_nonneg hD, abs_of_nonneg (by linarith [Real.add_one_le_exp D])]
    have h := Real.add_one_le_exp (-D)
    have e : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp D * (-D + 1) ≤ Real.exp D * Real.exp (-D) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos D).le
    rw [e] at h3; linarith
  · rw [abs_of_neg hD, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hD.le] : Real.exp D - 1 ≤ 0)]
    have h1 := Real.add_one_le_exp D
    have h2 : 1 ≤ Real.exp (-D) := Real.one_le_exp (by linarith)
    nlinarith

/-- `|e^{A+D} − 1 − A| ≤ A²/2 + |D| e^{|D|}` for `A ≤ 0`. -/
lemma abs_exp_add_sub_le {A D : ℝ} (hA : A ≤ 0) :
    |Real.exp (A + D) - 1 - A| ≤ A ^ 2 / 2 + |D| * Real.exp |D| := by
  have e : Real.exp (A + D) - 1 - A = (Real.exp A - 1 - A) + Real.exp A * (Real.exp D - 1) := by
    rw [Real.exp_add]; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_of_nonneg (by linarith [Real.add_one_le_exp A])]
    linarith [exp_le_quadratic_of_nonpos hA]
  · rw [abs_mul, abs_of_pos (Real.exp_pos A)]
    have : Real.exp A ≤ 1 := Real.exp_le_one_iff.mpr hA
    calc Real.exp A * |Real.exp D - 1| ≤ 1 * |Real.exp D - 1| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ ≤ |D| * Real.exp |D| := by rw [one_mul]; exact abs_exp_sub_one_le' D

/-- The constant of `|Λ₆(t)| ≤ c t⁶`. -/
noncomputable def cL : ℝ := 0.00044

/-- `δ = 65 c π⁴ / 256`, the loss in the Gaussian exponent from `e^{|D|}`. -/
noncomputable def deltaL : ℝ := 65 * cL * π ^ 4 / 256

lemma sig2_pos {M : ℕ} (hM : 2 ≤ M) : 0 < sig2 M := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sig2; nlinarith

lemma M_sq_le {M : ℕ} (hM : 2 ≤ M) : (M : ℝ) ^ 2 ≤ 16 * sig2 M := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sig2; nlinarith

lemma kap4_nonpos {M : ℕ} (hM : 2 ≤ M) : kap4 M ≤ 0 := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold kap4
  have := pow_le_pow_left₀ (by norm_num) this 4
  norm_num at this
  linarith

/-- The pointwise estimate on the main range `|θ| ≤ π/M`:
`|f(θ)^k − e^{−aθ²}(1 + Bθ⁴)| ≤ e^{−aθ²} B²θ⁸/2 + 65 c k σ⁶ θ⁶ e^{−βθ²}`, with `a = kσ²/2`,
`B = kκ₄/24`, `β = kσ²(1/2 − δ)`. -/
lemma main_pointwise {M k : ℕ} (hM : 2 ≤ M) {θ : ℝ} (hθ : |θ| ≤ π / M) :
    |fC M θ ^ k - Real.exp (-(k * sig2 M / 2) * θ ^ 2) * (1 + k * kap4 M / 24 * θ ^ 4)| ≤
      Real.exp (-(k * sig2 M / 2) * θ ^ 2) * ((k * kap4 M / 24) ^ 2 * θ ^ 8 / 2) +
      65 * cL * k * sig2 M ^ 3 * θ ^ 6 *
        Real.exp (-(k * sig2 M * (1 / 2 - deltaL)) * θ ^ 2) := by
  have hπ := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hR : 0 ≤ Real.exp (-(k * sig2 M / 2) * θ ^ 2) * ((k * kap4 M / 24) ^ 2 * θ ^ 8 / 2) +
      65 * cL * k * sig2 M ^ 3 * θ ^ 6 * Real.exp (-(k * sig2 M * (1 / 2 - deltaL)) * θ ^ 2) := by
    unfold cL; positivity
  rcases eq_or_ne θ 0 with h0 | h0
  · subst h0; rw [fC_zero (by omega)]; simp
  obtain ⟨hpos, hlog⟩ := fC_main hM h0 hθ
  set s := |θ| with hsdef
  have hs0 : 0 < s := abs_pos.mpr h0
  set y := M * s / 2
  set x := s / 2
  have hy0 : 0 < y := by positivity
  have hx0 : 0 < x := by positivity
  have hyπ : y ≤ π / 2 := by
    have := (le_div_iff₀ hM0).mp hθ; simp only [y]; nlinarith
  have hxπ : x ≤ π / 2 := by
    have : π / M ≤ π / 2 := div_le_div_of_nonneg_left hπ.le (by norm_num) hM2
    simp only [x]; linarith
  set A := k * kap4 M / 24 * θ ^ 4
  set D := (k : ℝ) * (lam6 y - lam6 x)
  have hA : A ≤ 0 := by
    have := kap4_nonpos hM
    simp only [A]
    have : 0 ≤ θ ^ 4 := by positivity
    have : k * kap4 M / 24 ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hk0 (kap4_nonpos hM); linarith
    nlinarith
  have hfk : fC M θ ^ k = Real.exp (-(k * sig2 M / 2) * θ ^ 2) * Real.exp (A + D) := by
    rw [← Real.exp_log hpos, ← Real.exp_nat_mul, hlog, ← Real.exp_add]
    congr 1; simp only [A, D]; ring
  -- `|D| ≤ k c (y⁶ + x⁶) ≤ (65/64) k c y⁶`
  have hy6 : x ^ 6 ≤ y ^ 6 / 64 := by
    have : y = M * x := by simp only [x, y]; ring
    rw [this, mul_pow]
    have : (64 : ℝ) ≤ (M : ℝ) ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hM2 6; norm_num at this; linarith
    have hx6 : 0 ≤ x ^ 6 := by positivity
    nlinarith
  have hD : |D| ≤ (65 / 64) * k * cL * y ^ 6 := by
    have h1 := abs_lam6_le hy0 hyπ
    have h2 := abs_lam6_le hx0 hxπ
    simp only [D, abs_mul, abs_of_nonneg hk0]
    have := abs_sub (lam6 y) (lam6 x)
    unfold cL
    calc (k : ℝ) * |lam6 y - lam6 x| ≤ k * (0.00044 * y ^ 6 + 0.00044 * x ^ 6) :=
          mul_le_mul_of_nonneg_left (by linarith) hk0
      _ ≤ 65 / 64 * k * 0.00044 * y ^ 6 := by nlinarith
  -- `y² ≤ 4σ²θ²`
  have hy2 : y ^ 2 ≤ 4 * sig2 M * θ ^ 2 := by
    have : y ^ 2 = (M : ℝ) ^ 2 * θ ^ 2 / 4 := by simp only [y, hsdef, mul_pow, div_pow, sq_abs]; ring
    rw [this]
    have := M_sq_le hM
    have : 0 ≤ θ ^ 2 := sq_nonneg _
    nlinarith
  have hD6 : |D| ≤ 65 * cL * k * sig2 M ^ 3 * θ ^ 6 := by
    have hy6' : y ^ 6 ≤ 64 * sig2 M ^ 3 * θ ^ 6 := by
      have e : y ^ 6 = (y ^ 2) ^ 3 := by ring
      have e2 : 64 * sig2 M ^ 3 * θ ^ 6 = (4 * sig2 M * θ ^ 2) ^ 3 := by ring
      rw [e, e2]; exact pow_le_pow_left₀ (sq_nonneg _) hy2 3
    have : 0 ≤ (k : ℝ) * cL := by unfold cL; positivity
    calc |D| ≤ 65 / 64 * k * cL * y ^ 6 := hD
      _ ≤ 65 / 64 * k * cL * (64 * sig2 M ^ 3 * θ ^ 6) :=
          mul_le_mul_of_nonneg_left hy6' (by unfold cL; positivity)
      _ = 65 * cL * k * sig2 M ^ 3 * θ ^ 6 := by ring
  have hD2 : |D| ≤ deltaL * k * sig2 M * θ ^ 2 := by
    have hy4 : y ^ 4 ≤ (π / 2) ^ 4 := pow_le_pow_left₀ hy0.le hyπ 4
    have : y ^ 6 ≤ (π / 2) ^ 4 * (4 * sig2 M * θ ^ 2) := by
      have e : y ^ 6 = y ^ 4 * y ^ 2 := by ring
      rw [e]; exact mul_le_mul hy4 hy2 (sq_nonneg _) (by positivity)
    calc |D| ≤ 65 / 64 * k * cL * y ^ 6 := hD
      _ ≤ 65 / 64 * k * cL * ((π / 2) ^ 4 * (4 * sig2 M * θ ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by unfold cL; positivity)
      _ = deltaL * k * sig2 M * θ ^ 2 := by unfold deltaL; ring
  rw [hfk, show Real.exp (-(k * sig2 M / 2) * θ ^ 2) * Real.exp (A + D) -
      Real.exp (-(k * sig2 M / 2) * θ ^ 2) * (1 + A) =
      Real.exp (-(k * sig2 M / 2) * θ ^ 2) * (Real.exp (A + D) - 1 - A) by ring, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have herr := abs_exp_add_sub_le (D := D) hA
  have hE := Real.exp_pos (-(k * sig2 M / 2) * θ ^ 2)
  calc Real.exp (-(k * sig2 M / 2) * θ ^ 2) * |Real.exp (A + D) - 1 - A|
      ≤ Real.exp (-(k * sig2 M / 2) * θ ^ 2) * (A ^ 2 / 2 + |D| * Real.exp |D|) :=
        mul_le_mul_of_nonneg_left herr hE.le
    _ = Real.exp (-(k * sig2 M / 2) * θ ^ 2) * (A ^ 2 / 2) +
        |D| * (Real.exp (-(k * sig2 M / 2) * θ ^ 2) * Real.exp |D|) := by ring
    _ ≤ Real.exp (-(k * sig2 M / 2) * θ ^ 2) * ((k * kap4 M / 24) ^ 2 * θ ^ 8 / 2) +
        65 * cL * k * sig2 M ^ 3 * θ ^ 6 *
          Real.exp (-(k * sig2 M * (1 / 2 - deltaL)) * θ ^ 2) := by
        apply add_le_add (le_of_eq (by simp only [A]; ring))
        rw [← Real.exp_add]
        apply mul_le_mul hD6 (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
          (by unfold cL; positivity)

end ArcsAlgo.LLT
