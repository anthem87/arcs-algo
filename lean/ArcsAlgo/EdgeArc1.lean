module

public import ArcsAlgo.EdgeCore
public import ArcsAlgo.EdgeBound
public import ArcsAlgo.ThmE3
public import ArcsAlgo.LemmaWSW
set_option autoImplicit false

/-!
# Theorem E(2), the core at the peak of an arc (paper §3.5)

* `pStar θ* w = u/(1 + u)`, `u = e(wθ*)`; `kS N θ* j = κ_j*` (Proposition C at `θ*`), `sS = √κ₂*`;
  `Hhat` is the paper's `Ĥ(T)`; `Rcore` is the integral of `F_N(e(θ))e(−Tθ)` over `|θ − θ*| ≤ τ/(2π)`.
* `FW_shift`, `Rcore_eq`: `F_N(e(θ* + σ/(2π))) = F_N(e(θ*)) Π_w(1 + p_w(e^{iwσ} − 1))` and the change of
  variables `θ = θ* + σ/(2π)`.
* `cos_star_ge`, `pStar_le`: if no weight vanishes at `a/q` and `N|t*| ≤ 1/q`, then
  `|cos(πwθ*)| ≥ 1/(2q)` and `|p_w| ≤ q`.
* `kS_one`, `kS_two` (Lemma W(3)): at a critical point `t*` of `log|G|`, `κ₁* = Σ_w w/2` is real, and
  `κ₂* = Σ_w w²/(4cos²(πwθ*))` is real.

No hypothesis.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- `p_w = u/(1 + u)`, `u = e(wθ*)`: the parameter of the factor of `w` at `θ*`. -/
noncomputable def pStar (θs : ℝ) (w : ℕ) : ℂ := ee (w * θs) / (1 + ee (w * θs))

/-- The cumulants `κ_j*` of Proposition C at `θ*` (Lemma W(3)). -/
noncomputable def kS (N : ℕ) (θs : ℝ) (j : ℕ) : ℂ := kap (WN N) (pStar θs) j

/-- `s* = √κ₂*` (κ₂* is real and positive at the peak, Lemma W(3)). -/
noncomputable def sS (N : ℕ) (θs : ℝ) : ℝ := Real.sqrt (kS N θs 2).re

/-- `Ĥ(T) = e^{−iTt*} G(θ*) φ(z)/s*·(1 + κ₃*He₃(z)/(6s*³) + κ₄*He₄(z)/(24s*⁴) + κ₃*²He₆(z)/(72s*⁶))`. -/
noncomputable def Hhat (N : ℕ) (ts θs T : ℝ) : ℂ :=
  Complex.exp (-(I * T * ts)) * FW (WN N) θs *
    mainE (kS N θs 1).re (sS N θs) (kS N θs 3) (kS N θs 4) T

/-- The core integral `∫_{|θ − θ*| ≤ τ/(2π)} F_N(e(θ)) e(−Tθ) dθ`. -/
noncomputable def Rcore (N : ℕ) (θs τ T : ℝ) : ℂ :=
  ∫ θ in (θs - τ / (2 * π))..(θs + τ / (2 * π)), FW (WN N) θ * ee (-(T * θ))

theorem ee_div_two_pi (x : ℝ) : ee (x / (2 * π)) = Complex.exp (I * x) := by
  unfold ee; congr 1; push_cast; field_simp

theorem factor_split {u : ℂ} (hu : 1 + u ≠ 0) (z : ℂ) :
    1 + u * z = (1 + u) * (1 + u / (1 + u) * (z - 1)) := by
  field_simp; ring

/-- `F_N(e(θ* + σ/(2π))) = F_N(e(θ*)) Π_w (1 + p_w(e^{iwσ} − 1))` when no factor vanishes at `θ*`. -/
theorem FW_shift (N : ℕ) (θs σ : ℝ) (hne : ∀ w ∈ WN N, 1 + ee (w * θs) ≠ 0) :
    FW (WN N) (θs + σ / (2 * π)) =
      FW (WN N) θs * ∏ w ∈ WN N, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1)) := by
  unfold FW
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun w hw => ?_
  have e : ee (w * (θs + σ / (2 * π))) = ee (w * θs) * Complex.exp (I * w * σ) := by
    rw [mul_add, ee_add, show (w : ℝ) * (σ / (2 * π)) = (w * σ) / (2 * π) by ring, ee_div_two_pi]
    push_cast; ring_nf
  rw [e, factor_split (hne w hw)]; rfl

/-- The change of variables `θ = θ* + σ/(2π)`. -/
theorem Rcore_eq (N : ℕ) (θs τ T : ℝ) (hne : ∀ w ∈ WN N, 1 + ee (w * θs) ≠ 0) :
    Rcore N θs τ T = FW (WN N) θs * ee (-(T * θs)) * ((1 / (2 * π) : ℂ) *
      ∫ σ in (-τ)..τ, (∏ w ∈ WN N, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1))) *
        Complex.exp (-(I * T * σ))) := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set g : ℝ → ℂ := fun θ => FW (WN N) θ * ee (-(T * θ)) with hg
  set h : ℝ → ℂ := fun σ => (∏ w ∈ WN N, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1))) *
    Complex.exp (-(I * T * σ)) with hh
  have hcv := intervalIntegral.integral_comp_add_div (f := g) (a := -τ) (b := τ) h2π θs
  have hpt : ∀ σ : ℝ, g (θs + σ / (2 * π)) = FW (WN N) θs * ee (-(T * θs)) * h σ := by
    intro σ
    simp only [hg, hh]
    rw [FW_shift N θs σ hne]
    have e : ee (-(T * (θs + σ / (2 * π)))) = ee (-(T * θs)) * Complex.exp (-(I * T * σ)) := by
      rw [show -(T * (θs + σ / (2 * π))) = -(T * θs) + (-(T * σ)) / (2 * π) by ring, ee_add, ee_div_two_pi]
      push_cast; ring_nf
    rw [e]; ring
  rw [intervalIntegral.integral_congr (fun σ _ => hpt σ), intervalIntegral.integral_const_mul] at hcv
  unfold Rcore
  rw [show θs - τ / (2 * π) = θs + -τ / (2 * π) by ring]
  change ∫ θ in (θs + -τ / (2 * π))..(θs + τ / (2 * π)), g θ = _
  rw [Complex.real_smul] at hcv
  have h2c : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2π
  have : ∫ θ in (θs + -τ / (2 * π))..(θs + τ / (2 * π)), g θ =
      (((2 * π : ℝ) : ℂ))⁻¹ * (FW (WN N) θs * ee (-(T * θs)) * ∫ σ in (-τ)..τ, h σ) := by
    rw [hcv]; field_simp
  rw [this]; push_cast; ring

theorem ee_eq_exp2 (x : ℝ) : ee x = Complex.exp (2 * ((π * x : ℝ) : ℂ) * I) := by
  unfold ee; congr 1; push_cast; ring

section params

variable {N q a : ℕ} {ts : ℝ}

/-- **The parameters at the peak**: if no weight vanishes at `a/q` and `N|t*| ≤ 1/q`, then at
`θ* = a/q + t*/(2π)` every `|1 + e(wθ*)| ≥ 1/q`, so `|p_w| ≤ q`. -/
theorem cos_star_ge (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (hts : (N : ℝ) * |ts| ≤ 1 / q)
    {w : ℕ} (hw : w ∈ WN N) : 1 / (2 * q) ≤ |Real.cos (π * (w * ((a : ℝ) / q + ts / (2 * π))))| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 := cos_lower (by omega : 1 ≤ q) (hnv w hw) (a := a)
  have hwN : (w : ℝ) ≤ N := by
    have := (mem_filter.mp hw).1; exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp this)
  have h2 := Real.abs_cos_sub_cos_le (π * (w * ((a : ℝ) / q + ts / (2 * π)))) (π * (w * ((a : ℝ) / q)))
  have e : π * (w * ((a : ℝ) / q + ts / (2 * π))) - π * (w * ((a : ℝ) / q)) = w * ts / 2 := by
    field_simp; ring
  rw [e] at h2
  have h3 : |(w : ℝ) * ts / 2| ≤ 1 / (2 * q) := by
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg w), abs_two]
    have : (w : ℝ) * |ts| ≤ N * |ts| := mul_le_mul_of_nonneg_right hwN (abs_nonneg _)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have := mul_le_mul_of_nonneg_right (this.trans hts) hq0.le
    rw [div_mul_cancel₀ _ hq0.ne'] at this
    nlinarith
  have := abs_sub_abs_le_abs_sub (Real.cos (π * (w * ((a : ℝ) / q)))) (Real.cos (π * (w * ((a : ℝ) / q + ts / (2 * π)))))
  rw [abs_sub_comm] at this
  have h4 : 1 / (q : ℝ) - 1 / (2 * q) = 1 / (2 * q) := by field_simp; ring
  linarith

theorem pStar_le (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (hts : (N : ℝ) * |ts| ≤ 1 / q)
    {w : ℕ} (hw : w ∈ WN N) :
    1 + ee (w * ((a : ℝ) / q + ts / (2 * π))) ≠ 0 ∧ ‖pStar ((a : ℝ) / q + ts / (2 * π)) w‖ ≤ q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc := cos_star_ge hq hnv hts hw
  have hn : ‖1 + ee (w * ((a : ℝ) / q + ts / (2 * π)))‖ = 2 * |Real.cos (π * (w * ((a : ℝ) / q + ts / (2 * π))))| :=
    norm_one_add_ee _
  have hpos : 0 < ‖1 + ee (w * ((a : ℝ) / q + ts / (2 * π)))‖ := by
    rw [hn]; have : 0 < 1 / (2 * (q : ℝ)) := by positivity
    linarith
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  unfold pStar
  rw [norm_div, norm_ee, div_le_iff₀ hpos, hn]
  have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * q)
  rw [show 2 * (q : ℝ) * (1 / (2 * q)) = 1 by field_simp] at this
  linarith

theorem cos_star_ne (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (hts : (N : ℝ) * |ts| ≤ 1 / q)
    {w : ℕ} (hw : w ∈ WN N) : Real.cos (alw q a w + w * ts / 2) ≠ 0 := by
  have hc := cos_star_ge hq hnv hts hw
  rw [arg_eq q a w ts] at hc
  intro h0; rw [h0, abs_zero] at hc
  have : (0 : ℝ) < 1 / (2 * q) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  linarith

theorem pStar_eq (q a w : ℕ) (ts : ℝ) :
    pStar ((a : ℝ) / q + ts / (2 * π)) w =
      Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I) /
        (1 + Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I)) := by
  unfold pStar; rw [ee_eq_exp2, arg_eq]

/-- **`κ₁*` is real at the peak** (Lemma W(3)): `κ₁* = Σ_w w/2` when `F′(t*) = 0`. -/
theorem kS_one (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (hts : (N : ℝ) * |ts| ≤ 1 / q)
    (hF : Fw' (WN N) q a ts = 0) :
    kS N ((a : ℝ) / q + ts / (2 * π)) 1 = ((∑ w ∈ WN N, (w : ℝ) / 2 : ℝ) : ℂ) := by
  have hfilt : (WN N).filter (fun w => ¬ vanish q a w) = WN N := filter_true_of_mem hnv
  have him := im_kappa1 (W := WN N) (q := q) (a := a) ts
  rw [hF, neg_zero, hfilt] at him
  unfold kS kap
  have hterm : ∀ w ∈ WN N, (w : ℂ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℂ) * cB (pStar ((a : ℝ) / q + ts / (2 * π)) w) 1 =
      (((w : ℝ) / 2 : ℝ) : ℂ) + I * (((w : ℝ) * (Real.tan (alw q a w + w * ts / 2) / 2) : ℝ) : ℂ) := by
    intro w hw
    have hp := (p_types (cos_star_ne hq hnv hts hw)).2.2
    simp only [cB, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [pStar_eq]
    set P := Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I) /
        (1 + Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I))
    push_cast at hp ⊢
    linear_combination (w : ℂ) * hp
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum, him]
  push_cast; ring

/-- **`κ₂*` is real and `≥ S₂/4`** (Lemma W(3)): `κ₂* = Σ_w w²/(4cos²(πwθ*))`. -/
theorem kS_two (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (hts : (N : ℝ) * |ts| ≤ 1 / q) :
    kS N ((a : ℝ) / q + ts / (2 * π)) 2 =
      ((∑ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) : ℝ) : ℂ) := by
  unfold kS kap
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun w hw => ?_
  have hp := (p_types (cos_star_ne hq hnv hts hw)).1
  simp only [cB]
  rw [pStar_eq]
  set P := Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I) /
      (1 + Complex.exp (2 * ((alw q a w + w * ts / 2 : ℝ) : ℂ) * I))
  have hc := cos_star_ne hq hnv hts hw
  have hc' : Complex.cos ((alw q a w + w * ts / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact_mod_cast hc
  push_cast at hp hc' ⊢
  norm_num [Nat.factorial]
  linear_combination (w : ℂ) ^ 2 * hp

end params

end ArcsAlgo.Core
