module

public import ArcsAlgo.EdgeShoulder
public import ArcsAlgo.EdgeSinc
public import ArcsAlgo.EdgeCoreV
set_option autoImplicit false

/-!
# Theorem E(2), the core with the vanishing factor, `𝒱(a/q) = {w₀}` (paper §3.5)

* `FW_split`, `one_add_ee_vanish`: `F_N = G·(1 + e(w₀θ))` and `1 + e(w₀θ) = −iw₀t·g(iw₀t)`, so
  `F_N = G̃·(−iw₀t)` with `G̃ = G·e^{iw₀t/2} sinc(w₀t/2)`.
* `kV`, `sV`, `GtV`, `HhatV`: the exact cumulants of `G̃` at `t*` (those of `G`, Proposition C, plus
  `λ_j = w₀^jψ^{(j)}(iw₀t*)`), `s̃* = √κ̃₂*`, `G̃(θ*)` and `Ĥ(T)` built from them (complex `z`).
* `FW_vanish_shift`, `Rcore_cv`, `vanish_identity`: the change of variables `θ = θ* + σ/(2π)`; the factor
  `−iw₀t` becomes `w₀·d/dT` (`hasDerivAt_HhatV`).
* `vanish_k2` (`κ̃₂*` real, `≥ N³/(512 log N)`), `vanish_k1im`, `vanish_alpha`, `vanish_expand`,
  `vanish_window`, `vanish_size`: the pieces of the proof.
* `thmE2_vanish`: `|∫_{|θ−θ*|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)·w₀·Ĥ′(T)| ≤
  |G(θ*)|(Ω N^{−3/2+2ε}/s̃* + w₀e^{−N^{2ε}/(16384 log N)})`, `Ω = w₀(|t*| + 1/s̃*)`, uniformly in `T`.

The only hypothesis is `SiegelWalfisz` (through Lemma W).
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- The weights whose factor does not vanish at `a/q`. -/
noncomputable def Wv (N q a : ℕ) : Finset ℕ := (WN N).filter (fun w => ¬ vanish q a w)

theorem Wv_sub (N q a : ℕ) : Wv N q a ⊆ WN N := filter_subset _ _

theorem vanish_filter_eq {q a N w₀ : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hw₀ : w₀ ∈ WN N)
    (hv : vanish q a w₀) : (WN N).filter (vanish q a) = {w₀} := by
  ext w; simp only [mem_filter, mem_singleton]; constructor
  · rintro ⟨hw, hvw⟩
    have h1 := vanish_eq hq ha (mem_filter.mp hw).2 hvw
    have h2 := vanish_eq hq ha (mem_filter.mp hw₀).2 hv
    omega
  · rintro rfl; exact ⟨hw₀, hv⟩

/-- `F_N = G·(1 + e(w₀θ))` when `𝒱(a/q) = {w₀}`. -/
theorem FW_split {q a N w₀ : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hw₀ : w₀ ∈ WN N) (hv : vanish q a w₀)
    (θ : ℝ) : FW (WN N) θ = Gw (WN N) q a θ * (1 + ee (w₀ * θ)) := by
  unfold FW Gw
  rw [← prod_filter_mul_prod_filter_not (WN N) (vanish q a) (f := fun w => 1 + ee (w * θ)),
    vanish_filter_eq hq ha hw₀ hv, prod_singleton]; ring

theorem ee_vanish {q a w₀ : ℕ} (hq : 1 ≤ q) (hv : vanish q a w₀) : ee (w₀ * ((a : ℝ) / q)) = -1 := by
  obtain ⟨c, hc⟩ := hv
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hc' : (2 * w₀ * a - q : ℝ) = 2 * q * c := by exact_mod_cast hc
  have e : (w₀ : ℝ) * ((a : ℝ) / q) = c + 1 / 2 := by field_simp; linarith
  rw [e]; unfold ee
  rw [show 2 * (π : ℂ) * I * (((c : ℝ) + 1 / 2 : ℝ) : ℂ) = (c : ℂ) * (2 * π * I) + π * I by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

/-- **The vanishing factor**: `1 + e(w₀(a/q + t/(2π))) = −iw₀t·g(iw₀t)`, `g(iw₀t) = e^{iw₀t/2} sinc(w₀t/2)`. -/
theorem one_add_ee_vanish {q a w₀ : ℕ} (hq : 1 ≤ q) (hv : vanish q a w₀) (t : ℝ) :
    1 + ee (w₀ * ((a : ℝ) / q + t / (2 * π))) = -(I * w₀ * t) * gS (I * w₀ * t) := by
  rw [mul_add, ee_add, ee_vanish hq hv, show (w₀ : ℝ) * (t / (2 * π)) = (w₀ * t) / (2 * π) by ring,
    ee_div_two_pi]
  have := mul_gS (I * w₀ * t)
  push_cast at this ⊢
  rw [show I * (w₀ * t) = I * w₀ * t by ring]
  linear_combination this

/-- The factors shifted from `θ*` (as `FW_shift`, any set of weights). -/
theorem prod_shift (W : Finset ℕ) (θs σ : ℝ) (hne : ∀ w ∈ W, 1 + ee (w * θs) ≠ 0) :
    ∏ w ∈ W, (1 + ee (w * (θs + σ / (2 * π)))) =
      (∏ w ∈ W, (1 + ee (w * θs))) * ∏ w ∈ W, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1)) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun w hw => ?_
  have e : ee (w * (θs + σ / (2 * π))) = ee (w * θs) * Complex.exp (I * w * σ) := by
    rw [mul_add, ee_add, show (w : ℝ) * (σ / (2 * π)) = (w * σ) / (2 * π) by ring, ee_div_two_pi]
    push_cast; ring_nf
  rw [e, factor_split (hne w hw)]; rfl

/-- The change of variables `θ = θ* + σ/(2π)` in the core integral. -/
theorem Rcore_cv (N : ℕ) (θs τ T : ℝ) :
    Rcore N θs τ T = ee (-(T * θs)) * ((1 / (2 * π) : ℂ) *
      ∫ σ in (-τ)..τ, FW (WN N) (θs + σ / (2 * π)) * Complex.exp (-(I * T * σ))) := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set g : ℝ → ℂ := fun θ => FW (WN N) θ * ee (-(T * θ)) with hg
  set h : ℝ → ℂ := fun σ => FW (WN N) (θs + σ / (2 * π)) * Complex.exp (-(I * T * σ)) with hh
  have hcv := intervalIntegral.integral_comp_add_div (f := g) (a := -τ) (b := τ) h2π θs
  have hpt : ∀ σ : ℝ, g (θs + σ / (2 * π)) = ee (-(T * θs)) * h σ := by
    intro σ
    simp only [hg, hh]
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
      (((2 * π : ℝ) : ℂ))⁻¹ * (ee (-(T * θs)) * ∫ σ in (-τ)..τ, h σ) := by
    rw [hcv]; field_simp
  rw [this]; push_cast; ring

/-! ### The objects of Theorem E(2) when `𝒱(a/q) = {w₀}` -/

/-- The cumulants of `G̃ = G·e^{iw₀t/2} sinc(w₀t/2)` at `t*`: those of `G` (Proposition C, weights `∉ 𝒱`)
plus those of the vanishing factor, `λ_j = w₀^jψ^{(j)}(iw₀t*)` (`j ≥ 1`). -/
noncomputable def kV (N q a w₀ : ℕ) (ts : ℝ) (j : ℕ) : ℂ :=
  kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) j + if j = 0 then 0 else lamS w₀ ts j

/-- `s̃* = √κ̃₂*` (`κ̃₂*` is real, `kV_two_real`). -/
noncomputable def sV (N q a w₀ : ℕ) (ts : ℝ) : ℝ := Real.sqrt (kV N q a w₀ ts 2).re

/-- `G̃(θ*) = G(θ*) e^{iw₀t*/2} sinc(w₀t*/2)`. -/
noncomputable def GtV (N q a w₀ : ℕ) (ts : ℝ) : ℂ :=
  Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π)) * gS (I * w₀ * ts)

/-- `Ĥ(T)` built from `G̃`: `e^{−iTt*} G̃(θ*) φ(z)/s̃*·(1 + κ̃₃He₃(z)/(6s̃*³) + κ̃₄He₄(z)/(24s̃*⁴) + κ̃₃²He₆(z)/(72s̃*⁶))`,
`z = (T − κ̃₁*)/s̃*` (complex). -/
noncomputable def HhatV (N q a w₀ : ℕ) (ts T : ℝ) : ℂ :=
  Complex.exp (-(I * T * ts)) * GtV N q a w₀ ts *
    mainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T

theorem hasDerivAt_HhatV {N q a w₀ : ℕ} {ts : ℝ} (hs : 0 < sV N q a w₀ ts) (T : ℝ) :
    HasDerivAt (fun T => HhatV N q a w₀ ts T)
      (Complex.exp (-(I * T * ts)) * GtV N q a w₀ ts *
        (-(I * ts) * mainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T +
          dmainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T)) T := by
  have he : HasDerivAt (fun T : ℝ => Complex.exp (-(I * T * ts))) (Complex.exp (-(I * T * ts)) * (-(I * ts))) T := by
    have h0 : HasDerivAt (fun T : ℝ => -(I * T * ts)) (-(I * ts)) T := by
      have := (hasDerivAt_ofReal T).const_mul (-(I * (ts : ℂ)))
      convert this using 1
      · ext y; ring
      · ring
    exact h0.cexp
  have := (he.mul_const (GtV N q a w₀ ts)).mul (hasDerivAt_mainEC hs (kV N q a w₀ ts 1) (kV N q a w₀ ts 3)
    (kV N q a w₀ ts 4) T)
  unfold HhatV
  convert this using 1; ring

/-- The rescaled integrand `f(σ) = Π_{w∉𝒱}(1 + p_w(e^{iwσ} − 1))·g(iw₀(t* + σ))/g(iw₀t*)`. -/
noncomputable def fV (N q a w₀ : ℕ) (ts σ : ℝ) : ℂ :=
  (∏ w ∈ Wv N q a, (1 + pStar ((a : ℝ) / q + ts / (2 * π)) w * (Complex.exp (I * w * σ) - 1))) *
    (gS (I * w₀ * ts + I * w₀ * σ) / gS (I * w₀ * ts))

theorem continuous_fV (N q a w₀ : ℕ) (ts : ℝ) : Continuous (fun σ => fV N q a w₀ ts σ) := by
  unfold fV
  have hg := differentiable_gS.continuous
  fun_prop

/-- `F_N(e(θ* + σ/(2π))) = G̃(θ*)·(−iw₀(t* + σ))·f(σ)`. -/
theorem FW_vanish_shift {q a N w₀ : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hw₀ : w₀ ∈ WN N)
    (hv : vanish q a w₀) {ts : ℝ} (hne : ∀ w ∈ Wv N q a, 1 + ee (w * ((a : ℝ) / q + ts / (2 * π))) ≠ 0)
    (hg0 : gS (I * w₀ * ts) ≠ 0) (σ : ℝ) :
    FW (WN N) ((a : ℝ) / q + ts / (2 * π) + σ / (2 * π)) =
      GtV N q a w₀ ts * (-(I * w₀ * (ts + σ))) * fV N q a w₀ ts σ := by
  rw [FW_split hq ha hw₀ hv]
  have h1 : Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π) + σ / (2 * π)) =
      Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π)) *
        ∏ w ∈ Wv N q a, (1 + pStar ((a : ℝ) / q + ts / (2 * π)) w * (Complex.exp (I * w * σ) - 1)) := by
    unfold Gw; exact prod_shift _ _ σ hne
  have h2 : 1 + ee (w₀ * ((a : ℝ) / q + ts / (2 * π) + σ / (2 * π))) =
      -(I * w₀ * (ts + σ)) * gS (I * w₀ * ts + I * w₀ * σ) := by
    rw [show (a : ℝ) / q + ts / (2 * π) + σ / (2 * π) = (a : ℝ) / q + (ts + σ) / (2 * π) by ring,
      one_add_ee_vanish (by omega) hv]
    push_cast; ring_nf
  rw [h1, h2]; unfold GtV fV
  set G := Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))
  set P := ∏ w ∈ Wv N q a, (1 + pStar ((a : ℝ) / q + ts / (2 * π)) w * (Complex.exp (I * w * σ) - 1))
  set m := -(I * (w₀ : ℂ) * (ts + σ))
  have e := mul_div_cancel₀ (gS (I * w₀ * ts + I * w₀ * σ)) hg0
  linear_combination (-(G * P * m)) * e

/-! ### At the peak -/

section peak

variable {N q a : ℕ} {ts : ℝ}

theorem cos_star_ge_v (hq : 3 ≤ q) {w : ℕ} (hvw : ¬ vanish q a w) (hwN : (w : ℝ) ≤ N)
    (hts : (N : ℝ) * |ts| ≤ 1 / q) : 1 / (2 * q) ≤ |Real.cos (π * (w * ((a : ℝ) / q + ts / (2 * π))))| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 := cos_lower (by omega : 1 ≤ q) hvw (a := a)
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

theorem pStar_le_v (hq : 3 ≤ q) {w : ℕ} (hw : w ∈ Wv N q a) (hts : (N : ℝ) * |ts| ≤ 1 / q) :
    1 + ee (w * ((a : ℝ) / q + ts / (2 * π))) ≠ 0 ∧ ‖pStar ((a : ℝ) / q + ts / (2 * π)) w‖ ≤ q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc := cos_star_ge_v hq (mem_filter.mp hw).2 (WN_le (mem_filter.mp hw).1) hts
  have hn := norm_one_add_ee (w * ((a : ℝ) / q + ts / (2 * π)))
  have hpos : 0 < ‖1 + ee (w * ((a : ℝ) / q + ts / (2 * π)))‖ := by
    rw [hn]; have : 0 < 1 / (2 * (q : ℝ)) := by positivity
    linarith
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  unfold pStar
  rw [norm_div, norm_ee, div_le_iff₀ hpos, hn]
  have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * q)
  rw [show 2 * (q : ℝ) * (1 / (2 * q)) = 1 by field_simp] at this
  linarith

theorem cos_star_ne_v (hq : 3 ≤ q) {w : ℕ} (hw : w ∈ Wv N q a) (hts : (N : ℝ) * |ts| ≤ 1 / q) :
    Real.cos (alw q a w + w * ts / 2) ≠ 0 := by
  have hc := cos_star_ge_v hq (mem_filter.mp hw).2 (WN_le (mem_filter.mp hw).1) hts
  rw [arg_eq q a w ts] at hc
  intro h0; rw [h0, abs_zero] at hc
  have : (0 : ℝ) < 1 / (2 * q) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  linarith

/-- `κ₁` of `G` at the peak is real: `Σ_{w∉𝒱} w/2`. -/
theorem kV_one_G (hq : 3 ≤ q) (hts : (N : ℝ) * |ts| ≤ 1 / q) (hF : Fw' (WN N) q a ts = 0) :
    kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) 1 = ((∑ w ∈ Wv N q a, (w : ℝ) / 2 : ℝ) : ℂ) := by
  have him := im_kappa1 (W := WN N) (q := q) (a := a) ts
  rw [hF, neg_zero] at him
  unfold kap
  have hterm : ∀ w ∈ Wv N q a, (w : ℂ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℂ) * cB (pStar ((a : ℝ) / q + ts / (2 * π)) w) 1 =
      (((w : ℝ) / 2 : ℝ) : ℂ) + I * (((w : ℝ) * (Real.tan (alw q a w + w * ts / 2) / 2) : ℝ) : ℂ) := by
    intro w hw
    have hp := (p_types (cos_star_ne_v hq hw hts)).2.2
    simp only [cB, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [pStar_eq]
    push_cast at hp ⊢
    linear_combination (w : ℂ) * hp
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum]
  unfold Wv; rw [him]
  push_cast; ring

/-- `κ₂` of `G` at the peak: `Σ_{w∉𝒱} w²/(4cos²(πwθ*))`. -/
theorem kV_two_G (hq : 3 ≤ q) (hts : (N : ℝ) * |ts| ≤ 1 / q) :
    kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) 2 =
      ((∑ w ∈ Wv N q a, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) : ℝ) : ℂ) := by
  unfold kap
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun w hw => ?_
  have hp := (p_types (cos_star_ne_v hq hw hts)).1
  simp only [cB]
  rw [pStar_eq]
  have hc := cos_star_ne_v hq hw hts
  have hc' : Complex.cos ((alw q a w + w * ts / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact_mod_cast hc
  push_cast at hp hc' ⊢
  norm_num [Nat.factorial]
  linear_combination (w : ℂ) ^ 2 * hp

theorem Ix_eq (w₀ : ℕ) (ts : ℝ) : I * (w₀ : ℂ) * ts = I * (((w₀ : ℝ) * ts : ℝ) : ℂ) := by push_cast; ring

theorem norm_gS_I_le (v : ℝ) : ‖gS (I * v)‖ ≤ 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gS_zero]
  have hv' : I * (v : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hv)
  rw [gS_of_ne hv', norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, div_le_one (by
    rw [Real.norm_eq_abs]; exact abs_pos.mpr hv)]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

end peak




/-! ### The pieces of the proof of `thmE2_vanish` -/

section split

variable {N q a w₀ : ℕ} {ts : ℝ}

theorem window_of {N q : ℕ} {ts : ℝ} (hq : 3 ≤ q) (hN : 1 ≤ N) (hts1 : (N : ℝ) * |ts| ≤ 1 / q) :
    |ts| < π / (q * N) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : |ts| ≤ 1 / (q * N) := by
    rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hq0] at hts1; linarith
  exact lt_of_le_of_lt this (div_lt_div_of_pos_right (by linarith [Real.two_le_pi]) (by positivity))

/-- `κ̃₂*` is real and `≥ N³/(512 log N)`. -/
theorem vanish_k2 (hq : 3 ≤ q) (hN : 1 ≤ N) (hts1 : (N : ℝ) * |ts| ≤ 1 / q)
    (hx₀ : (w₀ : ℝ) * |ts| ≤ 1 / 12) {L : ℝ}
    (hS2 : (N : ℝ) ^ 3 / (64 * L) ≤ S2W (WN N) q a) (hL0 : 0 < L)
    (h11 : 81 / 8 * (w₀ : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 / (512 * L)) :
    (kV N q a w₀ ts 2).im = 0 ∧ (N : ℝ) ^ 3 / (512 * L) ≤ (kV N q a w₀ ts 2).re := by
  have hw₀0 : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
  have hx₀6 : ‖I * (w₀ : ℂ) * ts‖ ≤ 1 / 6 := by rw [norm_Iwt]; linarith
  set X : ℝ := ∑ w ∈ Wv N q a, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) with hX
  have h2X : kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) 2 = (X : ℂ) := kV_two_G hq hts1
  have hXge : S2W (WN N) q a / 4 ≤ X :=
    kappa2_ge (W := WN N) (q := q) (a := a) (by omega) hN
      (fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)) (window_of hq hN hts1)
  set l2 := lamS w₀ ts 2 with hl2
  have hl2im : l2.im = 0 := by
    have := psiS_d2_real (v := (w₀ : ℝ) * ts) (by rw [abs_mul, abs_of_nonneg hw₀0]; linarith)
    simp only [hl2, lamS]
    rw [Ix_eq, show ((w₀ : ℂ)) ^ 2 = (((w₀ : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul, this,
      mul_zero]
  have hl2n : ‖l2‖ ≤ 81 / 8 * w₀ ^ 2 := by
    simp only [hl2, lamS]
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    have := norm_dpsiS_le 2 hx₀6
    calc (w₀ : ℝ) ^ 2 * ‖iteratedDeriv 2 psiS (I * w₀ * ts)‖ ≤
          (w₀ : ℝ) ^ 2 * ((Nat.factorial 2 : ℕ) * (9 / 16) * 3 ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 81 / 8 * w₀ ^ 2 := by norm_num [Nat.factorial]; ring
  have hkV2 : kV N q a w₀ ts 2 = (X : ℂ) + l2 := by
    unfold kV; rw [if_neg (by norm_num), h2X]
  have hl2re : -(81 / 8 * (w₀ : ℝ) ^ 2) ≤ l2.re := by
    have := Complex.abs_re_le_norm l2; have := abs_le.mp (this.trans hl2n); linarith
  refine ⟨by rw [hkV2]; simp [hl2im], ?_⟩
  rw [hkV2, Complex.add_re, Complex.ofReal_re]
  have : (N : ℝ) ^ 3 / (64 * L) / 4 = 2 * ((N : ℝ) ^ 3 / (512 * L)) := by field_simp; ring
  linarith

/-- `|Im κ̃₁*| ≤ N`: `κ₁` of `G` is real, `|Im λ₁| ≤ (81/4)w₀²|t*|`. -/
theorem vanish_k1im (hq : 3 ≤ q) (hts1 : (N : ℝ) * |ts| ≤ 1 / q) (hF : Fw' (WN N) q a ts = 0)
    (hx : (w₀ : ℝ) * |ts| ≤ 1 / 36) (hw₀N : (w₀ : ℝ) ≤ N) : |(kV N q a w₀ ts 1).im| ≤ N := by
  have hw₀0 : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
  have hx₀12 : ‖I * (w₀ : ℂ) * ts‖ ≤ 1 / 12 := by rw [norm_Iwt]; linarith
  have hG : (kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) 1).im = 0 := by
    rw [kV_one_G hq hts1 hF]; simp
  have e : (kV N q a w₀ ts 1).im = (lamS w₀ ts 1).im := by
    unfold kV; rw [if_neg (by norm_num), Complex.add_im, hG, zero_add]
  rw [e]
  have hd := dpsiS_near1 1 hx₀12
  rw [psiS_d1] at hd
  have hd' : ‖lamS w₀ ts 1 - w₀ / 2‖ ≤ w₀ * (81 / 4 * ‖I * (w₀ : ℂ) * ts‖) := by
    have : lamS w₀ ts 1 - w₀ / 2 = (w₀ : ℂ) * (iteratedDeriv 1 psiS (I * w₀ * ts) - 1 / 2) := by
      unfold lamS; ring
    rw [this, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hd.trans (le_of_eq (by norm_num))) hw₀0
  have him : (lamS w₀ ts 1).im = (lamS w₀ ts 1 - w₀ / 2).im := by simp
  rw [him]
  refine (Complex.abs_im_le_norm _).trans (hd'.trans ?_)
  rw [norm_Iwt]
  have : 81 / 4 * ((w₀ : ℝ) * |ts|) ≤ 1 := by nlinarith
  nlinarith

/-- The cumulants of order `3, 4, 5` and the remainder constant: `≤ A N^{j+1}`, `A = 8·8⁶q⁶`. -/
theorem vanish_alpha (hq : 3 ≤ q) (hN : 1 ≤ N) (hts1 : (N : ℝ) * |ts| ≤ 1 / q)
    (hx₀ : (w₀ : ℝ) * |ts| ≤ 1 / 6) (hw₀N : (w₀ : ℝ) ≤ N) :
    (∀ j : ℕ, 3 ≤ j → j ≤ 5 → ‖kV N q a w₀ ts j‖ / (Nat.factorial j : ℝ) ≤
        8 * 8 ^ 6 * (q : ℝ) ^ 6 * (N : ℝ) ^ (j + 1)) ∧
      2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ Wv N q a, (w : ℝ) ^ 6 + 4 ^ 6 * (w₀ : ℝ) ^ 6 ≤
        8 * 8 ^ 6 * (q : ℝ) ^ 6 * (N : ℝ) ^ 7 := by
  have hw₀0 : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx₀6 : ‖I * (w₀ : ℂ) * ts‖ ≤ 1 / 6 := by rw [norm_Iwt]; linarith
  have hpq : ∀ w ∈ Wv N q a, ‖pStar ((a : ℝ) / q + ts / (2 * π)) w‖ ≤ q := fun w hw =>
    (pStar_le_v hq hw hts1).2
  have hsumWv : ∀ j : ℕ, ∑ w ∈ Wv N q a, (w : ℝ) ^ j ≤ 2 * (N : ℝ) ^ (j + 1) := fun j =>
    (sum_le_sum_of_subset_of_nonneg (Wv_sub N q a) (fun _ _ _ => by positivity)).trans (sum_pow_WN hN j)
  have hq6 : (1 : ℝ) ≤ (q : ℝ) ^ 6 := one_le_pow₀ hq1
  refine ⟨fun j hj3 hj5 => ?_, ?_⟩
  · have hf : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have h := kap_le (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) hq1 hpq j
    have hl : ‖lamS w₀ ts j‖ ≤ (Nat.factorial j : ℝ) * 411 * (N : ℝ) ^ (j + 1) := by
      unfold lamS; rw [norm_mul, norm_pow, Complex.norm_natCast]
      have h1 := norm_dpsiS_le j hx₀6
      have h3 : (3 : ℝ) ^ j ≤ 3 ^ 5 := pow_le_pow_right₀ (by norm_num) hj5
      have hwj : (w₀ : ℝ) ^ j ≤ (N : ℝ) ^ j := pow_le_pow_left₀ hw₀0 hw₀N j
      have hNj : (N : ℝ) ^ j ≤ (N : ℝ) ^ (j + 1) := pow_le_pow_right₀ hN1 (by omega)
      calc (w₀ : ℝ) ^ j * ‖iteratedDeriv j psiS (I * w₀ * ts)‖ ≤
            (N : ℝ) ^ (j + 1) * ((Nat.factorial j : ℕ) * (9 / 16) * 3 ^ 5) :=
            mul_le_mul (hwj.trans hNj) (h1.trans (by gcongr)) (norm_nonneg _) (by positivity)
        _ ≤ (Nat.factorial j : ℝ) * 411 * (N : ℝ) ^ (j + 1) := by
            have : (0 : ℝ) ≤ (Nat.factorial j : ℕ) * (N : ℝ) ^ (j + 1) := by positivity
            norm_num; nlinarith
    have hkVj : kV N q a w₀ ts j = kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) j + lamS w₀ ts j := by
      unfold kV; rw [if_neg (by omega)]
    rw [div_le_iff₀ hf, hkVj]
    have hqj : (q : ℝ) ^ j ≤ (q : ℝ) ^ 6 := pow_le_pow_right₀ hq1 (by omega)
    calc ‖kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) j + lamS w₀ ts j‖ ≤
          ‖kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) j‖ + ‖lamS w₀ ts j‖ := norm_add_le _ _
      _ ≤ (Nat.factorial j : ℝ) * 25 * (q : ℝ) ^ 6 * (2 * (N : ℝ) ^ (j + 1)) +
            (Nat.factorial j : ℝ) * 411 * (N : ℝ) ^ (j + 1) := by
          gcongr
          exact h.trans (by gcongr; exact hsumWv j)
      _ ≤ 8 * 8 ^ 6 * (q : ℝ) ^ 6 * (N : ℝ) ^ (j + 1) * (Nat.factorial j : ℝ) := by
          have : (0 : ℝ) ≤ (N : ℝ) ^ (j + 1) * (Nat.factorial j : ℝ) := by positivity
          nlinarith
  · have hsum' : ∑ w ∈ Wv N q a, (w : ℝ) ^ 6 ≤ 2 * (N : ℝ) ^ 7 := hsumWv 6
    have h0 : (0 : ℝ) ≤ 2 * 8 ^ 6 * (q : ℝ) ^ 6 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsum' h0
    have hw6 : (w₀ : ℝ) ^ 6 ≤ (N : ℝ) ^ 7 :=
      (pow_le_pow_left₀ hw₀0 hw₀N 6).trans (pow_le_pow_right₀ hN1 (by norm_num))
    have hN7 : 0 ≤ (N : ℝ) ^ 7 := by positivity
    have h2 : (4 : ℝ) ^ 6 * (w₀ : ℝ) ^ 6 ≤ 4 * 8 ^ 6 * (q : ℝ) ^ 6 * (N : ℝ) ^ 7 := by nlinarith
    nlinarith

/-- **The expansion on the core**: `f(σ) = exp(Σ_{n≤5} κ̃_n(iσ)^n/n! + R)`, `|R| ≤ ρσ⁶`. -/
theorem vanish_expand (hq : 3 ≤ q) (hts1 : (N : ℝ) * |ts| ≤ 1 / q) (hx₀ : (w₀ : ℝ) * |ts| ≤ 1 / 6)
    (hw₀N : (w₀ : ℝ) ≤ N) {τ : ℝ} (hτ : 16 * q * N * τ ≤ 1) {σ : ℝ} (hσ : |σ| ≤ τ) :
    ∃ R : ℂ, ‖R‖ ≤ (2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ Wv N q a, (w : ℝ) ^ 6 + 4 ^ 6 * (w₀ : ℝ) ^ 6) * σ ^ 6 ∧
      fV N q a w₀ ts σ = Complex.exp (∑ n ∈ range 6, kV N q a w₀ ts n * (I * σ) ^ n / (Nat.factorial n : ℂ) + R) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hpq : ∀ w ∈ Wv N q a, ‖pStar ((a : ℝ) / q + ts / (2 * π)) w‖ ≤ q := fun w hw =>
    (pStar_le_v hq hw hts1).2
  have hWv : ∀ w ∈ Wv N q a, (w : ℝ) ≤ N := fun w hw => WN_le (Wv_sub N q a hw)
  have hx₀6 : ‖I * (w₀ : ℂ) * ts‖ ≤ 1 / 6 := by rw [norm_Iwt]; linarith
  have hτ0 : 0 ≤ τ := (abs_nonneg σ).trans hσ
  have hNτ : (N : ℝ) * τ ≤ 1 / 16 := by
    have : 16 * (N : ℝ) * τ ≤ 16 * q * N * τ := by
      have : 0 ≤ (N : ℝ) * τ := by positivity
      nlinarith
    linarith
  obtain ⟨R₁, hR₁, hP⟩ := prod_expand (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) hq1 hpq hWv hτ hσ
  have hz : ‖I * (w₀ : ℂ) * σ‖ ≤ 1 / 8 := by
    rw [norm_Iwt]
    have := mul_le_mul hw₀N hσ (abs_nonneg σ) (Nat.cast_nonneg N)
    linarith
  obtain ⟨R₂, hR₂, hg⟩ := gS_expand hx₀6 hz
  have hσ6 : |σ| ^ 6 = σ ^ 6 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  refine ⟨R₁ + R₂, ?_, ?_⟩
  · have h2' : ‖R₂‖ ≤ 4 ^ 6 * (w₀ : ℝ) ^ 6 * σ ^ 6 := by
      rw [norm_Iwt] at hR₂; refine hR₂.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, hσ6]; ring
    refine (norm_add_le _ _).trans ?_
    nlinarith
  · have hg0 : gS (I * (w₀ : ℂ) * ts) ≠ 0 := slitPlane_ne_zero (gS_slit (by linarith))
    simp only [fV]
    rw [hP, hg]
    rw [mul_div_cancel_left₀ _ hg0, ← Complex.exp_add]
    congr 1
    simp only [sum_range_succ, sum_range_zero, kV, lamS, iteratedDeriv_zero, Nat.factorial]
    simp
    push_cast
    ring

/-- **The identity**: `R_core − e(−Ta/q)w₀Ĥ′(T) = e(−Ta/q)e^{−iTt*}G̃(θ*)(J − w₀Z)`. -/
theorem vanish_identity (hq : 3 ≤ q) (ha : a.Coprime q) (hw₀ : w₀ ∈ WN N) (hv : vanish q a w₀)
    (hts1 : (N : ℝ) * |ts| ≤ 1 / q) (hx₀ : (w₀ : ℝ) * |ts| ≤ 1 / 6) (hs0 : 0 < sV N q a w₀ ts) (τ T : ℝ) :
    Rcore N ((a : ℝ) / q + ts / (2 * π)) τ T - ee (-(T * ((a : ℝ) / q))) *
        (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T) =
      ee (-(T * ((a : ℝ) / q))) * Complex.exp (-(I * T * ts)) * GtV N q a w₀ ts *
        ((1 / (2 * π) : ℂ) * (∫ σ in (-τ)..τ, (-(I * ((w₀ : ℝ) : ℂ) * (ts + σ))) * fV N q a w₀ ts σ *
          Complex.exp (-(I * T * σ))) - ((w₀ : ℝ) : ℂ) *
          (-(I * ts) * mainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T +
            dmainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T)) := by
  have hne : ∀ w ∈ Wv N q a, 1 + ee (w * ((a : ℝ) / q + ts / (2 * π))) ≠ 0 := fun w hw =>
    (pStar_le_v hq hw hts1).1
  have hg0 : gS (I * (w₀ : ℂ) * ts) ≠ 0 :=
    slitPlane_ne_zero (gS_slit (by rw [norm_Iwt]; linarith))
  have hee : ee (-(T * ((a : ℝ) / q + ts / (2 * π)))) = ee (-(T * ((a : ℝ) / q))) * Complex.exp (-(I * T * ts)) := by
    rw [show -(T * ((a : ℝ) / q + ts / (2 * π))) = -(T * ((a : ℝ) / q)) + (-(T * ts)) / (2 * π) by ring,
      ee_add, ee_div_two_pi]; push_cast; ring_nf
  have hder := (hasDerivAt_HhatV hs0 T).deriv
  have hpt : ∀ σ : ℝ, FW (WN N) ((a : ℝ) / q + ts / (2 * π) + σ / (2 * π)) * Complex.exp (-(I * T * σ)) =
      GtV N q a w₀ ts * ((-(I * ((w₀ : ℝ) : ℂ) * (ts + σ))) * fV N q a w₀ ts σ * Complex.exp (-(I * T * σ))) := by
    intro σ; rw [FW_vanish_shift hq ha hw₀ hv hne hg0 σ]; push_cast; ring
  rw [Rcore_cv, intervalIntegral.integral_congr (fun σ _ => hpt σ), intervalIntegral.integral_const_mul,
    hder, hee]
  push_cast; ring

end split

/-! ### The arithmetic of the window and of the error -/

/-- The window conditions `16qNτ ≤ 1` and `α₃τ³ + α₄τ⁴ + α₅τ⁵ + ρτ⁶ ≤ 1`. -/
theorem vanish_window {q L B ε τ A α3 α4 α5 ρ : ℝ} (hL0 : 0 < L) (hLone : 1 ≤ L) (hε0 : 0 < ε) (hε : ε < 1 / 8)
    (hq1 : 1 ≤ q) (hqL : q ≤ L ^ B) (hτe : τ = Real.exp ((-(3 / 2) + ε) * L))
    (hk2 : 16 * L ^ B ≤ Real.exp ((1 / 2 - ε) * √L)) (hk3 : 32 * 8 ^ 6 * L ^ (6 * B) ≤ Real.exp ((1 / 2 - 3 * ε) * √L))
    (hA : A = 8 * 8 ^ 6 * q ^ 6)
    (hα3 : α3 ≤ A * Real.exp (4 * L)) (hα4 : α4 ≤ A * Real.exp (5 * L)) (hα5 : α5 ≤ A * Real.exp (6 * L))
    (hρb : ρ ≤ A * Real.exp (7 * L)) :
    16 * q * Real.exp L * τ ≤ 1 ∧ α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 ≤ 1 := by
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hLB0 : 0 ≤ L ^ B := by positivity
  refine ⟨?_, ?_⟩
  · have h' : 16 * q ≤ Real.exp ((1 / 2 - ε) * L) :=
      (by nlinarith : 16 * q ≤ 16 * L ^ B).trans (hk2.trans (Real.exp_le_exp.mpr (by nlinarith)))
    have e : Real.exp L * τ = Real.exp ((-(1 / 2) + ε) * L) := by
      rw [hτe, ← Real.exp_add]; congr 1; ring
    have he : Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc 16 * q * Real.exp L * τ = 16 * q * (Real.exp L * τ) := by ring
      _ ≤ Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) := by
          rw [e]; exact mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = 1 := he
  · have hτk : ∀ k : ℕ, τ ^ k = Real.exp (k * ((-(3 / 2) + ε) * L)) := fun k => by
      rw [hτe, ← Real.exp_nat_mul]
    set E0 := Real.exp ((-(1 / 2) + 3 * ε) * L)
    have hA1 : 0 ≤ A := by rw [hA]; positivity
    have hterm : ∀ (u : ℝ) (j : ℕ), 3 ≤ j → u ≤ A * Real.exp ((j + 1) * L) → u * τ ^ j ≤ A * E0 := by
      intro u j hj hu
      rw [hτk]
      calc u * Real.exp (j * ((-(3 / 2) + ε) * L)) ≤ A * Real.exp ((j + 1) * L) * Real.exp (j * ((-(3 / 2) + ε) * L)) :=
            mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
        _ = A * Real.exp ((1 - j * (1 / 2 - ε)) * L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ A * E0 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA1
            have : (3 : ℝ) ≤ j := by exact_mod_cast hj
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr this) hε1.le) hL0.le]
    have t3 := hterm α3 3 le_rfl (by norm_num; exact hα3)
    have t4 := hterm α4 4 (by norm_num) (by norm_num; exact hα4)
    have t5 := hterm α5 5 (by norm_num) (by norm_num; exact hα5)
    have t6 := hterm ρ 6 (by norm_num) (by norm_num; exact hρb)
    have h4A : 4 * A * E0 ≤ 1 := by
      have hq6 : q ^ 6 ≤ L ^ (6 * B) := by
        rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
        exact pow_le_pow_left₀ (by linarith) hqL 6
      have h' : 4 * A ≤ Real.exp ((1 / 2 - 3 * ε) * L) := by
        rw [hA]
        calc 4 * (8 * 8 ^ 6 * q ^ 6) = 32 * 8 ^ 6 * q ^ 6 := by ring
          _ ≤ 32 * 8 ^ 6 * L ^ (6 * B) := by gcongr
          _ ≤ Real.exp ((1 / 2 - 3 * ε) * √L) := hk3
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
      have he : Real.exp ((1 / 2 - 3 * ε) * L) * E0 = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      nlinarith [Real.exp_pos ((-(1 / 2) + 3 * ε) * L)]
    linarith

set_option maxHeartbeats 4000000 in
/-- The size of the error of `core_intV` at `τ₀ = N^{−3/2+ε}`, `N = e^L`. -/
theorem vanish_size {q L B ε τ s ts w A α3 α4 α5 ρ : ℝ} (hB : 0 < B) (hL0 : 0 < L) (hLone : 1 ≤ L) (hε0 : 0 < ε)
    (hq1 : 1 ≤ q) (hqL : q ≤ L ^ B) (hτe : τ = Real.exp ((-(3 / 2) + ε) * L)) (hA : A = 8 * 8 ^ 6 * q ^ 6)
    (hα3 : α3 ≤ A * Real.exp (4 * L)) (hα4 : α4 ≤ A * Real.exp (5 * L)) (hα5 : α5 ≤ A * Real.exp (6 * L))
    (hρb : ρ ≤ A * Real.exp (7 * L)) (hα30 : 0 ≤ α3) (hα40 : 0 ≤ α4) (hα50 : 0 ≤ α5) (hρ0 : 0 ≤ ρ)
    (hsD : Real.exp (3 / 2 * L) / (32 * √L) ≤ s) (hs1 : 1 ≤ s) (hts : |ts| ≤ 1) (hw : 0 ≤ w)
    (hk4 : 48 * (8 * 8 ^ 6 * 32 ^ 6) ^ 3 * (LamE + LamE1) * L ^ (18 * B + 9) ≤ Real.exp (2 * ε * √L))
    (hk5 : (8 * 8 ^ 6 * 32 ^ 6) ^ 2 * (LamT3 + LamT4) * L ^ (12 * B + 6) ≤ Real.exp (1 * √L))
    (hk6 : 16384 * L ^ (3 / 2 : ℝ) ≤ Real.exp (2 * ε * √L)) :
    1 / (2 * π) * (w * (3 * (|ts| * EI α3 α4 α5 ρ s + EI1 α3 α4 α5 ρ s) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s))) ≤
      w * (|ts| + 1 / s) * (Real.exp ((-(3 / 2) + 2 * ε) * L) / s) +
        w * Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by
  set K₀ : ℝ := 8 * 8 ^ 6 * 32 ^ 6 with hK₀
  have hs0 : 0 < s := by linarith
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  set D := 32 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ q ^ 6 := one_le_pow₀ hq1; nlinarith
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
  set M := A * D ^ 6 with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [one_le_pow₀ (n := 6) hD1]
  set x := Real.exp (-(1 / 2) * L) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hxk : ∀ k : ℕ, x ^ k = Real.exp (-(k / 2 : ℝ) * L) := fun k => by
    rw [hx, ← Real.exp_nat_mul]; congr 1; ring
  have b3 : α3 / s ^ 3 ≤ M * x := by
    have := norm_cum (k := 3) (by norm_num) (by linarith) hD1 hα3 hsD
    rw [hx]; convert this using 2; push_cast; ring_nf
  have b4 : α4 / s ^ 4 ≤ M * x ^ 2 := by
    have := norm_cum (k := 4) (by norm_num) (by linarith) hD1 hα4 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have b5 : α5 / s ^ 5 ≤ M * x ^ 3 := by
    have := norm_cum (k := 5) (by norm_num) (by linarith) hD1 hα5 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have br : ρ / s ^ 6 ≤ M * x ^ 4 := by
    have := norm_cum (k := 6) (by norm_num) (by linarith) hD1 hρb hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have hEI := EI_le hs0 hα30 hα40 hα50 hρ0 hM1 hx0 hx1 b3 b4 b5 br
  have hEI1 := EI1_le hs0 hα30 hα40 hα50 hρ0 hM1 hx0 hx1 b3 b4 b5 br
  have hTI := TIs_le hs0 hα30 hα40 hM1 (b3.trans (by nlinarith))
    (b4.trans (by nlinarith [pow_le_one₀ hx0 hx1 (n := 2)]))
  have hMle : M ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hM, hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : q ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hpow : ∀ k : ℕ, (L ^ (6 * B) * L ^ 3) ^ k = L ^ ((6 * B + 3) * k) := by
    intro k
    have h63 : L ^ (6 * B) * L ^ 3 = L ^ (6 * B + 3) := by
      rw [Real.rpow_add hL0, show L ^ (3 : ℝ) = L ^ 3 by norm_cast]
    rw [h63, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hLamE : 0 ≤ LamE := sum_nonneg fun i _ => Am_nonneg _
  have hLamE1 : 0 ≤ LamE1 := sum_nonneg fun i _ => Am_nonneg _
  have hLamT3 : 0 ≤ LamT3 := by
    unfold LamT3; have := Am_nonneg 0; have := Am_nonneg 3; have := Am_nonneg 4; have := Am_nonneg 6; positivity
  have hLamT4 : 0 ≤ LamT4 := by
    unfold LamT4; have := Am_nonneg 1; have := Am_nonneg 4; have := Am_nonneg 5; have := Am_nonneg 7; positivity
  have hM3 : 48 * M ^ 3 * (LamE + LamE1) ≤ Real.exp (2 * ε * L) := by
    have e : L ^ (18 * B + 9) = (L ^ (6 * B) * L ^ 3) ^ 3 := by rw [hpow]; congr 1; push_cast; ring
    have hm3 : M ^ 3 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 := pow_le_pow_left₀ hM0 (by linarith) 3
    calc 48 * M ^ 3 * (LamE + LamE1) ≤ 48 * (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 * (LamE + LamE1) := by gcongr
      _ = 48 * K₀ ^ 3 * (LamE + LamE1) * L ^ (18 * B + 9) := by rw [e]; ring
      _ ≤ Real.exp (2 * ε * √L) := hk4
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hM2 : M ^ 2 * (LamT3 + LamT4) ≤ Real.exp (√L) := by
    have e : L ^ (12 * B + 6) = (L ^ (6 * B) * L ^ 3) ^ 2 := by rw [hpow]; congr 1; push_cast; ring
    have hm2 : M ^ 2 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 := pow_le_pow_left₀ hM0 (by linarith) 2
    calc M ^ 2 * (LamT3 + LamT4) ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 * (LamT3 + LamT4) := by gcongr
      _ = K₀ ^ 2 * (LamT3 + LamT4) * L ^ (12 * B + 6) := by rw [e]; ring
      _ ≤ Real.exp (1 * √L) := hk5
      _ = _ := by rw [one_mul]
  set NE := Real.exp ((-(3 / 2) + 2 * ε) * L) with hNE
  have hNEx : NE = x ^ 3 * Real.exp (2 * ε * L) := by
    rw [hNE, hxk, ← Real.exp_add]; congr 1; push_cast; ring
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hpart1 : 3 * EI α3 α4 α5 ρ s ≤ NE / s := by
    have : 3 * (16 * (M ^ 3 * x ^ 3) * LamE / s) ≤ NE / s := by
      rw [show 3 * (16 * (M ^ 3 * x ^ 3) * LamE / s) = (48 * M ^ 3 * LamE) * x ^ 3 / s by ring,
        div_le_div_iff_of_pos_right hs0, hNEx]
      have : 48 * M ^ 3 * LamE ≤ Real.exp (2 * ε * L) := by nlinarith [pow_nonneg hM0 3]
      nlinarith
    linarith
  have hpart1' : 3 * EI1 α3 α4 α5 ρ s ≤ NE / s ^ 2 := by
    have : 3 * (16 * (M ^ 3 * x ^ 3) * LamE1 / s ^ 2) ≤ NE / s ^ 2 := by
      rw [show 3 * (16 * (M ^ 3 * x ^ 3) * LamE1 / s ^ 2) = (48 * M ^ 3 * LamE1) * x ^ 3 / s ^ 2 by ring,
        div_le_div_iff_of_pos_right (by positivity), hNEx]
      have : 48 * M ^ 3 * LamE1 ≤ Real.exp (2 * ε * L) := by nlinarith [pow_nonneg hM0 3]
      nlinarith
    linarith
  -- the tail
  have hE2 : Real.exp (2 * ε * L) / (1024 * L) ≤ s ^ 2 * τ ^ 2 := by
    have h1' : (Real.exp (3 / 2 * L) / D) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 * τ ^ 2 = Real.exp (2 * ε * L) / (1024 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hτe, ← Real.exp_nat_mul,
        div_mul_eq_mul_div, ← Real.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right h1' (by positivity)
  have hTIs0 : 0 ≤ TIs α3 α4 s := by
    unfold TIs; have := Am_nonneg 0; have := Am_nonneg 3; have := Am_nonneg 4; have := Am_nonneg 6
    positivity
  have hTIs10 : 0 ≤ TIs1 α3 α4 s := by
    unfold TIs1; have := Am_nonneg 1; have := Am_nonneg 4; have := Am_nonneg 5; have := Am_nonneg 7
    positivity
  have hpart2 : Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s) ≤
      Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by
    set E := Real.exp (2 * ε * L)
    have hL32 : L ^ (3 / 2 : ℝ) = L * √L := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL0, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hL32] at hk6
    have hsqE : √L ≤ E / (16384 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 16384 * (L * √L) ≤ E := hk6.trans (Real.exp_le_exp.mpr (by nlinarith))
      linarith
    have hTs : |ts| * TIs α3 α4 s + TIs1 α3 α4 s ≤ M ^ 2 * (LamT3 + LamT4) := by
      have t1 : TIs α3 α4 s ≤ M ^ 2 * LamT3 := hTI.1.trans (by
        rw [div_le_iff₀ hs0]; have : 0 ≤ M ^ 2 * LamT3 := by positivity
        nlinarith)
      have t2 : TIs1 α3 α4 s ≤ M ^ 2 * LamT4 := hTI.2.trans (by
        rw [div_le_iff₀ (by positivity)]; have : 0 ≤ M ^ 2 * LamT4 := by positivity
        nlinarith [one_le_pow₀ (n := 2) hs1])
      have : |ts| * TIs α3 α4 s ≤ TIs α3 α4 s := mul_le_of_le_one_left hTIs0 hts
      nlinarith
    have hTs0 : 0 ≤ |ts| * TIs α3 α4 s + TIs1 α3 α4 s := by positivity
    calc Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s)
        ≤ Real.exp (-(E / (1024 * L)) / 8) * (M ^ 2 * (LamT3 + LamT4)) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hTs hTs0 (Real.exp_pos _).le
      _ ≤ Real.exp (-(E / (1024 * L)) / 8) * Real.exp (E / (16384 * L)) := by
          gcongr; exact hM2.trans (Real.exp_le_exp.mpr hsqE)
      _ = Real.exp (-E / (16384 * L)) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
  have h2pi : 1 / (2 * π) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hEI0 : 0 ≤ EI α3 α4 α5 ρ s := by
    unfold EI; exact sum_nonneg fun i _ => by
      have := ebC_nonneg hα30 hα40 hα50 hρ0 i; have := Am_nonneg (ebM i); positivity
  have hEI10 : 0 ≤ EI1 α3 α4 α5 ρ s := by
    unfold EI1; exact sum_nonneg fun i _ => by
      have := ebC_nonneg hα30 hα40 hα50 hρ0 i; have := Am_nonneg (ebM i + 1); positivity
  have hbig : 0 ≤ w * (3 * (|ts| * EI α3 α4 α5 ρ s + EI1 α3 α4 α5 ρ s) +
      Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s)) := by positivity
  calc 1 / (2 * π) * (w * (3 * (|ts| * EI α3 α4 α5 ρ s + EI1 α3 α4 α5 ρ s) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s)))
      ≤ 1 * (w * (3 * (|ts| * EI α3 α4 α5 ρ s + EI1 α3 α4 α5 ρ s) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s))) :=
        mul_le_mul_of_nonneg_right h2pi hbig
    _ ≤ w * (|ts| * (NE / s) + NE / s ^ 2 + Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L))) := by
        rw [one_mul]
        refine mul_le_mul_of_nonneg_left ?_ hw
        have := mul_le_mul_of_nonneg_left hpart1 (abs_nonneg ts)
        nlinarith
    _ = _ := by field_simp
set_option maxHeartbeats 8000000 in
/-- **Theorem E(2), the core, `𝒱(a/q) = {w₀}`** (paper §3.5): fix `B > 0` and `0 < ε < 1/8`, put
`τ₀ = N^{−3/2+ε}`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, the vanishing weight `w₀`, every critical point
`t*` of `log|G|` with `|t*| ≤ 4|ν|/S₂` (the peak of Lemma W; `θ*` stays the peak of `|G|`) and every `T`:
`|∫_{|θ−θ*|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)·w₀·(d/dT)Ĥ(T)| ≤ |G(θ*)|(Ω N^{−3/2+2ε}/s̃* + w₀e^{−N^{2ε}/(16384 log N)})`,
`Ω = w₀(|t*| + 1/s̃*)`, where `Ĥ` is built from `G̃ = G·e^{iw₀t/2} sinc(w₀t/2)` with its exact cumulants at `t*`
(`kV`; `κ̃₂*` is real and `s̃*² = κ̃₂*`). Also `w₀|t*| ≤ 1/12` and `w₀²|t*| ≤ 1`, so `lamS_close` applies.
The only hypothesis is Siegel–Walfisz (through Lemma W). -/
theorem thmE2_vanish (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ w₀ ∈ WN N, vanish q a w₀ → ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a →
      Fw' (WN N) q a ts = 0 →
        (w₀ : ℝ) * |ts| ≤ 1 / 12 ∧ (w₀ : ℝ) ^ 2 * |ts| ≤ 1 ∧ (kV N q a w₀ ts 2).im = 0 ∧
        0 < sV N q a w₀ ts ∧ (((sV N q a w₀ ts) ^ 2 : ℝ) : ℂ) = kV N q a w₀ ts 2 ∧
        ∀ T : ℝ,
        ‖Rcore N ((a : ℝ) / q + ts / (2 * π)) ((N : ℝ) ^ (-(3 / 2 : ℝ) + ε)) T -
            ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
          ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
            (w₀ * (|ts| + 1 / sV N q a w₀ ts) * ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sV N q a w₀ ts) +
              w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N))) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  have hLamE : 0 ≤ LamE := sum_nonneg fun i _ => Am_nonneg _
  have hLamE1 : 0 ≤ LamE1 := sum_nonneg fun i _ => Am_nonneg _
  have hLamT : 0 ≤ LamT3 + LamT4 := by
    unfold LamT3 LamT4
    have := Am_nonneg 0; have := Am_nonneg 1; have := Am_nonneg 3; have := Am_nonneg 4
    have := Am_nonneg 5; have := Am_nonneg 6; have := Am_nonneg 7; positivity
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp B hc 12
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (6 * B) hε3 (32 * 8 ^ 6)
  obtain ⟨K₄, hK₄, hk4⟩ := ev_poly_exp (18 * B + 9) (by positivity : 0 < 2 * ε) (48 * (8 * 8 ^ 6 * 32 ^ 6) ^ 3 * (LamE + LamE1))
  obtain ⟨K₅, hK₅, hk5⟩ := ev_poly_exp (12 * B + 6) one_pos ((8 * 8 ^ 6 * 32 ^ 6) ^ 2 * (LamT3 + LamT4))
  obtain ⟨K₆, hK₆, hk6⟩ := ev_poly_exp (3 / 2) (by positivity : 0 < 2 * ε) 16384
  obtain ⟨K₇, hK₇, hk7⟩ := ev_poly_exp 1 one_pos 5632
  obtain ⟨K₈, hK₈, hk8⟩ := ev_poly_exp 1 (by norm_num : (0 : ℝ) < 1 / 2) 2048
  set Kmax := max (max (max K₁ K₂) (max K₃ K₄)) (max (max K₅ K₆) (max K₇ K₈))
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha w₀ hw₀ hv ts hts hF => ?_⟩
  obtain ⟨-, hS2pos, hwin, hrat, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL4 : K₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL5 : K₅ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL6 : K₆ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL7 : K₇ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hL8 : K₈ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hnp : ∀ k : ℕ, Nr ^ k = Real.exp (k * L) := fun k => by rw [← hexpL, ← Real.exp_nat_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  -- `N|t*| ≤ 1/(12q)`
  have hts' : Nr * |ts| ≤ 1 / (12 * q) := by
    have h1 : Nr * |ts| ≤ Real.exp (-c * √L) := by
      have := hts.trans hrat; rw [le_div_iff₀ hNpos] at this; linarith
    have h2 : 12 * (q : ℝ) * Real.exp (-c * √L) ≤ 1 := by
      have := hk1 L hL1
      have he : Real.exp (c * √L) * Real.exp (-c * √L) = 1 := by rw [← Real.exp_add]; simp
      calc 12 * (q : ℝ) * Real.exp (-c * √L) ≤ Real.exp (c * √L) * Real.exp (-c * √L) :=
            mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
        _ = 1 := he
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-c * √L)]
  have hts1 : Nr * |ts| ≤ 1 / q := hts'.trans (by
    rw [div_le_div_iff₀ (by positivity) hq0]; nlinarith)
  have hw₀N : (w₀ : ℝ) ≤ Nr := WN_le hw₀
  have hw₀q : (w₀ : ℝ) ≤ q := by
    have := vanish_eq hq ha (mem_filter.mp hw₀).2 hv
    have : (2 * w₀ : ℝ) = q := by exact_mod_cast this
    have : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
    linarith
  have hw₀0 : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
  have hwts : (w₀ : ℝ) * |ts| ≤ 1 / (12 * q) :=
    (mul_le_mul_of_nonneg_right hw₀N (abs_nonneg ts)).trans hts'
  have hwts12 : (w₀ : ℝ) * |ts| ≤ 1 / 36 := hwts.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hwts2 : (w₀ : ℝ) ^ 2 * |ts| ≤ 1 := by
    have : (w₀ : ℝ) ^ 2 * |ts| = w₀ * (w₀ * |ts|) := by ring
    rw [this]
    calc (w₀ : ℝ) * (w₀ * |ts|) ≤ q * (1 / (12 * q)) :=
          mul_le_mul hw₀q hwts (by positivity) hq0.le
      _ ≤ 1 := by rw [show (q : ℝ) * (1 / (12 * q)) = 1 / 12 by field_simp]; norm_num
  set x₀ : ℂ := I * w₀ * ts with hx₀def
  have hx₀ : ‖x₀‖ = w₀ * |ts| := norm_Iwt w₀ ts
  have hx₀6 : ‖x₀‖ ≤ 1 / 6 := by rw [hx₀]; linarith
  have hx₀12 : ‖x₀‖ ≤ 1 / 12 := by rw [hx₀]; linarith
  have hg0 : gS x₀ ≠ 0 := slitPlane_ne_zero (gS_slit (by linarith))
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  have hpar := fun w (hw : w ∈ Wv N q a) => pStar_le_v hq hw hts1
  have hne : ∀ w ∈ Wv N q a, 1 + ee (w * θs) ≠ 0 := fun w hw => (hpar w hw).1
  have hpq : ∀ w ∈ Wv N q a, ‖pStar θs w‖ ≤ q := fun w hw => (hpar w hw).2
  have hWv : ∀ w ∈ Wv N q a, (w : ℝ) ≤ Nr := fun w hw => WN_le (Wv_sub N q a hw)
  have htsw : |ts| < π / (q * Nr) := by
    have : |ts| ≤ 1 / (q * Nr) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at hts1; linarith
    exact lt_of_le_of_lt this (div_lt_div_of_pos_right (by linarith [Real.two_le_pi]) (by positivity))
  have hN1 : 1 ≤ N := by omega
  -- `κ̃₂` and `s̃`
  have h11 : 81 / 8 * (w₀ : ℝ) ^ 2 ≤ Nr ^ 3 / (512 * L) := by
    have h7 := hk7 L hL7; rw [Real.rpow_one] at h7
    have hN7 : 5632 * L ≤ Nr := h7.trans (by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
    rw [le_div_iff₀ (by positivity)]
    have : (w₀ : ℝ) ^ 2 ≤ Nr ^ 2 := pow_le_pow_left₀ hw₀0 hw₀N 2
    nlinarith [mul_le_mul_of_nonneg_left hN7 (by positivity : (0 : ℝ) ≤ Nr ^ 2)]
  obtain ⟨hkV2im, hre⟩ := vanish_k2 (a := a) hq hN1 hts1 (by linarith) hS2lo hL0 h11
  have hre0 : 0 < (kV N q a w₀ ts 2).re := lt_of_lt_of_le (by positivity) hre
  set s := sV N q a w₀ ts with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hre0
  have hs2 : s ^ 2 = (kV N q a w₀ ts 2).re := Real.sq_sqrt hre0.le
  have h2 : kV N q a w₀ ts 2 = ((s ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, hs2]
    · rw [Complex.ofReal_im, hkV2im]
  set D := 32 * √L with hD
  have hsD : Real.exp (3 / 2 * L) / D ≤ s := by
    rw [hsdef]; unfold sV
    rw [Real.le_sqrt (by positivity) hre0.le]
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 = Nr ^ 3 / (1024 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hnp 3]
      congr 1; push_cast; ring_nf; ring
    rw [e]
    have : Nr ^ 3 / (1024 * L) ≤ Nr ^ 3 / (512 * L) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
    linarith
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ hsD
    rw [le_div_iff₀ (by positivity), one_mul, hD]
    have h7 := hk7 L hL7; rw [Real.rpow_one] at h7
    calc 32 * √L ≤ 5632 * L := by nlinarith
      _ ≤ Real.exp (1 * √L) := h7
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hk0 : kV N q a w₀ ts 0 = 0 := by unfold kV; simp [kap, cB]
  set k1 := kV N q a w₀ ts 1 with hk1def
  have hk1im : |k1.im| ≤ Nr := vanish_k1im hq hts1 hF hwts12 hw₀N
  -- the cumulants of order 3, 4, 5 and the remainder
  obtain ⟨hαN, hρN⟩ := vanish_alpha (a := a) hq hN1 hts1 (by linarith) hw₀N
  set A : ℝ := 8 * 8 ^ 6 * (q : ℝ) ^ 6 with hA
  set α3 := ‖kV N q a w₀ ts 3‖ / 6
  set α4 := ‖kV N q a w₀ ts 4‖ / 24
  set α5 := ‖kV N q a w₀ ts 5‖ / 120
  set ρ := 2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ Wv N q a, (w : ℝ) ^ 6 + 4 ^ 6 * (w₀ : ℝ) ^ 6 with hρ
  have hα3 : α3 ≤ A * Real.exp (4 * L) := by
    have := hαN 3 le_rfl (by norm_num); norm_num [Nat.factorial] at this; rw [hnp] at this; norm_num at this
    exact this
  have hα4 : α4 ≤ A * Real.exp (5 * L) := by
    have := hαN 4 (by norm_num) (by norm_num); norm_num [Nat.factorial] at this; rw [hnp] at this
    norm_num at this; exact this
  have hα5 : α5 ≤ A * Real.exp (6 * L) := by
    have := hαN 5 (by norm_num) le_rfl; norm_num [Nat.factorial] at this; rw [hnp] at this
    norm_num at this; exact this
  have hρb : ρ ≤ A * Real.exp (7 * L) := by
    have := hρN; rw [hnp] at this; norm_num at this; exact this
  have hα30 : 0 ≤ α3 := by positivity
  have hα40 : 0 ≤ α4 := by positivity
  have hα50 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  -- the window
  set τ := Nr ^ (-(3 / 2 : ℝ) + ε) with hτdef
  have hτe : τ = Real.exp ((-(3 / 2) + ε) * L) := hrp _
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
  obtain ⟨hτ', hy⟩ := vanish_window hL0 hLone hε0 hε hq1 hqL hτe (hk2 L hL2) (hk3 L hL3) hA hα3 hα4 hα5 hρb
  rw [hexpL] at hτ'
  have hexpf : ∀ σ : ℝ, |σ| ≤ τ → ∃ R : ℂ, ‖R‖ ≤ ρ * σ ^ 6 ∧
      fV N q a w₀ ts σ = Complex.exp (∑ n ∈ range 6, kV N q a w₀ ts n * (I * σ) ^ n / (Nat.factorial n : ℂ) + R) :=
    fun σ hσ => vanish_expand hq hts1 (by linarith) hw₀N hτ' hσ
  -- the conditions on `κ̃₁`
  have hNNτ : 2048 * L ≤ Nr * Nr * τ := by
    have h8 := hk8 L hL8; rw [Real.rpow_one] at h8
    have e : Nr * Nr * τ = Real.exp ((1 / 2 + ε) * L) := by
      rw [hτe, ← hexpL, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]; refine h8.trans (Real.exp_le_exp.mpr ?_); nlinarith
  have hNτ : Nr * τ ≤ 1 / 16 := by
    have : 16 * Nr * τ ≤ 16 * q * Nr * τ := by nlinarith [mul_pos hNpos hτ0]
    linarith
  have hyτ : |k1.im| * τ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hk1im hτ0.le; linarith
  have hyt : |k1.im| ≤ s ^ 2 * τ / 4 := by
    rw [hs2]
    have h1 : Nr ^ 3 / (512 * L) * τ / 4 ≤ (kV N q a w₀ ts 2).re * τ / 4 := by
      have := mul_le_mul_of_nonneg_right hre hτ0.le; linarith
    have h2' : Nr ≤ Nr ^ 3 / (512 * L) * τ / 4 := by
      rw [show Nr ^ 3 / (512 * L) * τ / 4 = Nr * (Nr * Nr * τ) / (2048 * L) by ring, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hts1' : |ts| ≤ 1 := by
    have : |ts| ≤ Nr * |ts| := le_mul_of_one_le_left (abs_nonneg _) (by linarith)
    have : 1 / (12 * (q : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  refine ⟨by linarith, hwts2, hkV2im, hs0, h2.symm, fun T => ?_⟩
  have hcore := core_intV (fV N q a w₀ ts) (continuous_fV N q a w₀ ts) (kV N q a w₀ ts) (k1 := k1) (ts := ts)
    hs0 hτ0 hρ0 hw₀0 hk0 rfl h2 hexpf hy hyτ hyt T
  rw [vanish_identity hq ha hw₀ hv hts1 (by linarith) hs0 τ T, norm_mul, norm_mul, norm_mul, norm_ee,
    norm_cexp_IT, one_mul, one_mul]
  have hGt : ‖GtV N q a w₀ ts‖ ≤ ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ := by
    unfold GtV; rw [norm_mul, Ix_eq]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gS_I_le _)
  refine mul_le_mul hGt (hcore.trans ?_) (norm_nonneg _) (norm_nonneg _)
  have hsz := vanish_size hB hL0 hLone hε0 hq1 hqL hτe hA hα3 hα4 hα5 hρb hα30 hα40 hα50 hρ0 hsD hs1 hts1'
    hw₀0 (hk4 L hL4) (hk5 L hL5) (hk6 L hL6)
  rw [hrp (-(3 / 2) + 2 * ε), hrp (2 * ε)]
  exact hsz

end ArcsAlgo.Core
