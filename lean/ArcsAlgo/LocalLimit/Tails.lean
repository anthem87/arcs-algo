module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false

/-!
# Gaussian tails (paper §6.2, proof of Lemma B0′)

`integral_Ioi_exp_le`: `∫_{θ₀}^∞ e^{−aθ²} ≤ e^{−aθ₀²}/(2aθ₀)`, and
`integral_Ioi_pow_four_exp_le`: `∫_{θ₀}^∞ θ⁴e^{−aθ²} ≤ e^{−aθ₀²}(θ₀³/(2a) + 3θ₀/(4a²) + 3/(8a³θ₀))`.
Both come from an explicit antiderivative whose derivative dominates the integrand:
`−(e^{−aθ²}/(2aθ))′ = e^{−aθ²}(1 + 1/(2aθ²))` and
`−(e^{−aθ²}(θ³/(2a) + 3θ/(4a²) + 3/(8a³θ)))′ = e^{−aθ²}(θ⁴ + 3/(8a³θ²))`.
-/

open Real MeasureTheory Set Filter Topology

@[expose] public section

namespace ArcsAlgo.LLT

lemma tendsto_sq_rpow_mul_exp (s : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun θ : ℝ => (θ ^ 2) ^ s * Real.exp (-a * θ ^ 2)) atTop (𝓝 0) :=
  (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s a ha).comp
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))

lemma sq_rpow_half_nat {θ : ℝ} (hθ : 0 < θ) (n : ℕ) : (θ ^ 2) ^ ((n : ℝ) / 2) = θ ^ n := by
  rw [← Real.rpow_natCast θ 2, ← Real.rpow_mul hθ.le, ← Real.rpow_natCast]
  congr 1; push_cast; ring

lemma sq_rpow_neg_half {θ : ℝ} (hθ : 0 < θ) : (θ ^ 2) ^ (-(1 : ℝ) / 2) = θ⁻¹ := by
  rw [← Real.rpow_natCast θ 2, ← Real.rpow_mul hθ.le]
  norm_num; exact Real.rpow_neg_one θ

lemma tendsto_pow_mul_exp {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun θ : ℝ => θ ^ n * Real.exp (-a * θ ^ 2)) atTop (𝓝 0) :=
  (tendsto_sq_rpow_mul_exp ((n : ℝ) / 2) ha).congr' (by
    filter_upwards [eventually_gt_atTop 0] with θ hθ; rw [sq_rpow_half_nat hθ])

lemma tendsto_inv_mul_exp {a : ℝ} (ha : 0 < a) :
    Tendsto (fun θ : ℝ => θ⁻¹ * Real.exp (-a * θ ^ 2)) atTop (𝓝 0) :=
  (tendsto_sq_rpow_mul_exp (-(1 : ℝ) / 2) ha).congr' (by
    filter_upwards [eventually_gt_atTop 0] with θ hθ; rw [sq_rpow_neg_half hθ])

lemma integrableOn_pow_mul_exp {a : ℝ} (ha : 0 < a) (n : ℕ) (S : Set ℝ) :
    IntegrableOn (fun θ : ℝ => θ ^ n * Real.exp (-a * θ ^ 2)) S := by
  have h := integrable_rpow_mul_exp_neg_mul_sq ha (s := n) (by
    have := n.cast_nonneg (α := ℝ); linarith)
  simp_rw [Real.rpow_natCast] at h
  exact h.integrableOn

lemma integrableOn_exp_div_sq {a θ0 : ℝ} (ha : 0 < a) (h0 : 0 < θ0) :
    IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2) / θ ^ 2) (Ioi θ0) := by
  have hb : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2) / θ0 ^ 2) (Ioi θ0) :=
    ((integrable_exp_neg_mul_sq ha).div_const _).integrableOn
  refine hb.mono' ((by fun_prop : Measurable fun θ : ℝ =>
    Real.exp (-a * θ ^ 2) / θ ^ 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
  rw [Real.norm_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ h0.le (le_of_lt hθ) 2

/-- `∫_{θ₀}^∞ e^{−aθ²} ≤ e^{−aθ₀²}/(2aθ₀)`. -/
lemma integral_Ioi_exp_le {a θ0 : ℝ} (ha : 0 < a) (h0 : 0 < θ0) :
    ∫ θ in Ioi θ0, Real.exp (-a * θ ^ 2) ≤ Real.exp (-a * θ0 ^ 2) / (2 * a * θ0) := by
  set G : ℝ → ℝ := fun θ => Real.exp (-a * θ ^ 2) / (2 * a * θ)
  set g : ℝ → ℝ := fun θ => Real.exp (-a * θ ^ 2) + Real.exp (-a * θ ^ 2) / θ ^ 2 / (2 * a)
  have hderiv : ∀ x ∈ Ioi θ0, HasDerivAt (fun θ => -G θ) (g x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans h0 hx
    have h1 : HasDerivAt (fun θ : ℝ => Real.exp (-a * θ ^ 2)) (Real.exp (-a * x ^ 2) * (-a * (2 * x))) x := by
      have := ((hasDerivAt_pow 2 x).const_mul (-a)).exp
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun θ : ℝ => 2 * a * θ) (2 * a) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * a)
    have := (h1.div h2 (by positivity)).neg
    convert this using 1
    simp only [g]; field_simp; ring
  have hA : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2)) (Ioi θ0) := by
    simpa using integrableOn_pow_mul_exp ha 0 (Ioi θ0)
  have hB : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2) / θ ^ 2 / (2 * a)) (Ioi θ0) :=
    (integrableOn_exp_div_sq ha h0).div_const _
  have hint : IntegrableOn g (Ioi θ0) := hA.add hB
  have hlim : Tendsto (fun θ => -G θ) atTop (𝓝 0) := by
    have := ((tendsto_inv_mul_exp ha).div_const (2 * a)).neg
    simp only [neg_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    simp only [G]; field_simp
  have hcont : ContinuousWithinAt (fun θ => -G θ) (Ici θ0) θ0 := by
    apply ContinuousAt.continuousWithinAt
    simp only [G]
    exact (((by fun_prop : Continuous fun θ : ℝ => Real.exp (-a * θ ^ 2)).continuousAt).div
      (by fun_prop) (by positivity)).neg
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hle : ∫ θ in Ioi θ0, Real.exp (-a * θ ^ 2) ≤ ∫ θ in Ioi θ0, g θ := by
    apply setIntegral_mono_on (by simpa using integrableOn_pow_mul_exp ha 0 (Ioi θ0)) hint
      measurableSet_Ioi
    intro θ hθ
    simp only [g]
    have : 0 ≤ Real.exp (-a * θ ^ 2) / θ ^ 2 / (2 * a) := by positivity
    linarith
  rw [hI] at hle
  simpa [G] using hle

/-- `∫_{θ₀}^∞ θ⁴e^{−aθ²} ≤ e^{−aθ₀²}(θ₀³/(2a) + 3θ₀/(4a²) + 3/(8a³θ₀))`. -/
lemma integral_Ioi_pow_four_exp_le {a θ0 : ℝ} (ha : 0 < a) (h0 : 0 < θ0) :
    ∫ θ in Ioi θ0, θ ^ 4 * Real.exp (-a * θ ^ 2) ≤ Real.exp (-a * θ0 ^ 2) *
      (θ0 ^ 3 / (2 * a) + 3 * θ0 / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ0)) := by
  set G : ℝ → ℝ := fun θ => Real.exp (-a * θ ^ 2) *
      (θ ^ 3 / (2 * a) + 3 * θ / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ))
  set g : ℝ → ℝ := fun θ => θ ^ 4 * Real.exp (-a * θ ^ 2) +
      Real.exp (-a * θ ^ 2) / θ ^ 2 * (3 / (8 * a ^ 3))
  have hderiv : ∀ x ∈ Ioi θ0, HasDerivAt (fun θ => -G θ) (g x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans h0 hx
    have h1 : HasDerivAt (fun θ : ℝ => Real.exp (-a * θ ^ 2)) (Real.exp (-a * x ^ 2) * (-a * (2 * x))) x := by
      have := ((hasDerivAt_pow 2 x).const_mul (-a)).exp
      convert this using 1; push_cast; ring
    have hP : HasDerivAt (fun θ : ℝ => θ ^ 3 / (2 * a) + 3 * θ / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ))
        (3 * x ^ 2 / (2 * a) + 3 / (4 * a ^ 2) - 3 / (8 * a ^ 3 * x ^ 2)) x := by
      have e1 := (hasDerivAt_pow 3 x).div_const (2 * a)
      have e2 := ((hasDerivAt_id x).const_mul 3).div_const (4 * a ^ 2)
      have e3 := (hasDerivAt_inv hx0.ne').const_mul (3 / (8 * a ^ 3))
      convert (e1.add e2).add e3 using 1
      · funext θ; simp only [id, Pi.add_apply]; field_simp
      · field_simp; push_cast; ring
    have := (h1.mul hP).neg
    convert this using 1
    simp only [g]; field_simp; ring
  have hA : IntegrableOn (fun θ : ℝ => θ ^ 4 * Real.exp (-a * θ ^ 2)) (Ioi θ0) :=
    integrableOn_pow_mul_exp ha 4 (Ioi θ0)
  have hB : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2) / θ ^ 2 * (3 / (8 * a ^ 3))) (Ioi θ0) :=
    (integrableOn_exp_div_sq ha h0).mul_const _
  have hint : IntegrableOn g (Ioi θ0) := hA.add hB
  have hlim : Tendsto (fun θ => -G θ) atTop (𝓝 0) := by
    have h3 := (tendsto_pow_mul_exp ha 3).div_const (2 * a)
    have h1 := ((tendsto_pow_mul_exp ha 1).const_mul 3).div_const (4 * a ^ 2)
    have hm := (tendsto_inv_mul_exp ha).const_mul (3 / (8 * a ^ 3))
    have := ((h3.add h1).add hm).neg
    simp only [zero_div, mul_zero, add_zero, neg_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    simp only [G]; field_simp
  have hcont : ContinuousWithinAt (fun θ => -G θ) (Ici θ0) θ0 := by
    apply ContinuousAt.continuousWithinAt
    simp only [G]
    have hne : 8 * a ^ 3 * θ0 ≠ 0 := by positivity
    have hd : ContinuousAt (fun θ : ℝ => 8 * a ^ 3 * θ) θ0 := continuousAt_const.mul continuousAt_id
    have : ContinuousAt (fun θ : ℝ => 3 / (8 * a ^ 3 * θ)) θ0 := continuousAt_const.div hd hne
    fun_prop
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hle : ∫ θ in Ioi θ0, θ ^ 4 * Real.exp (-a * θ ^ 2) ≤ ∫ θ in Ioi θ0, g θ := by
    apply setIntegral_mono_on (integrableOn_pow_mul_exp ha 4 (Ioi θ0)) hint measurableSet_Ioi
    intro θ hθ
    simp only [g]
    have : 0 ≤ Real.exp (-a * θ ^ 2) / θ ^ 2 * (3 / (8 * a ^ 3)) := by positivity
    linarith
  rw [hI] at hle
  simpa [G] using hle

end ArcsAlgo.LLT
