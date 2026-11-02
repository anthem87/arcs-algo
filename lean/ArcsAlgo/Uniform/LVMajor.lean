module

public import ArcsAlgo.LocalLimit.Tails
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false

/-!
# Theorem LV: the major arc, abstractly (paper §6.6)

`major_lb`: a lower bound for `∫_0^β cos(cθ)P(θ)dθ` when `P` is close to `e^{−aθ²}`; the Gaussian
moments `∫_0^∞ θ^{2,4} e^{−aθ²}` (`integral_sq_gauss`, `integral_four_gauss`).
-/

open Real MeasureTheory Set

@[expose] public section

namespace ArcsAlgo.LLT

theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

theorem Gamma_five_halves : Real.Gamma (5 / 2) = 3 * √π / 4 := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Gamma_three_halves]
  ring

theorem rpow_neg_half_eq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    a ^ (-((2 * k + 1 : ℝ)) / 2) = 1 / (a ^ k * √a) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add ha, one_div, ← Real.rpow_neg ha.le]
  congr 1; ring

/-- `∫_0^∞ θ² e^{−aθ²} = √(π/a)/(4a)`. -/
theorem integral_sq_gauss {a : ℝ} (ha : 0 < a) :
    ∫ θ in Ioi (0 : ℝ), θ ^ 2 * Real.exp (-a * θ ^ 2) = √(π / a) / (4 * a) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := a) (by norm_num) (by norm_num) ha
  have e : ∀ θ : ℝ, θ ^ (2 : ℝ) * Real.exp (-a * θ ^ (2 : ℝ)) = θ ^ 2 * Real.exp (-a * θ ^ 2) := by
    intro θ; rw [Real.rpow_two]
  simp only [e] at h
  rw [h, show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num, Gamma_three_halves,
    show (-((2 : ℝ) + 1) / 2) = -(2 * (1 : ℕ) + 1 : ℝ) / 2 by norm_num, rpow_neg_half_eq ha,
    Real.sqrt_div' _ ha.le]
  have hs := Real.sqrt_pos.mpr ha
  field_simp
  ring

/-- `∫_0^∞ θ⁴ e^{−aθ²} = 3√(π/a)/(8a²)`. -/
theorem integral_four_gauss {a : ℝ} (ha : 0 < a) :
    ∫ θ in Ioi (0 : ℝ), θ ^ 4 * Real.exp (-a * θ ^ 2) = 3 * √(π / a) / (8 * a ^ 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 4) (b := a) (by norm_num) (by norm_num) ha
  have e : ∀ θ : ℝ, θ ^ (4 : ℝ) * Real.exp (-a * θ ^ (2 : ℝ)) = θ ^ 4 * Real.exp (-a * θ ^ 2) := by
    intro θ; rw [Real.rpow_two, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e] at h
  rw [h, show ((4 : ℝ) + 1) / 2 = 5 / 2 by norm_num, Gamma_five_halves,
    show (-((4 : ℝ) + 1) / 2) = -(2 * (2 : ℕ) + 1 : ℝ) / 2 by norm_num, rpow_neg_half_eq ha,
    Real.sqrt_div' _ ha.le]
  have hs := Real.sqrt_pos.mpr ha
  field_simp
  ring

theorem integrableOn_gauss {a : ℝ} (ha : 0 < a) (S : Set ℝ) :
    IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2)) S :=
  (integrable_exp_neg_mul_sq ha).integrableOn

theorem integrableOn_cos_gauss {a : ℝ} (ha : 0 < a) (c : ℝ) (S : Set ℝ) :
    IntegrableOn (fun θ : ℝ => Real.cos (c * θ) * Real.exp (-a * θ ^ 2)) S := by
  refine Integrable.integrableOn ?_
  refine (integrable_exp_neg_mul_sq ha).mono (by fun_prop) (Filter.Eventually.of_forall fun θ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (abs_cos_le_one _)

/-- **The major arc, abstractly.** Let `g(θ) = e^{−aθ²}` and let `P` be continuous with
`|g − P| ≤ Kθ⁴g` on `[0, β₁]` and `|P| ≤ g` on `[β₁, β]`. Then
`∫_0^β cos(cθ)P ≥ √(π/a)/2 − c²√(π/a)/(8a) − 3K√(π/a)/(8a²) − 3e^{−aβ₁²}/(2aβ₁)`. -/
theorem major_lb {a β₁ β K c : ℝ} (ha : 0 < a) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β) (hK : 0 ≤ K)
    {P : ℝ → ℝ} (hP : Continuous P)
    (h1 : ∀ θ ∈ Icc 0 β₁, |Real.exp (-a * θ ^ 2) - P θ| ≤ K * θ ^ 4 * Real.exp (-a * θ ^ 2))
    (h2 : ∀ θ ∈ Icc β₁ β, |P θ| ≤ Real.exp (-a * θ ^ 2)) :
    √(π / a) / 2 - c ^ 2 * √(π / a) / (8 * a) - K * (3 * √(π / a) / (8 * a ^ 2)) -
        3 * (Real.exp (-a * β₁ ^ 2) / (2 * a * β₁)) ≤
      ∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * P θ := by
  set g : ℝ → ℝ := fun θ => Real.exp (-a * θ ^ 2) with hg
  have hβ0 : 0 ≤ β := hβ₁.le.trans hβ
  have hgc : Continuous g := by fun_prop
  have tail := integral_Ioi_exp_le ha hβ₁
  set T := ∫ θ in Ioi β₁, g θ
  -- the full half-line integral of `cos(cθ)g`
  have hA0 : √(π / a) / 2 - c ^ 2 * √(π / a) / (8 * a) ≤ ∫ θ in Ioi (0 : ℝ), Real.cos (c * θ) * g θ := by
    have e : ∫ θ in Ioi (0 : ℝ), (g θ - c ^ 2 / 2 * (θ ^ 2 * g θ)) =
        √(π / a) / 2 - c ^ 2 * √(π / a) / (8 * a) := by
      rw [integral_sub (integrableOn_gauss ha _) ((integrableOn_pow_mul_exp ha 2 _).const_mul _),
        integral_const_mul, integral_gaussian_Ioi, integral_sq_gauss ha]
      field_simp; ring
    rw [← e]
    refine setIntegral_mono_on ((integrableOn_gauss ha _).sub
      ((integrableOn_pow_mul_exp ha 2 _).const_mul _)) (integrableOn_cos_gauss ha c _)
      measurableSet_Ioi fun θ _ => ?_
    have hc := Real.one_sub_sq_div_two_le_cos (x := c * θ)
    have hg0 : 0 < g θ := Real.exp_pos _
    nlinarith
  -- `∫_0^β cos(cθ)g ≥ ∫_0^∞ cos(cθ)g − T`
  have hsplit : ∫ θ in Ioi (0 : ℝ), Real.cos (c * θ) * g θ =
      (∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * g θ) + ∫ θ in Ioi β, Real.cos (c * θ) * g θ := by
    rw [intervalIntegral.integral_of_le hβ0, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (integrableOn_cos_gauss ha c _) (integrableOn_cos_gauss ha c _),
      Ioc_union_Ioi_eq_Ioi hβ0]
  have hTβ : ∫ θ in Ioi β, Real.cos (c * θ) * g θ ≤ T := by
    calc ∫ θ in Ioi β, Real.cos (c * θ) * g θ ≤ ∫ θ in Ioi β, g θ :=
          setIntegral_mono_on (integrableOn_cos_gauss ha c _) (integrableOn_gauss ha _) measurableSet_Ioi
            fun θ _ => mul_le_of_le_one_left (Real.exp_pos _).le (Real.cos_le_one _)
      _ ≤ T := setIntegral_mono_set (integrableOn_gauss ha _)
            (Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le)
            (Filter.Eventually.of_forall (Ioi_subset_Ioi hβ))
  -- the error `∫_0^β cos(cθ)(g − P)`
  have hB : ∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * (g θ - P θ) ≤
      K * (3 * √(π / a) / (8 * a ^ 2)) + 2 * T := by
    have i1 : IntervalIntegrable (fun θ => |g θ - P θ|) volume 0 β₁ :=
      (by fun_prop : Continuous fun θ => |g θ - P θ|).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => |g θ - P θ|) volume β₁ β :=
      (by fun_prop : Continuous fun θ => |g θ - P θ|).intervalIntegrable _ _
    calc ∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * (g θ - P θ) ≤ ∫ θ in (0 : ℝ)..β, |g θ - P θ| := by
          refine intervalIntegral.integral_mono_on hβ0
            ((by fun_prop : Continuous fun θ => Real.cos (c * θ) * (g θ - P θ)).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun θ => |g θ - P θ|).intervalIntegrable _ _) fun θ _ => ?_
          calc Real.cos (c * θ) * (g θ - P θ) ≤ |Real.cos (c * θ) * (g θ - P θ)| := le_abs_self _
            _ = |Real.cos (c * θ)| * |g θ - P θ| := abs_mul _ _
            _ ≤ 1 * |g θ - P θ| := mul_le_mul_of_nonneg_right (abs_cos_le_one _) (abs_nonneg _)
            _ = _ := one_mul _
      _ = (∫ θ in (0 : ℝ)..β₁, |g θ - P θ|) + ∫ θ in β₁..β, |g θ - P θ| :=
          (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
      _ ≤ K * (3 * √(π / a) / (8 * a ^ 2)) + 2 * T := by
          gcongr
          · calc ∫ θ in (0 : ℝ)..β₁, |g θ - P θ| ≤ ∫ θ in (0 : ℝ)..β₁, K * (θ ^ 4 * g θ) :=
                  intervalIntegral.integral_mono_on hβ₁.le i1
                    ((by fun_prop : Continuous fun θ => K * (θ ^ 4 * g θ)).intervalIntegrable _ _)
                    fun θ hθ => by have := h1 θ hθ; simp only [hg]; linarith
              _ = K * ∫ θ in Ioc (0 : ℝ) β₁, θ ^ 4 * g θ := by
                  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hβ₁.le]
              _ ≤ K * ∫ θ in Ioi (0 : ℝ), θ ^ 4 * g θ := by
                  refine mul_le_mul_of_nonneg_left ?_ hK
                  exact setIntegral_mono_set (integrableOn_pow_mul_exp ha 4 _)
                    (Filter.Eventually.of_forall fun θ => by positivity)
                    (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
              _ = K * (3 * √(π / a) / (8 * a ^ 2)) := by rw [integral_four_gauss ha]
          · calc ∫ θ in β₁..β, |g θ - P θ| ≤ ∫ θ in β₁..β, 2 * g θ :=
                  intervalIntegral.integral_mono_on hβ i2
                    ((by fun_prop : Continuous fun θ => 2 * g θ).intervalIntegrable _ _)
                    fun θ hθ => by
                      have := h2 θ hθ
                      have h3 := abs_sub (g θ) (P θ)
                      rw [abs_of_pos (Real.exp_pos _)] at h3
                      simp only [hg] at h3 ⊢; linarith
              _ = 2 * ∫ θ in Ioc β₁ β, g θ := by
                  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hβ]
              _ ≤ 2 * T := by
                  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
                  exact setIntegral_mono_set (integrableOn_gauss ha _)
                    (Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le)
                    (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  have e : ∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * P θ =
      (∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * g θ) - ∫ θ in (0 : ℝ)..β, Real.cos (c * θ) * (g θ - P θ) := by
    rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun θ => Real.cos (c * θ) * g θ).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ => Real.cos (c * θ) * (g θ - P θ)).intervalIntegrable _ _)]
    congr 1; funext θ; ring
  rw [e]
  have hT : T ≤ Real.exp (-a * β₁ ^ 2) / (2 * a * β₁) := tail
  linarith

end ArcsAlgo.LLT
