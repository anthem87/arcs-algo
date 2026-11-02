module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# Lemma M: a one-sided trigonometric majorant (paper §3.5)

`lemmaM`: there is `C` such that for every `M ≥ 2` a trigonometric polynomial `K_M` of degree
`≤ M` satisfies `K_M(x) ≥ log|cos πx|` (wherever `cos πx ≠ 0`), `K̂_M(0) ≤ −log 2 + C M^{−1/2}`,
and its other coefficients are bounded by `C`.

The proof is the paper's: `f_ε = max(log|cos πx|, log ε) = log max(|cos πx|, ε)` is continuous,
`1`-periodic and `(π/ε)`-Lipschitz (`fε_lip`); `−log 2 ≤ ∫₀¹ f_ε ≤ −log 2 + 4ε` (`integral_fε_ge`,
`integral_fε_le`, from `∫₀^{π/2} log sin = −(π/2) log 2` and `sin πt ≥ 2t`); the Jackson mean of
`f_ε`, raised by its error, majorizes `f_ε`; `ε = M^{−1/2}`.

**Hypothesis.** Jackson's theorem for Lipschitz functions, in the form given by the Jackson means
(`JacksonThm`, cited: Jackson 1911; Lorentz, *Approximation of Functions*, Ch. 4). It is a `Prop`,
never an axiom.
-/

open Real intervalIntegral MeasureTheory

@[expose] public section

namespace ArcsAlgo.ArcM

/-- A real trigonometric polynomial of degree `≤ n`. -/
noncomputable def trigPoly (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (a k * cos (2 * π * k * x) + b k * sin (2 * π * k * x))

/-- **Jackson's theorem** [D. Jackson, *Über die Genauigkeit der Annäherung stetiger Funktionen
durch ganze rationale Funktionen gegebenen Grades und trigonometrische Summen gegebener Ordnung*,
1911; G. G. Lorentz, *Approximation of Functions*, Ch. 4, Thm 1], in the form given by the
Jackson means `J_n f = j_n ∗ f`: a continuous `1`-periodic `L`-Lipschitz `f` is approximated
within `C·L/n` by a trigonometric polynomial of degree `≤ n` whose mean is that of `f` and whose
coefficients are those of `f` times multipliers in `[0, 1]`, hence bounded by `2∫₀¹|f|`.
An explicit hypothesis, never an axiom. -/
def JacksonThm : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (L : ℝ), 0 ≤ L → Continuous f → (∀ x, f (x + 1) = f x) →
    (∀ x y, |f x - f y| ≤ L * |x - y|) → ∀ n : ℕ, 1 ≤ n →
    ∃ a b : ℕ → ℝ, a 0 = (∫ x in (0 : ℝ)..1, f x) ∧
      (∀ k, 1 ≤ k → |a k| ≤ 2 * ∫ x in (0 : ℝ)..1, |f x| ∧ |b k| ≤ 2 * ∫ x in (0 : ℝ)..1, |f x|) ∧
      ∀ x, |f x - trigPoly n a b x| ≤ C * L / n

/-- `f_ε = max(log|cos πx|, log ε) = log max(|cos πx|, ε)`. -/
noncomputable def fε (ε x : ℝ) : ℝ := log (max |cos (π * x)| ε)

theorem fε_periodic (ε x : ℝ) : fε ε (x + 1) = fε ε x := by
  unfold fε; rw [show π * (x + 1) = π * x + π by ring, cos_add_pi, abs_neg]

theorem fε_cont {ε : ℝ} (hε : 0 < ε) : Continuous (fε ε) := by
  unfold fε
  apply Continuous.log (by fun_prop)
  intro x; exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'

theorem log_lip {ε u v : ℝ} (hε : 0 < ε) (hu : ε ≤ u) (hv : ε ≤ v) : |log u - log v| ≤ |u - v| / ε := by
  have hu0 : 0 < u := lt_of_lt_of_le hε hu
  have hv0 : 0 < v := lt_of_lt_of_le hε hv
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (by linarith [log_le_log hv0 h]), abs_of_nonneg (by linarith)]
    rw [← log_div hu0.ne' hv0.ne']
    have := log_le_sub_one_of_pos (div_pos hu0 hv0)
    calc log (u / v) ≤ u / v - 1 := this
      _ = (u - v) / v := by field_simp
      _ ≤ (u - v) / ε := div_le_div_of_nonneg_left (by linarith) hε hv
  · rw [abs_of_nonpos (by linarith [log_le_log hu0 h]), abs_of_nonpos (by linarith)]
    rw [show -(log u - log v) = log (v / u) by rw [log_div hv0.ne' hu0.ne']; ring]
    have := log_le_sub_one_of_pos (div_pos hv0 hu0)
    calc log (v / u) ≤ v / u - 1 := this
      _ = -(u - v) / u := by field_simp; ring
      _ ≤ -(u - v) / ε := div_le_div_of_nonneg_left (by linarith) hε hu

/-- `f_ε` is `(π/ε)`-Lipschitz. -/
theorem fε_lip {ε : ℝ} (hε : 0 < ε) (x y : ℝ) : |fε ε x - fε ε y| ≤ π / ε * |x - y| := by
  unfold fε
  have h1 := log_lip hε (le_max_right |cos (π * x)| ε) (le_max_right |cos (π * y)| ε)
  have h2 : |max |cos (π * x)| ε - max |cos (π * y)| ε| ≤ π * |x - y| := by
    calc |max |cos (π * x)| ε - max |cos (π * y)| ε| ≤ |(|cos (π * x)| - |cos (π * y)|)| :=
          abs_max_sub_max_le_abs _ _ _
      _ ≤ |cos (π * x) - cos (π * y)| := abs_abs_sub_abs_le_abs_sub _ _
      _ ≤ |π * x - π * y| := abs_cos_sub_cos_le _ _
      _ = π * |x - y| := by rw [← mul_sub, abs_mul, abs_of_pos pi_pos]
  calc |log (max |cos (π * x)| ε) - log (max |cos (π * y)| ε)|
      ≤ |max |cos (π * x)| ε - max |cos (π * y)| ε| / ε := h1
    _ ≤ π * |x - y| / ε := div_le_div_of_nonneg_right h2 hε.le
    _ = π / ε * |x - y| := by ring

theorem fε_nonpos {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) : fε ε x ≤ 0 := by
  unfold fε
  apply log_nonpos (lt_of_lt_of_le hε (le_max_right _ _)).le
  exact max_le (abs_cos_le_one _) hε1

theorem log_le_fε {ε : ℝ} (x : ℝ) (hx : cos (π * x) ≠ 0) : log |cos (π * x)| ≤ fε ε x := by
  unfold fε
  exact log_le_log (abs_pos.mpr hx) (le_max_left _ _)

/-- The two halves of a period: `∫₀¹ f_ε = 2∫₀^{1/2} log max(sin πt, ε)`. -/
theorem integral_fε {ε : ℝ} (hε : 0 < ε) :
    ∫ x in (0 : ℝ)..1, fε ε x = 2 * ∫ t in (0 : ℝ)..1 / 2, log (max (sin (π * t)) ε) := by
  have hc := fε_cont hε
  have hG : Continuous fun t : ℝ => log (max (sin (π * t)) ε) := by
    apply Continuous.log (by fun_prop)
    intro x; exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'
  rw [← integral_add_adjacent_intervals (b := 1 / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (0 : ℝ)..1 / 2, fε ε x = ∫ t in (0 : ℝ)..1 / 2, log (max (sin (π * t)) ε) := by
    have : ∫ x in (0 : ℝ)..1 / 2, fε ε x =
        ∫ x in (0 : ℝ)..1 / 2, log (max (sin (π * (1 / 2 - x))) ε) := by
      refine integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      unfold fε
      have : cos (π * x) = sin (π * (1 / 2 - x)) := by
        rw [show π * (1 / 2 - x) = π / 2 - π * x by ring, sin_pi_div_two_sub]
      rw [this, abs_of_nonneg]
      apply sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [pi_pos, hx.1, hx.2]
    rw [this, intervalIntegral.integral_comp_sub_left (fun t => log (max (sin (π * t)) ε)) (1 / 2)]
    norm_num
  have h2 : ∫ x in (1 / 2 : ℝ)..1, fε ε x = ∫ t in (0 : ℝ)..1 / 2, log (max (sin (π * t)) ε) := by
    have : ∫ x in (1 / 2 : ℝ)..1, fε ε x =
        ∫ x in (1 / 2 : ℝ)..1, log (max (sin (π * (x - 1 / 2))) ε) := by
      refine integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      unfold fε
      have : |cos (π * x)| = sin (π * (x - 1 / 2)) := by
        have e : cos (π * x) = -sin (π * (x - 1 / 2)) := by
          rw [show π * x = π * (x - 1 / 2) + π / 2 by ring, cos_add_pi_div_two]
        rw [e, abs_neg, abs_of_nonneg]
        apply sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [pi_pos, hx.1, hx.2]
      rw [this]
    rw [this, intervalIntegral.integral_comp_sub_right (fun t => log (max (sin (π * t)) ε)) (1 / 2)]
    norm_num
  rw [h1, h2]; ring

theorem integral_log_sin_half : ∫ t in (0 : ℝ)..1 / 2, log (sin (π * t)) = -log 2 / 2 := by
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1 / 2) (fun u => log (sin u))
    pi_pos.ne'
  rw [this, mul_zero, show π * (1 / 2) = π / 2 by ring, integral_log_sin_zero_pi_div_two, smul_eq_mul]
  field_simp

theorem intervalIntegrable_log_sin_pi (a b : ℝ) :
    IntervalIntegrable (fun t => log (sin (π * t))) volume a b := by
  have h := (intervalIntegrable_log_sin (a := π * a) (b := π * b)).comp_mul_left (c := π)
  have e : π * a / π = a := by field_simp
  have e2 : π * b / π = b := by field_simp
  rw [e, e2] at h
  exact h

/-- `∫₀¹ f_ε ≥ −log 2`. -/
theorem integral_fε_ge {ε : ℝ} (hε : 0 < ε) : -log 2 ≤ ∫ x in (0 : ℝ)..1, fε ε x := by
  rw [integral_fε hε]
  have hG : Continuous fun t : ℝ => log (max (sin (π * t)) ε) := by
    apply Continuous.log (by fun_prop)
    intro x; exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'
  have : ∫ t in (0 : ℝ)..1 / 2, log (sin (π * t)) ≤ ∫ t in (0 : ℝ)..1 / 2, log (max (sin (π * t)) ε) := by
    apply intervalIntegral.integral_mono_ae_restrict (by norm_num) (intervalIntegrable_log_sin_pi _ _)
      (hG.intervalIntegrable _ _)
    have hnull : volume ({0} : Set ℝ) = 0 := measure_singleton 0
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htI
    have ht0 : 0 < t := lt_of_le_of_ne htI.1 (fun h => ht (by simp [h]))
    have hs : 0 < sin (π * t) := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos, htI.2])
    exact log_le_log hs (le_max_left _ _)
  rw [integral_log_sin_half] at this
  linarith

/-- `∫₀¹ f_ε ≤ −log 2 + 4ε` for `0 < ε ≤ 1`. -/
theorem integral_fε_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x in (0 : ℝ)..1, fε ε x ≤ -log 2 + 4 * ε := by
  rw [integral_fε hε]
  set G := fun t : ℝ => log (max (sin (π * t)) ε)
  have hG : Continuous G := by
    apply Continuous.log (by fun_prop)
    intro x; exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'
  set a := ε / 2
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by simp only [a]; linarith
  have hsplit := integral_add_adjacent_intervals (hG.intervalIntegrable (μ := volume) 0 a)
    (hG.intervalIntegrable (μ := volume) a (1 / 2))
  have hsplit2 := integral_add_adjacent_intervals (intervalIntegrable_log_sin_pi 0 a)
    (intervalIntegrable_log_sin_pi a (1 / 2))
  -- on `[a, 1/2]`, `sin πt ≥ 2t ≥ ε`
  have hright : ∫ t in a..1 / 2, G t = ∫ t in a..1 / 2, log (sin (π * t)) := by
    refine integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le ha1] at ht
    simp only [G]
    congr 1
    apply max_eq_left
    have := mul_le_sin (x := π * t) (by nlinarith [pi_pos, ht.1]) (by nlinarith [pi_pos, ht.2])
    have e : 2 / π * (π * t) = 2 * t := by field_simp
    rw [e] at this
    simp only [a] at ht; linarith [ht.1]
  -- on `[0, a]`, `log max(sin πt, ε) ≤ log sin πt + 2√(ε/2)·t^{−1/2}`
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hleft : ∫ t in (0 : ℝ)..a, G t ≤
      ∫ t in (0 : ℝ)..a, (log (sin (π * t)) + 2 * √(ε / 2) * t ^ (-(1 / 2) : ℝ)) := by
    apply intervalIntegral.integral_mono_ae_restrict ha0.le (hG.intervalIntegrable _ _)
      ((intervalIntegrable_log_sin_pi _ _).add (hint.const_mul _))
    have hnull : volume ({0} : Set ℝ) = 0 := measure_singleton 0
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htI
    have ht0 : 0 < t := lt_of_le_of_ne htI.1 (fun h => ht (by simp [h]))
    have htle : t ≤ 1 / 2 := le_trans htI.2 ha1
    have hs2 : 2 * t ≤ sin (π * t) := by
      have := mul_le_sin (x := π * t) (by positivity) (by nlinarith [pi_pos])
      have e : 2 / π * (π * t) = 2 * t := by field_simp
      rwa [e] at this
    have hs : 0 < sin (π * t) := by linarith
    simp only [G]
    rcases le_total ε (sin (π * t)) with h | h
    · rw [max_eq_left h]
      have : 0 ≤ 2 * √(ε / 2) * t ^ (-(1 / 2) : ℝ) := by positivity
      linarith
    · rw [max_eq_right h]
      have e1 : log ε = log (sin (π * t)) + log (ε / sin (π * t)) := by
        rw [log_div hε.ne' hs.ne']; ring
      have e2 : log (ε / sin (π * t)) ≤ log (ε / (2 * t)) :=
        log_le_log (by positivity) (div_le_div_of_nonneg_left hε.le (by positivity) hs2)
      have e3 : log (ε / (2 * t)) ≤ (ε / (2 * t)) ^ (1 / 2 : ℝ) / (1 / 2) :=
        log_le_rpow_div (by positivity) (by norm_num)
      have e4 : (ε / (2 * t)) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * √(ε / 2) * t ^ (-(1 / 2) : ℝ) := by
        rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          show ε / (2 * t) = (ε / 2) / t by ring, Real.sqrt_div' _ ht0.le]
        field_simp
      linarith
  have hr : ∫ t in (0 : ℝ)..a, t ^ (-(1 / 2) : ℝ) = 2 * √a := by
    rw [integral_rpow (by norm_num), show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num,
      Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow]
    ring
  have hJ : ∫ t in (0 : ℝ)..a, (log (sin (π * t)) + 2 * √(ε / 2) * t ^ (-(1 / 2) : ℝ)) =
      (∫ t in (0 : ℝ)..a, log (sin (π * t))) + 2 * ε := by
    rw [integral_add (intervalIntegrable_log_sin_pi _ _) (hint.const_mul _),
      intervalIntegral.integral_const_mul, hr]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ ε / 2 by positivity)
    have e : 2 * √(ε / 2) * (2 * √a) = 2 * ε := by
      simp only [a]; nlinarith [this]
    rw [e]
  have hhalf := integral_log_sin_half
  linarith

/-- `∫₀¹ |f_ε| ≤ log 2` for `0 < ε ≤ 1`. -/
theorem integral_abs_fε {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x in (0 : ℝ)..1, |fε ε x| ≤ log 2 := by
  have : ∫ x in (0 : ℝ)..1, |fε ε x| = -∫ x in (0 : ℝ)..1, fε ε x := by
    rw [← intervalIntegral.integral_neg]
    refine integral_congr fun x _ => ?_
    rw [abs_of_nonpos (fε_nonpos hε hε1 x)]
  rw [this]; linarith [integral_fε_ge hε]

/-- **Lemma M (one-sided trigonometric majorant)** (paper §3.5), with Jackson's theorem as the only
(cited) hypothesis: there is `C` such that for every `M ≥ 2` some trigonometric polynomial `K_M`
of degree `≤ M` satisfies `K_M(x) ≥ log|cos πx|` wherever `cos πx ≠ 0`, `K̂_M(0) ≤ −log 2 + C/√M`,
and all its other coefficients are bounded by `C`. -/
theorem lemmaM (hJ : JacksonThm) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∃ a b : ℕ → ℝ,
      (∀ x, cos (π * x) ≠ 0 → log |cos (π * x)| ≤ trigPoly M a b x) ∧
      a 0 ≤ -log 2 + C / √(M : ℝ) ∧ ∀ k, 1 ≤ k → |a k| ≤ C ∧ |b k| ≤ C := by
  obtain ⟨CJ, hCJ, hJ⟩ := hJ
  refine ⟨max (4 + CJ * π) (2 * log 2), lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun M hM => ?_⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hM0
  have hsM1 : 1 ≤ √(M : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hM0.le]; exact_mod_cast (by omega : 1 ≤ M)
  set ε := 1 / √(M : ℝ)
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [div_le_one hsM]; exact hsM1
  obtain ⟨a, b, ha0, hab, happ⟩ := hJ (fε ε) (π / ε) (by positivity) (fε_cont hε)
    (fε_periodic ε) (fε_lip hε) M (by omega)
  set δ := CJ * (π / ε) / M
  have hδ : δ = CJ * π / √(M : ℝ) := by
    have h1 : π / ε = π * √(M : ℝ) := by simp only [ε]; field_simp
    simp only [δ]
    rw [h1, div_eq_div_iff hM0.ne' hsM.ne']
    have := Real.mul_self_sqrt hM0.le
    linear_combination CJ * π * this
  set a' : ℕ → ℝ := fun k => if k = 0 then a 0 + δ else a k
  have htp : ∀ x, trigPoly M a' b x = trigPoly M a b x + δ := by
    intro x
    unfold trigPoly
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => a k * cos (2 * π * k * x) + b k * sin (2 * π * k * x))]
    have : ∀ k ∈ Finset.range M, a' (k + 1) * cos (2 * π * ((k + 1 : ℕ) : ℝ) * x) +
        b (k + 1) * sin (2 * π * ((k + 1 : ℕ) : ℝ) * x) =
        a (k + 1) * cos (2 * π * ((k + 1 : ℕ) : ℝ) * x) + b (k + 1) * sin (2 * π * ((k + 1 : ℕ) : ℝ) * x) := by
      intro k _; simp [a']
    rw [Finset.sum_congr rfl this]
    simp [a']; ring
  refine ⟨a', b, fun x hx => ?_, ?_, fun k hk => ?_⟩
  · have h1 := log_le_fε (ε := ε) x hx
    have h2 := (abs_le.mp (happ x)).2
    rw [htp]
    linarith
  · simp only [a', if_pos rfl, ha0]
    have := integral_fε_le hε hε1
    have e : 4 * ε = 4 / √(M : ℝ) := by simp only [ε]; ring
    rw [hδ]
    calc (∫ x in (0 : ℝ)..1, fε ε x) + CJ * π / √(M : ℝ) ≤ -log 2 + 4 / √(M : ℝ) + CJ * π / √(M : ℝ) := by
          linarith
      _ = -log 2 + (4 + CJ * π) / √(M : ℝ) := by ring
      _ ≤ -log 2 + max (4 + CJ * π) (2 * log 2) / √(M : ℝ) := by
          gcongr; exact le_max_left _ _
  · have hk0 : k ≠ 0 := by omega
    simp only [a', if_neg hk0]
    obtain ⟨h1, h2⟩ := hab k hk
    have h3 := integral_abs_fε hε hε1
    constructor
    · refine h1.trans ((by linarith : 2 * ∫ x in (0 : ℝ)..1, |fε ε x| ≤ 2 * log 2).trans (le_max_right _ _))
    · refine h2.trans ((by linarith : 2 * ∫ x in (0 : ℝ)..1, |fε ε x| ≤ 2 * log 2).trans (le_max_right _ _))

end ArcsAlgo.ArcM
