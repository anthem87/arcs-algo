module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Log
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false

/-!
# The Clausen bound (paper §3.3, Lemma Q)

`G(u) = log|2 sin πu|` (`Gs`, written `log 2 + log|sin πu|`, equal to it off `ℤ`),
`C(u) = ∫₀^u G = −Cl₂(2πu)/(2π)` (`Cl`) and `κ = Cl₂(π/3)/π = −2C(1/6)` (`kappa`).

* `integral_Gs_zero_one`: `∫₀¹ G = 0`, from `∫₀^π log sin = −π log 2`.
* `Cl_periodic`, `Cl_one_sub`: `C(u + 1) = C(u)`, `C(1 − u) = −C(u)`.
* `Gs_nonpos_small`, `Gs_nonneg_mid`: `G ≤ 0` on `(0, 1/6)`, `G ≥ 0` on `(1/6, 5/6)`.
* `abs_Cl_le`: `|C(u)| ≤ κ/2` for all `u`, i.e. `|Cl₂| ≤ Cl₂(π/3)`.
* `abs_avg_Gs_le`: `|X⁻¹∫₀^X G(dx + c) dx| ≤ κ/(dX)`.

No hypothesis; the numerical value `κ = 0.32307…` is not used here.
-/

open Real MeasureTheory

@[expose] public section

namespace ArcsAlgo.Core

/-- `G(u) = log|2 sin πu|`, written `log 2 + log|sin πu|` (they differ only at `u ∈ ℤ`). -/
noncomputable def Gs (u : ℝ) : ℝ := Real.log 2 + Real.log (sin (π * u))

/-- `C(u) = ∫₀^u log|2 sin πt| dt = −Cl₂(2πu)/(2π)`. -/
noncomputable def Cl (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, Gs t

/-- `κ = Cl₂(π/3)/π = −2C(1/6)` (`= 0.32307…`). -/
noncomputable def kappa : ℝ := -2 * Cl (1 / 6)

theorem logsin_int (a b : ℝ) : IntervalIntegrable (fun t => Real.log (sin (π * t))) volume a b := by
  have := (intervalIntegrable_log_sin (a := π * a) (b := π * b)).comp_mul_left (c := π)
  rwa [mul_div_cancel_left₀ _ Real.pi_ne_zero, mul_div_cancel_left₀ _ Real.pi_ne_zero] at this

theorem Gs_int (a b : ℝ) : IntervalIntegrable Gs volume a b :=
  intervalIntegrable_const.add (logsin_int a b)

theorem Gs_periodic : Function.Periodic Gs 1 := by
  intro u; unfold Gs
  rw [show π * (u + 1) = π * u + π by ring, Real.sin_add_pi, Real.log_neg_eq_log]

theorem Gs_one_sub (u : ℝ) : Gs (1 - u) = Gs u := by
  unfold Gs; rw [show π * (1 - u) = π - π * u by ring, Real.sin_pi_sub]

theorem Gs_le (u : ℝ) : Gs u ≤ Real.log 2 := by
  unfold Gs
  have : Real.log (sin (π * u)) ≤ 0 := by
    rw [← Real.log_abs]
    rcases (abs_nonneg (sin (π * u))).eq_or_lt with h | h
    · rw [← h, Real.log_zero]
    · exact Real.log_nonpos h.le (abs_sin_le_one _)
  linarith

/-- `∫₀¹ log|2 sin πt| dt = 0`, from `∫₀^π log sin = −π log 2`. -/
theorem integral_Gs_zero_one : ∫ t in (0 : ℝ)..1, Gs t = 0 := by
  unfold Gs
  have h := logsin_int 0 1
  rw [intervalIntegral.integral_add intervalIntegrable_const h, intervalIntegral.integral_const,
    intervalIntegral.integral_comp_mul_left (fun x => Real.log (sin x)) Real.pi_ne_zero, mul_zero, mul_one,
    integral_log_sin_zero_pi]
  simp only [sub_zero, smul_eq_mul, one_mul]
  field_simp; ring

theorem Cl_add (u v : ℝ) : Cl v = Cl u + ∫ t in u..v, Gs t := by
  unfold Cl; rw [intervalIntegral.integral_add_adjacent_intervals (Gs_int 0 u) (Gs_int u v)]

theorem Cl_periodic : Function.Periodic Cl 1 := by
  intro u
  rw [Cl_add u (u + 1), Gs_periodic.intervalIntegral_add_eq u 0, zero_add, integral_Gs_zero_one, add_zero]

theorem Cl_one_sub (u : ℝ) : Cl (1 - u) = -Cl u := by
  have h1 : Cl (1 - u) = ∫ t in u..1, Gs t := by
    unfold Cl
    have := intervalIntegral.integral_comp_sub_left (a := u) (b := 1) Gs 1
    simp only [sub_self, sub_sub_cancel] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => (Gs_one_sub t)
  have h2 := Cl_add u 1
  have h3 : Cl 1 = 0 := integral_Gs_zero_one
  rw [h1]; linarith

theorem Gs_nonpos_small {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) (1 / 6)) : Gs u ≤ 0 := by
  obtain ⟨h0, h1⟩ := hu
  unfold Gs
  have hpi := Real.pi_pos
  have hs0 : 0 < sin (π * u) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hs1 : sin (π * u) ≤ 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
  have : Real.log (sin (π * u)) ≤ Real.log (1 / 2) := Real.log_le_log hs0 hs1
  rw [one_div, Real.log_inv] at this
  linarith

theorem Gs_nonneg_mid {u : ℝ} (hu : u ∈ Set.Ioo (1 / 6 : ℝ) (5 / 6)) : 0 ≤ Gs u := by
  obtain ⟨h0, h1⟩ := hu
  unfold Gs
  have hpi := Real.pi_pos
  have hs1 : 1 / 2 ≤ sin (π * u) := by
    rcases le_or_gt u (1 / 2) with h | h
    · rw [← Real.sin_pi_div_six]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
    · rw [← Real.sin_pi_div_six, ← Real.sin_pi_sub (π * u)]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
  have : Real.log (1 / 2) ≤ Real.log (sin (π * u)) := Real.log_le_log (by norm_num) hs1
  rw [one_div, Real.log_inv] at this
  linarith

theorem Cl_sixth_nonpos : Cl (1 / 6) ≤ 0 := by
  unfold Cl
  have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 6)
    (Gs_int 0 (1 / 6)) (intervalIntegrable_const (c := (0 : ℝ))) fun x hx => Gs_nonpos_small hx
  simpa using this

/-- `C(u) ≥ C(1/6)` on `[0, 1]`. -/
theorem Cl_ge_unit {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Cl (1 / 6) ≤ Cl u := by
  rcases le_or_gt u (1 / 6) with hu | hu
  · have e := Cl_add u (1 / 6)
    have : ∫ t in u..(1 / 6), Gs t ≤ 0 := by
      have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hu (Gs_int u (1 / 6))
        (intervalIntegrable_const (c := (0 : ℝ))) fun x hx =>
          Gs_nonpos_small ⟨lt_of_le_of_lt h0 hx.1, hx.2⟩
      simpa using this
    linarith
  rcases le_or_gt u (5 / 6) with hu' | hu'
  · have e := Cl_add (1 / 6) u
    have : 0 ≤ ∫ t in (1 / 6)..u, Gs t := by
      have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hu.le
        (intervalIntegrable_const (c := (0 : ℝ))) (Gs_int (1 / 6) u) fun x hx =>
          Gs_nonneg_mid ⟨hx.1, lt_of_lt_of_le hx.2 hu'⟩
      simpa using this
    linarith
  · -- `C(u) = −C(1 − u)` with `1 − u ∈ [0, 1/6)`, where `C ≤ 0`
    have e := Cl_one_sub (1 - u)
    rw [sub_sub_cancel] at e
    have h1u : Cl (1 - u) ≤ 0 := by
      unfold Cl
      have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (by linarith : (0 : ℝ) ≤ 1 - u)
        (Gs_int 0 (1 - u)) (intervalIntegrable_const (c := (0 : ℝ))) fun x hx =>
          Gs_nonpos_small ⟨hx.1, by linarith [hx.2]⟩
      simpa using this
    have := Cl_sixth_nonpos
    linarith

/-- **The Clausen bound** `|Cl₂| ≤ Cl₂(π/3)`, in the form `|∫₀^u log|2 sin πt| dt| ≤ κ/2`.
Proved: the sign of `log|2 sin πt|` on `(0, 1/6)` and `(1/6, 5/6)`, `C(1 − u) = −C(u)` and the
periodicity, through `∫₀¹ log|2 sin πt| dt = 0`. -/
theorem abs_Cl_le (u : ℝ) : |Cl u| ≤ kappa / 2 := by
  have hf : Cl u = Cl (Int.fract u) := by
    have := Cl_periodic.sub_int_mul_eq (x := u) ⌊u⌋
    rw [mul_one] at this
    rw [Int.fract, this]
  rw [hf]
  have h0 := Int.fract_nonneg u
  have h1 := (Int.fract_lt_one u).le
  have hlo := Cl_ge_unit h0 h1
  have hhi : Cl (Int.fract u) ≤ -Cl (1 / 6) := by
    have := Cl_ge_unit (u := 1 - Int.fract u) (by linarith) (by linarith)
    rw [Cl_one_sub] at this; linarith
  unfold kappa
  rw [abs_le]; constructor <;> linarith

/-- **Averages of `G(d· + c)`**: `|X⁻¹ ∫₀^X log|2 sin π(dx + c)| dx| ≤ κ/(dX)` for `d, X > 0`. -/
theorem abs_avg_Gs_le {d X : ℝ} (hd : 0 < d) (hX : 0 < X) (c : ℝ) :
    |(∫ x in (0 : ℝ)..X, Gs (d * x + c)) / X| ≤ kappa / (d * X) := by
  rw [intervalIntegral.integral_comp_mul_add Gs hd.ne' c, mul_zero, zero_add, smul_eq_mul]
  have e : ∫ x in c..d * X + c, Gs x = Cl (d * X + c) - Cl c := by rw [Cl_add c (d * X + c)]; ring
  rw [e, abs_div, abs_of_pos hX, abs_mul, abs_inv, abs_of_pos hd,
    div_le_div_iff₀ hX (by positivity)]
  have h1 := abs_Cl_le (d * X + c)
  have h2 := abs_Cl_le c
  have h3 : |Cl (d * X + c) - Cl c| ≤ kappa := by
    calc |Cl (d * X + c) - Cl c| ≤ |Cl (d * X + c)| + |Cl c| := abs_sub _ _
      _ ≤ kappa := by linarith
  have : d⁻¹ * |Cl (d * X + c) - Cl c| * (d * X) = |Cl (d * X + c) - Cl c| * X := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h3 hX.le

end ArcsAlgo.Core
