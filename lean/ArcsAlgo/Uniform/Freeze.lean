module

public import ArcsAlgo.LocalLimit.MainRange
set_option autoImplicit false

/-!
# Freezing the variance (paper §6.3, proof of Lemma B(1))

`gPair` is `g_k(a) g_{m−k}(s−a)` written with `A₁ = a − kμ`, `A₂ = s − a − (m−k)μ`; `gPair0` is the
same Gaussian with `k(m−k)` replaced by `m²/4`. `gPair_freeze`: for `m/4 ≤ k ≤ 3m/4`,
`|g − g₀| ≤ (8j²/m² + E) e^E g₀` with `j = k − m/2` and `E = 4|j|(A₁² + A₂²)/(σ²m²)`.
-/

open Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- The product of the two Gaussian factors, with `k(m − k)` and `A₁²/k + A₂²/(m−k)`. -/
noncomputable def gPair (σ2 m k A₁ A₂ : ℝ) : ℝ :=
  1 / (2 * π * σ2 * √(k * (m - k))) * exp (-((A₁ ^ 2 / k + A₂ ^ 2 / (m - k)) / (2 * σ2)))

/-- The same, frozen at `k = m/2`. -/
noncomputable def gPair0 (σ2 m A₁ A₂ : ℝ) : ℝ :=
  1 / (π * σ2 * m) * exp (-((A₁ ^ 2 + A₂ ^ 2) / (m * σ2)))

set_option maxHeartbeats 800000 in
/-- **Freezing the variance.** For `m/4 ≤ k ≤ 3m/4`, with `j = k − m/2`,
`|g − g₀| ≤ (8j²/m² + |D|) e^{|D|} g₀` and `|D| ≤ 4|j|(A₁² + A₂²)/(σ²m²)`. -/
theorem gPair_freeze {σ2 m k A₁ A₂ : ℝ} (hσ : 0 < σ2) (hk1 : m / 4 ≤ k) (hk2 : k ≤ 3 * m / 4)
    (hm : 0 < m) :
    |gPair σ2 m k A₁ A₂ - gPair0 σ2 m A₁ A₂| ≤
      (8 * (k - m / 2) ^ 2 / m ^ 2 + 4 * |k - m / 2| * (A₁ ^ 2 + A₂ ^ 2) / (σ2 * m ^ 2)) *
        exp (4 * |k - m / 2| * (A₁ ^ 2 + A₂ ^ 2) / (σ2 * m ^ 2)) * gPair0 σ2 m A₁ A₂ := by
  have hk : 0 < k := by linarith
  have hmk : 0 < m - k := by linarith
  set j := k - m / 2 with hj
  set D := (A₁ ^ 2 * (1 / k - 2 / m) + A₂ ^ 2 * (1 / (m - k) - 2 / m)) / (2 * σ2) with hD
  set r := m / (2 * √(k * (m - k))) with hr
  have hkm : 0 < k * (m - k) := mul_pos hk hmk
  have hsq := Real.sqrt_pos.mpr hkm
  -- the exact relation g = r e^{−D} g₀
  have hrel : gPair σ2 m k A₁ A₂ = r * exp (-D) * gPair0 σ2 m A₁ A₂ := by
    have hx : exp (-((A₁ ^ 2 / k + A₂ ^ 2 / (m - k)) / (2 * σ2))) =
        exp (-D) * exp (-((A₁ ^ 2 + A₂ ^ 2) / (m * σ2))) := by
      rw [← exp_add]; congr 1; rw [hD]; field_simp; ring
    unfold gPair gPair0
    rw [hx, hr]; field_simp
  -- r ≥ 1 and r − 1 ≤ 8j²/m²
  have hkm' : k * (m - k) = m ^ 2 / 4 - j ^ 2 := by rw [hj]; ring
  have hj2 : j ^ 2 ≤ m ^ 2 / 16 := by
    have : |j| ≤ m / 4 := by rw [abs_le]; constructor <;> linarith
    have h := pow_le_pow_left₀ (abs_nonneg j) this 2
    rw [sq_abs] at h; linarith
  have hr2 : r ^ 2 = m ^ 2 / (4 * (k * (m - k))) := by
    rw [hr, div_pow, mul_pow, Real.sq_sqrt hkm.le]; ring
  have hr0 : 0 ≤ r := by positivity
  have hr1 : 1 ≤ r := by
    have h1 : √(k * (m - k)) ≤ m / 2 := by
      rw [Real.sqrt_le_left (by linarith)]; rw [hkm']; nlinarith [sq_nonneg j]
    rw [hr, le_div_iff₀ (by positivity)]; linarith
  have hrm : r - 1 ≤ 8 * j ^ 2 / m ^ 2 := by
    have h1 : r - 1 ≤ r ^ 2 - 1 := by nlinarith
    have h2 : r ^ 2 - 1 ≤ 8 * j ^ 2 / m ^ 2 := by
      rw [hr2, hkm', div_sub_one (by nlinarith), div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith [sq_nonneg j, sq_nonneg m]
    linarith
  -- |D| ≤ 4|j|(A₁² + A₂²)/(σ² m²)
  have hD1 : |1 / k - 2 / m| ≤ 8 * |j| / m ^ 2 := by
    have e : 1 / k - 2 / m = -(2 * j) / (k * m) := by rw [hj]; field_simp; ring
    rw [e, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < k * m), abs_two,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg (mul_nonneg (abs_nonneg j) hm.le) (by linarith : (0 : ℝ) ≤ 4 * k - m)
    nlinarith
  have hD2 : |1 / (m - k) - 2 / m| ≤ 8 * |j| / m ^ 2 := by
    have e : 1 / (m - k) - 2 / m = (2 * j) / ((m - k) * m) := by rw [hj]; field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (m - k) * m), abs_two,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg (mul_nonneg (abs_nonneg j) hm.le) (by linarith : (0 : ℝ) ≤ 4 * (m - k) - m)
    nlinarith
  have hDb : |D| ≤ 4 * |j| * (A₁ ^ 2 + A₂ ^ 2) / (σ2 * m ^ 2) := by
    rw [hD, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ2)]
    have := abs_add_le (A₁ ^ 2 * (1 / k - 2 / m)) (A₂ ^ 2 * (1 / (m - k) - 2 / m))
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg A₁), abs_of_nonneg (sq_nonneg A₂)] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hD1 (sq_nonneg A₁)
    have h2 := mul_le_mul_of_nonneg_left hD2 (sq_nonneg A₂)
    have e : A₁ ^ 2 * (8 * |j| / m ^ 2) + A₂ ^ 2 * (8 * |j| / m ^ 2) =
        8 * |j| * (A₁ ^ 2 + A₂ ^ 2) / m ^ 2 := by ring
    have hsum : |A₁ ^ 2 * (1 / k - 2 / m) + A₂ ^ 2 * (1 / (m - k) - 2 / m)| ≤
        8 * |j| * (A₁ ^ 2 + A₂ ^ 2) / m ^ 2 := by linarith
    calc |A₁ ^ 2 * (1 / k - 2 / m) + A₂ ^ 2 * (1 / (m - k) - 2 / m)| * (σ2 * m ^ 2)
        ≤ 8 * |j| * (A₁ ^ 2 + A₂ ^ 2) / m ^ 2 * (σ2 * m ^ 2) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = 4 * |j| * (A₁ ^ 2 + A₂ ^ 2) * (2 * σ2) := by field_simp; ring
  -- combine
  set E := 4 * |j| * (A₁ ^ 2 + A₂ ^ 2) / (σ2 * m ^ 2)
  have hE0 : 0 ≤ E := by positivity
  have hg0 : 0 ≤ gPair0 σ2 m A₁ A₂ := by unfold gPair0; positivity
  have hexp := abs_exp_sub_one_le' (-D)
  rw [abs_neg] at hexp
  have hexpD : exp (-D) ≤ exp E := exp_le_exp.mpr (by linarith [neg_abs_le D, le_abs_self (-D), abs_neg D])
  have hexpE : exp |D| ≤ exp E := exp_le_exp.mpr hDb
  have key : |r * exp (-D) - 1| ≤ (8 * j ^ 2 / m ^ 2 + E) * exp E := by
    have e : r * exp (-D) - 1 = (r - 1) * exp (-D) + (exp (-D) - 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - 1), abs_of_pos (exp_pos _)]
    have h1 : (r - 1) * exp (-D) ≤ 8 * j ^ 2 / m ^ 2 * exp E :=
      mul_le_mul hrm hexpD (exp_pos _).le (by positivity)
    have h2 : |exp (-D) - 1| ≤ E * exp E :=
      hexp.trans (mul_le_mul hDb hexpE (exp_pos _).le hE0)
    nlinarith
  rw [hrel, show r * exp (-D) * gPair0 σ2 m A₁ A₂ - gPair0 σ2 m A₁ A₂ =
    (r * exp (-D) - 1) * gPair0 σ2 m A₁ A₂ by ring, abs_mul, abs_of_nonneg hg0]
  exact mul_le_mul_of_nonneg_right key hg0

end ArcsAlgo.LLT
