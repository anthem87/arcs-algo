module

public import ArcsAlgo.EdgeCore
set_option autoImplicit false

/-!
# Theorem E(2), the core: size of the error terms

* `EI_norm`, `ebC_bound`, `EI_le`: with the normalized cumulants `α₃/s³ ≤ Mx`, `α₄/s⁴ ≤ Mx²`,
  `α₅/s⁵ ≤ Mx³`, `ρ/s⁶ ≤ Mx⁴` (`0 ≤ x ≤ 1 ≤ M`), every dropped term `Π_i κ_{j_i}σ^{j_i}` has
  `Σ(j_i − 2) ≥ 3`, and `E_I ≤ 16M³x³Λ/s`.
* `TI_le`: `T_I ≤ M²Λ₂/s`.

No hypothesis.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.Edge

/-- `E_I` in the normalized cumulants `α₃/s³, α₄/s⁴, α₅/s⁵, ρ/s⁶`. -/
theorem EI_norm (α3 α4 α5 ρ : ℝ) {s : ℝ} (hs : 0 < s) :
    EI α3 α4 α5 ρ s = (1 / s) * ∑ i ∈ range 12,
      ebC (α3 / s ^ 3) (α4 / s ^ 4) (α5 / s ^ 5) (ρ / s ^ 6) i * Am (ebM i) := by
  simp only [EI, ebC, ebM, sum_range_succ, sum_range_zero]
  field_simp
  ring

theorem le_M3 {M x : ℝ} (hM : 1 ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {a k : ℕ} (ha : a ≤ 3) (hk : 3 ≤ k) :
    M ^ a * x ^ k ≤ M ^ 3 * x ^ 3 :=
  mul_le_mul (pow_le_pow_right₀ hM ha) (pow_le_pow_of_le_one hx0 hx1 hk) (by positivity) (by positivity)

/-- Each term of `E_I` is `≤ 16M³x³` when `α₃/s³ ≤ Mx`, `α₄/s⁴ ≤ Mx²`, `α₅/s⁵ ≤ Mx³`, `ρ/s⁶ ≤ Mx⁴`. -/
theorem ebC_bound {a3 a4 a5 r M x : ℝ} (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (hr : 0 ≤ r)
    (hM : 1 ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (b3 : a3 ≤ M * x) (b4 : a4 ≤ M * x ^ 2) (b5 : a5 ≤ M * x ^ 3) (br : r ≤ M * x ^ 4) :
    ∀ i ∈ range 12, ebC a3 a4 a5 r i ≤ 16 * (M ^ 3 * x ^ 3) := by
  have hM0 : 0 ≤ M := by linarith
  have p3 : ∀ {u B : ℝ}, 0 ≤ u → u ≤ B → u ^ 3 ≤ B ^ 3 := fun hu h => pow_le_pow_left₀ hu h 3
  have p2 : ∀ {u B : ℝ}, 0 ≤ u → u ≤ B → u ^ 2 ≤ B ^ 2 := fun hu h => pow_le_pow_left₀ hu h 2
  have m2 : ∀ {u v B C : ℝ}, 0 ≤ u → 0 ≤ v → u ≤ B → v ≤ C → u * v ≤ B * C :=
    fun hu hv h1 h2 => mul_le_mul h1 h2 hv (le_trans hu h1)
  have hM3 : 0 ≤ M ^ 3 * x ^ 3 := by positivity
  intro i hi
  have hi' := mem_range.mp hi
  interval_cases i <;> simp only [ebC]
  · have := p3 h3 b3; have := le_M3 hM hx0 hx1 (a := 3) (k := 3) le_rfl le_rfl
    nlinarith [show (M * x) ^ 3 = M ^ 3 * x ^ 3 by ring]
  · have := p3 h4 b4; have := le_M3 hM hx0 hx1 (a := 3) (k := 6) le_rfl (by norm_num)
    nlinarith [show (M * x ^ 2) ^ 3 = M ^ 3 * x ^ 6 by ring]
  · have := p3 h5 b5; have := le_M3 hM hx0 hx1 (a := 3) (k := 9) le_rfl (by norm_num)
    nlinarith [show (M * x ^ 3) ^ 3 = M ^ 3 * x ^ 9 by ring]
  · have := p3 hr br; have := le_M3 hM hx0 hx1 (a := 3) (k := 12) le_rfl (by norm_num)
    nlinarith [show (M * x ^ 4) ^ 3 = M ^ 3 * x ^ 12 by ring]
  · have := le_M3 hM hx0 hx1 (a := 1) (k := 3) (by norm_num) le_rfl
    nlinarith [show M ^ 1 = M by ring]
  · have := le_M3 hM hx0 hx1 (a := 1) (k := 4) (by norm_num) (by norm_num)
    nlinarith [show M ^ 1 = M by ring]
  · have := m2 h3 h4 b3 b4; have := le_M3 hM hx0 hx1 (a := 2) (k := 3) (by norm_num) le_rfl
    nlinarith [show M * x * (M * x ^ 2) = M ^ 2 * x ^ 3 by ring]
  · have := m2 h3 h5 b3 b5; have := le_M3 hM hx0 hx1 (a := 2) (k := 4) (by norm_num) (by norm_num)
    nlinarith [show M * x * (M * x ^ 3) = M ^ 2 * x ^ 4 by ring]
  · have := m2 h3 hr b3 br; have := le_M3 hM hx0 hx1 (a := 2) (k := 5) (by norm_num) (by norm_num)
    nlinarith [show M * x * (M * x ^ 4) = M ^ 2 * x ^ 5 by ring]
  · have := p2 h4 b4; have := le_M3 hM hx0 hx1 (a := 2) (k := 4) (by norm_num) (by norm_num)
    nlinarith [show (M * x ^ 2) ^ 2 = M ^ 2 * x ^ 4 by ring]
  · have := p2 h5 b5; have := le_M3 hM hx0 hx1 (a := 2) (k := 6) (by norm_num) (by norm_num)
    nlinarith [show (M * x ^ 3) ^ 2 = M ^ 2 * x ^ 6 by ring]
  · have := p2 hr br; have := le_M3 hM hx0 hx1 (a := 2) (k := 8) (by norm_num) (by norm_num)
    nlinarith [show (M * x ^ 4) ^ 2 = M ^ 2 * x ^ 8 by ring]

/-- `Λ = Σ_i A_{m_i}`. -/
noncomputable def LamE : ℝ := ∑ i ∈ range 12, Am (ebM i)

theorem EI_le {α3 α4 α5 ρ s M x : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (h5 : 0 ≤ α5) (hr : 0 ≤ ρ)
    (hM : 1 ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (b3 : α3 / s ^ 3 ≤ M * x) (b4 : α4 / s ^ 4 ≤ M * x ^ 2) (b5 : α5 / s ^ 5 ≤ M * x ^ 3)
    (br : ρ / s ^ 6 ≤ M * x ^ 4) :
    EI α3 α4 α5 ρ s ≤ 16 * (M ^ 3 * x ^ 3) * LamE / s := by
  rw [EI_norm _ _ _ _ hs]
  have hb := ebC_bound (by positivity) (by positivity) (by positivity) (by positivity) hM hx0 hx1 b3 b4 b5 br
  have : ∑ i ∈ range 12, ebC (α3 / s ^ 3) (α4 / s ^ 4) (α5 / s ^ 5) (ρ / s ^ 6) i * Am (ebM i) ≤
      ∑ i ∈ range 12, 16 * (M ^ 3 * x ^ 3) * Am (ebM i) :=
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hb i hi) (Am_nonneg _)
  rw [← mul_sum] at this
  unfold LamE
  rw [one_div_mul_eq_div, div_le_div_iff_of_pos_right hs]
  exact this

/-- `Λ₂ = √2A₀ + 4A₃ + 6A₄ + 6A₆`. -/
noncomputable def LamT : ℝ := √2 * Am 0 + 4 * Am 3 + 6 * Am 4 + 6 * Am 6

theorem TI_le {α3 α4 s M : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (hM : 1 ≤ M)
    (b3 : α3 / s ^ 3 ≤ M) (b4 : α4 / s ^ 4 ≤ M) : TI α3 α4 s ≤ M ^ 2 * LamT / s := by
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : TI α3 α4 s = (1 / s) * (√2 * Am 0 + 4 * (α3 / s ^ 3) * Am 3 + 4 * √2 * (α4 / s ^ 4) * Am 4 +
      4 * √2 * (α3 / s ^ 3) ^ 2 * Am 6) := by
    unfold TI
    have h4' : √2 ^ 4 = 4 := by rw [show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring, hsq]; norm_num
    have h5' : √2 ^ 5 = 4 * √2 := by rw [show √2 ^ 5 = (√2 ^ 2) ^ 2 * √2 by ring, hsq]; norm_num
    have h7' : √2 ^ 7 = 8 * √2 := by rw [show √2 ^ 7 = (√2 ^ 2) ^ 3 * √2 by ring, hsq]; norm_num
    rw [div_pow, div_pow, div_pow, h4', h5', h7']
    field_simp
    ring
  rw [e, one_div_mul_eq_div, div_le_div_iff_of_pos_right hs]
  have a0 := Am_nonneg 0
  have a3 := Am_nonneg 3
  have a4 := Am_nonneg 4
  have a6 := Am_nonneg 6
  have c3 : 0 ≤ α3 / s ^ 3 := by positivity
  have c4 : 0 ≤ α4 / s ^ 4 := by positivity
  have hsq2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have q3 : (α3 / s ^ 3) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ c3 b3 2
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have t1 : √2 * Am 0 ≤ M ^ 2 * (√2 * Am 0) := le_mul_of_one_le_left (by positivity) (by nlinarith)
  have t2 : 4 * (α3 / s ^ 3) * Am 3 ≤ M ^ 2 * (4 * Am 3) := by nlinarith
  have t3 : 4 * √2 * (α4 / s ^ 4) * Am 4 ≤ M ^ 2 * (6 * Am 4) := by
    have : 4 * √2 ≤ 6 := by linarith
    have : 4 * √2 * (α4 / s ^ 4) ≤ 6 * M ^ 2 := by nlinarith
    nlinarith
  have t4 : 4 * √2 * (α3 / s ^ 3) ^ 2 * Am 6 ≤ M ^ 2 * (6 * Am 6) := by
    have : 4 * √2 ≤ 6 := by linarith
    have : 4 * √2 * (α3 / s ^ 3) ^ 2 ≤ 6 * M ^ 2 := by nlinarith
    nlinarith
  unfold LamT; nlinarith

end ArcsAlgo.Edge
