module

public import ArcsAlgo.Uniform.Sum1
set_option autoImplicit false

/-!
# Lemma B(1) with an explicit error, uniform in `M` (paper §6.3)

* `L_rel`: `|Σ_k C(m,k) p_k(a) p_{m−k}(s−a) − Λ| ≤ δ₁(g,m,T)·Λ` with `Λ = 2^m B₀ √(π/α)`, where
  `δ₁` depends only on `g`, `m` and the width `T` of the typical range.
* `lamB_eq`: `λ = (Σ_k C(m,k) p_k(a) p_{m−k}(s−a)) / Pr(S_E = s)`; `law_rel`:
  `|Pr(S_E = s)/g_m(s) − 1| ≤ δ₂(g,m)` (Lemma B0′); `a_pos`: `a, s − a > 0` in the window.
* `lamB_rel`: `|λ/λ_m − 1| ≤ 2(δ₁ + δ₂ + 3/(2m))` uniformly in `M ≥ 2`, in the window and in
  `|u| ≤ M`, `u ≡ s (mod 2)`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem B0c_sqrt_eq {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) (s u : ℤ) :
    B0c M m s u * √(π / alB M m) =
      exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) * exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M))) /
        (π * m * (√(sig2 M) * √(ew2 M))) := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hπ := pi_pos
  have s1 : √(2 / (π * m)) * √(π / alB M m) = √(sig2 M) / √(ew2 M) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div hσ.le]
    congr 1; unfold alB; field_simp
  have hA : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
  have hB : 0 < √(ew2 M) := Real.sqrt_pos.mpr he
  have hss : √(sig2 M) * √(sig2 M) = sig2 M := Real.mul_self_sqrt hσ.le
  unfold B0c
  calc √(2 / (π * m)) * (1 / (π * sig2 M * m)) * exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) *
        exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M))) * √(π / alB M m)
      = (√(2 / (π * m)) * √(π / alB M m)) * (1 / (π * sig2 M * m)) *
        exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) *
        exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M))) := by ring
    _ = _ := by
      rw [s1]
      have hq : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hσ.le
      field_simp
      rw [hq]

/-- The constant `c₀ = e^{−g²/2 − 3/2}`. -/
noncomputable def c0g (g : ℝ) : ℝ := exp (-(g ^ 2 / 2 + 3 / 2))

theorem B0c_sqrt_ge {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} {s u : ℤ}
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) :
    c0g g / (π * m * (√(sig2 M) * √(ew2 M))) ≤ B0c M m s u * √(π / alB M m) := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [B0c_sqrt_eq hM hm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold c0g
  rw [show -(g ^ 2 / 2 + 3 / 2) = -(g ^ 2 / 2) + -(3 / 2) by ring, exp_add]
  apply mul_le_mul _ _ (exp_pos _).le (exp_pos _).le
  · apply exp_le_exp.mpr
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hm0.le] at h
    rw [neg_le_neg_iff, div_le_iff₀ (by positivity)]; nlinarith
  · apply exp_le_exp.mpr
    have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
    have h := pow_le_pow_left₀ (abs_nonneg _) hu' 2
    rw [sq_abs] at h
    have := ew2_ge (M := M)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [neg_le_neg_iff, div_le_iff₀ (by positivity)]; nlinarith

/-- The relative error of the first moment, uniform in `M`. -/
noncomputable def del1 (g : ℝ) (m T : ℕ) : ℝ :=
  3808 * π * √17 / (c0g g * m) + (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) +
    rhoT g m T * (1 + RT m T / √(π * m / 34)) + RT m T / √(π * m / 34) +
    2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g)

theorem ew2_le {M : ℕ} (hM : 2 ≤ M) : ew2 M ≤ 17 * sig2 M := by
  rw [ew2_eq]; linarith [muW_sq_le hM]

set_option maxHeartbeats 1000000 in
/-- **Lemma B(1), the sum**: `|Σ_k C(m,k)p_k(a)p_{m−k}(s−a) − Λ| ≤ δ₁(g,m,T)·Λ`, `Λ = 2^m B₀√(π/α)`. -/
theorem L_rel {M m : ℕ} (hM : 2 ≤ M) {g : ℝ} {s u a : ℤ} (ha : 2 * a = s + u)
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) (ha0 : a ≠ 0)
    (hsa0 : s - a ≠ 0) {T : ℕ} (hT : 3 ≤ T) (hTm : 4 * T + 8 ≤ m) :
    |∑ k ∈ range (m + 1), (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a)) -
        2 ^ m * B0c M m s u * √(π / alB M m)| ≤
      del1 g m T * (2 ^ m * B0c M m s u * √(π / alB M m)) := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hπ := pi_pos
  set k₀ := m / 2 - T
  have hsub : Ico k₀ (k₀ + (2 * T + 1)) ⊆ range (m + 1) := by
    intro k hk; rw [mem_Ico] at hk; rw [mem_range]; omega
  have hsplit := sum_sdiff hsub (f := fun k => (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a)))
  have hIco : ∑ k ∈ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a)) =
      ∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) *
        (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) := by
    rw [sum_Ico_eq_sum_range]; simp
  have htyp := typ_sum hM ha hw hu hT hTm
  have htail := tail_sum hM ha0 hsa0 hT hTm
  have htail0 : 0 ≤ ∑ k ∈ range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) *
      (lawS M k a * lawS M (m - k) (s - a)) :=
    sum_nonneg fun k _ => mul_nonneg (by positivity) (mul_nonneg (by unfold lawS; positivity)
      (by unfold lawS; positivity))
  rw [← hsplit, hIco]
  set Λ := 2 ^ m * B0c M m s u * √(π / alB M m)
  set P := √(sig2 M) * √(ew2 M)
  have hP0 : 0 < P := by positivity
  have hP : P ≤ √17 * sig2 M := by
    have h1 : P = √(sig2 M * ew2 M) := (Real.sqrt_mul hσ.le _).symm
    have h2 : √17 * sig2 M = √(17 * sig2 M ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hσ.le]
    rw [h1, h2]; apply Real.sqrt_le_sqrt
    calc sig2 M * ew2 M ≤ sig2 M * (17 * sig2 M) := mul_le_mul_of_nonneg_left (ew2_le hM) hσ.le
      _ = 17 * sig2 M ^ 2 := by ring
  have hc0 : 0 < c0g g := by unfold c0g; positivity
  have hΛ : 2 ^ m * (c0g g / (π * m * P)) ≤ Λ := by
    rw [show Λ = 2 ^ m * (B0c M m s u * √(π / alB M m)) by simp only [Λ]; ring]
    exact mul_le_mul_of_nonneg_left (B0c_sqrt_ge hM hm1 hw hu) (by positivity)
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  have hsq : √(π * m / 34) ≤ √(π / alB M m) := by
    apply Real.sqrt_le_sqrt
    unfold alB; rw [div_div_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    have := mul_le_mul_of_nonneg_left (ew2_le hM) (by positivity : (0 : ℝ) ≤ π * m * 2)
    nlinarith
  have hsq0 : 0 < √(π * m / 34) := Real.sqrt_pos.mpr (by positivity)
  have hRT0 : 0 ≤ RT m T := by
    unfold RT
    have : (3 : ℝ) ≤ T := by exact_mod_cast hT
    have : 0 < 2 * ((T : ℝ) - 2) := by linarith
    positivity
  have hρ0 : 0 ≤ rhoT g m T := by unfold rhoT; positivity
  -- the five pieces
  have p1 : 2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) ≤ 3808 * π * √17 / (c0g g * m) * Λ := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hΛ (by positivity))
    rw [show 3808 * π * √17 / (c0g g * m) * (2 ^ m * (c0g g / (π * m * P))) =
      2 ^ m * (3808 * √17 / ((m : ℝ) ^ 2 * P)) by field_simp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 3808 * (m : ℝ) ^ 2)]
  have p2 : (2 * T + 1) * (2 ^ m * (136 / (sig2 M * (m : ℝ) ^ 2 * √(m : ℝ)))) ≤
      (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) * Λ := by
    have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hΛ (by positivity))
    rw [show (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) * (2 ^ m * (c0g g / (π * m * P))) =
      (2 * T + 1) * (2 ^ m * (136 * √17 / ((m : ℝ) ^ 2 * √(m : ℝ) * P))) by field_simp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 136 * (m : ℝ) ^ 2 * √(m : ℝ))]
  have hBR : 2 ^ m * B0c M m s u * RT m T ≤ RT m T / √(π * m / 34) * Λ := by
    have hB0 : 0 ≤ 2 ^ m * B0c M m s u := by unfold B0c; positivity
    rw [show RT m T / √(π * m / 34) * Λ = 2 ^ m * B0c M m s u * RT m T * (√(π / alB M m) / √(π * m / 34)) by
      simp only [Λ]; field_simp]
    have : 1 ≤ √(π / alB M m) / √(π * m / 34) := by rw [le_div_iff₀ hsq0]; linarith
    nlinarith [mul_nonneg hB0 hRT0]
  have p3 : rhoT g m T * (2 ^ m * B0c M m s u * (√(π / alB M m) + RT m T)) ≤
      rhoT g m T * (1 + RT m T / √(π * m / 34)) * Λ := by
    have h : 2 ^ m * B0c M m s u * (√(π / alB M m) + RT m T) ≤ (1 + RT m T / √(π * m / 34)) * Λ := by
      have e1 : 2 ^ m * B0c M m s u * (√(π / alB M m) + RT m T) = Λ + 2 ^ m * B0c M m s u * RT m T := by
        simp only [Λ]; ring
      rw [e1, add_mul, one_mul]; linarith [hBR]
    calc rhoT g m T * (2 ^ m * B0c M m s u * (√(π / alB M m) + RT m T))
        ≤ rhoT g m T * ((1 + RT m T / √(π * m / 34)) * Λ) := mul_le_mul_of_nonneg_left h hρ0
      _ = _ := by ring
  have p5 : 2 * 2 ^ m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (M : ℝ) ^ 2 ≤
      2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g) * Λ := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hΛ (by positivity))
    rw [show 2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g) *
      (2 ^ m * (c0g g / (π * m * P))) = 2 * 2 ^ m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) * (√17 / (12 * P)) by
      field_simp]
    rw [div_eq_mul_one_div (2 * 2 ^ m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hs : 12 * sig2 M ≤ (M : ℝ) ^ 2 := by unfold sig2; linarith
    have := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 17)
    nlinarith [mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 12)]
  have habs := abs_sub_le (∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) *
        (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) +
      ∑ k ∈ range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) *
        (lawS M k a * lawS M (m - k) (s - a)))
    (∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) *
        (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a))) Λ
  rw [add_sub_cancel_left, abs_of_nonneg htail0] at habs
  unfold del1
  have e : (3808 * π * √17 / (c0g g * m) + (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) +
    rhoT g m T * (1 + RT m T / √(π * m / 34)) + RT m T / √(π * m / 34) +
    2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g)) * Λ =
      3808 * π * √17 / (c0g g * m) * Λ + (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) * Λ +
      rhoT g m T * (1 + RT m T / √(π * m / 34)) * Λ + RT m T / √(π * m / 34) * Λ +
      2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g) * Λ := by ring
  rw [e]
  have htyp' := htyp
  rw [add_comm (∑ k ∈ range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)), _)] at *
  linarith [habs, htyp', htail, p1, p2, p3, hBR, p5]

theorem cntS_eq {M : ℕ} (hM : 0 < M) (m : ℕ) (s : ℤ) :
    (cntS M m s : ℝ) = (M : ℝ) ^ m * lawS M m s := by
  have hM' : (M : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM.ne')
  unfold cntS lawS
  rw [mul_div_cancel₀ _ hM']; rfl

/-- `λ = (Σ_k C(m,k) p_k(a) p_{m−k}(s−a)) / Pr(S_E = s)`. -/
theorem lamB_eq {M m : ℕ} (hM : 2 ≤ M) (s u a : ℤ) (ha : 2 * a = s + u) :
    lamB M m s u = (∑ k ∈ range (m + 1), (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a))) /
      lawS M m s := by
  have hM0 : (0 : ℝ) < (M : ℝ) ^ m := by
    have : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    positivity
  rw [← sumZ_eq (by omega) s u a ha, lamB, cntS_eq (by omega), div_div]

/-- In the window, for `√m ≥ g + 2`, both `a` and `s − a` are positive. -/
theorem a_pos {M m : ℕ} (hM : 2 ≤ M) {g : ℝ} (hg : 0 ≤ g) (hmg : g + 2 ≤ √(m : ℝ)) {s u a : ℤ}
    (ha : 2 * a = s + u) (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) :
    0 < a ∧ 0 < s - a := by
  have hσ := sig2_pos hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hs12 : √(sig2 M) ≤ M / 3 := by
    rw [Real.sqrt_le_left (by positivity)]; unfold sig2; nlinarith
  have hsm := Real.sqrt_nonneg (m : ℝ)
  have hmm : (m : ℝ) = √(m : ℝ) * √(m : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
  have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
  have hu1 := (abs_le.mp hu').1
  have hu2 := (abs_le.mp hu').2
  have hw1 := (abs_le.mp hw).1
  have hgs : g * √(sig2 M) * √(m : ℝ) ≤ g * (M / 3) * √(m : ℝ) := by gcongr
  have key : (M : ℝ) * (1 : ℝ) < m * muW M - g * (M / 3) * √(m : ℝ) - M := by
    unfold muW
    have : (g + 2) * √(m : ℝ) ≤ √(m : ℝ) * √(m : ℝ) := mul_le_mul_of_nonneg_right hmg hsm
    nlinarith [mul_nonneg hg hsm]
  have haR : (2 : ℝ) * a = s + u := by exact_mod_cast ha
  constructor
  · have : (0 : ℝ) < a := by nlinarith
    exact_mod_cast this
  · have : (0 : ℝ) < (s : ℝ) - a := by nlinarith
    exact_mod_cast (show (0 : ℝ) < ((s - a : ℤ) : ℝ) by push_cast; exact this)

theorem ratio3 {r x q d1 d2 d3 : ℝ} (h1 : |r - 1| ≤ d1) (hx1 : 1 - d3 ≤ x) (hx2 : x ≤ 1)
    (h2 : |q - 1| ≤ d2) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) (hD : d1 + d2 + d3 ≤ 1 / 2) :
    |r * x / q - 1| ≤ 2 * (d1 + d2 + d3) := by
  obtain ⟨r1, r2⟩ := abs_le.mp h1
  obtain ⟨q1, q2⟩ := abs_le.mp h2
  have hq : 0 < q := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hr0 : 0 ≤ r := by linarith
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hq]
    have : (1 - d1) * (1 - d3) ≤ r * x := mul_le_mul (by linarith) hx1 (by linarith) hr0
    nlinarith [mul_nonneg hd1 hd3, mul_nonneg (by linarith : (0 : ℝ) ≤ d1 + d2 + d3) hd2]
  · rw [sub_le_iff_le_add, div_le_iff₀ hq]
    have : r * x ≤ (1 + d1) * 1 := mul_le_mul (by linarith) hx2 hx0 (by linarith)
    nlinarith [mul_nonneg hd1 (by linarith : (0 : ℝ) ≤ 1 - 2 * d2), mul_nonneg hd2 (by linarith : (0 : ℝ) ≤ 1 - 2 * d2),
      mul_nonneg hd3 (by linarith : (0 : ℝ) ≤ 1 - d2)]

/-- The relative error of `Pr(S_E = s)` against `g_m(s)` in the window. -/
noncomputable def del2 (g : ℝ) (m : ℕ) : ℝ := 17 * √(2 * π) * exp (g ^ 2 / 2) / m

theorem law_rel {M m : ℕ} (hM : 2 ≤ M) (hm : 2 ≤ m) {g : ℝ} {s : ℤ}
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) :
    |lawS M m s / gaussB M m s - 1| ≤ del2 g m := by
  have hσ := sig2_pos hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsσ := Real.sqrt_pos.mpr hσ
  have hsm := Real.sqrt_pos.mpr hm0
  have hz : zB M m s ^ 2 ≤ g ^ 2 := by
    unfold zB tB
    rw [div_pow, div_le_iff₀ (by positivity), mul_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs, mul_pow, mul_pow] at h
    linarith
  have hG : exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ))) ≤ gaussB M m s := by
    unfold gaussB
    have e : √(2 * π * m * sig2 M) = √(2 * π) * (√(sig2 M) * √(m : ℝ)) := by
      rw [show 2 * π * m * sig2 M = (2 * π) * (sig2 M * m) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_mul hσ.le]
    rw [e, one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact exp_le_exp.mpr (by linarith)
  have hG0 : 0 < gaussB M m s := lt_of_lt_of_le (by positivity) hG
  have hB := lemmaB0'_gauss hM hm s
  have hCB := CB_le hM hm
  rw [div_sub_one hG0.ne', abs_div, abs_of_pos hG0, div_le_iff₀ hG0]
  refine hB.trans ?_
  calc CB M m / (√(sig2 M) * (m * √(m : ℝ))) ≤ 17 / (√(sig2 M) * (m * √(m : ℝ))) := by gcongr
    _ = del2 g m * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) := by
        unfold del2
        have : exp (g ^ 2 / 2) * exp (-(g ^ 2 / 2)) = 1 := by rw [← exp_add]; simp
        have hπ : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
        field_simp
        rw [this]
    _ ≤ del2 g m * gaussB M m s := by
        apply mul_le_mul_of_nonneg_left hG; unfold del2; positivity

set_option maxHeartbeats 1000000 in
/-- **Lemma B(1), with an explicit error uniform in `M`**:
`|λ/λ_m − 1| ≤ 2(δ₁(g,m,T) + δ₂(g,m) + 3/(2m))` whenever this sum is `≤ 1/2`. -/
theorem lamB_rel {M m : ℕ} (hM : 2 ≤ M) {g : ℝ} (hg : 0 ≤ g) (hmg : g + 2 ≤ √(m : ℝ)) {s u : ℤ}
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) (hsu : (2 : ℤ) ∣ u - s)
    {T : ℕ} (hT : 3 ≤ T) (hTm : 4 * T + 8 ≤ m)
    (hD : del1 g m T + del2 g m + 3 / (2 * m) ≤ 1 / 2) :
    |lamB M m s u / lamM M m - 1| ≤ 2 * (del1 g m T + del2 g m + 3 / (2 * m)) := by
  obtain ⟨k, hk⟩ := hsu
  set a := s + k with ha'
  have ha : 2 * a = s + u := by rw [ha']; linarith
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨ha0, hsa0⟩ := a_pos hM hg hmg ha hw hu
  have hL := L_rel hM ha hw hu ha0.ne' hsa0.ne' hT hTm
  have hmain := main_term_eq hM hm1 s u
  have hp := law_rel hM (by omega) hw
  rw [lamB_eq hM s u a ha]
  set L := ∑ k ∈ range (m + 1), (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a))
  set Λ := 2 ^ m * B0c M m s u * √(π / alB M m)
  set x := exp (-(1 / 2) * smQ1 M m u)
  have hc0 : 0 < c0g g := by unfold c0g; positivity
  have hΛ0 : 0 < Λ := by
    have hσ := sig2_pos hM
    have he : 0 < ew2 M := by unfold ew2; positivity
    have h := B0c_sqrt_ge hM hm1 hw hu
    have : 0 < 2 ^ m * (B0c M m s u * √(π / alB M m)) :=
      mul_pos (by positivity) (lt_of_lt_of_le (by positivity) h)
    simpa [Λ, mul_assoc] using this
  have hlM : 0 < lamM M m := by unfold lamM cMB; positivity
  have hx0 : 0 < x := exp_pos _
  have hGpos : 0 < gaussB M m s := by unfold gaussB; have := sig2_pos hM; positivity
  -- x ∈ [1 − 3/(2m), 1]
  have hQ1 : smQ1 M m u ≤ 3 / m := by
    have := smQ1_le (M := M) hm1 hu
    have he3 := ew2_ge (M := M)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    refine this.trans ?_
    rw [div_div, div_le_div_iff₀ (by unfold ew2; positivity) hm0]
    nlinarith
  have hQ0 : 0 ≤ smQ1 M m u := by unfold smQ1; have := ew2_pos M; positivity
  have hx1 : x ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hx2 : 1 - 3 / (2 * m) ≤ x := by
    have := add_one_le_exp (-(1 / 2) * smQ1 M m u)
    have : 3 / (2 * (m : ℝ)) = (1 / 2) * (3 / m) := by field_simp
    nlinarith
  have hr : |L / Λ - 1| ≤ del1 g m T := by
    rw [div_sub_one hΛ0.ne', abs_div, abs_of_pos hΛ0, div_le_iff₀ hΛ0]; exact hL
  have hd1 : 0 ≤ del1 g m T := le_trans (abs_nonneg _) hr
  have hd2 : 0 ≤ del2 g m := le_trans (abs_nonneg _) hp
  have h3 := ratio3 hr hx2 hx1 hp hd1 hd2 (by positivity) hD
  have e : L / lawS M m s / lamM M m = L / Λ * x / (lawS M m s / gaussB M m s) := by
    rw [hmain]; field_simp
  rw [e]; exact h3

end ArcsAlgo.LLT
