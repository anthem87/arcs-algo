module

public import ArcsAlgo.Uniform.B1
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false

/-!
# Lemma B(1), uniformly in `M` (paper §6.3)

`lemmaB1_unif`: for fixed `g ≥ 0` and every `ε > 0` there is `m₀` such that for all `M ≥ 2`,
`m ≥ m₀`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`, `u ≡ s (mod 2)`: `|λ/λ_m − 1| ≤ ε`, where
`λ = E[Z(u) | S_E = s]` and `λ_m = 2^{m+1}/(M√(2πm c_M))`.

The proof takes the typical range `|k − m/2| ≤ T` with `T = ⌊m^{3/5}⌋` (`Tm`), so that the
error of `lamB_rel` is at most `Φ(m^{1/5})` (`del_le_Phi1`) and `Φ(y) → 0` (`tendsto_Phi1`).
Only Lemma B0′ enters (for the weights, and with `M = 2` for the binomial); no hypothesis.
-/

open Finset Real Filter Topology

@[expose] public section

namespace ArcsAlgo.LLT

/-- The majorant `Φ(y)` of the error of Lemma B(1), with `y = m^{1/5}`. -/
noncomputable def PhiE (g y : ℝ) : ℝ := 4 * g ^ 2 * y⁻¹ ^ 2 + 128 * y⁻¹ ^ 7 + 2048 * y⁻¹

noncomputable def Phi1 (g y : ℝ) : ℝ :=
  3808 * π * √17 / c0g g * y⁻¹ ^ 5 + 408 * π * √17 / c0g g * y⁻¹ ^ 4 +
    (32 * y⁻¹ ^ 4 + PhiE g y) * exp (PhiE g y) * (1 + √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2)))) +
    √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2))) +
    2 * π * √17 / (12 * c0g g) * (y ^ 5 * exp (-(y / 2))) +
    17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 + 3 / 2 * y⁻¹ ^ 5

theorem tendsto_Phi1 (g : ℝ) : Tendsto (Phi1 g) atTop (𝓝 0) := by
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hip : ∀ n : ℕ, 0 < n → Tendsto (fun y : ℝ => y⁻¹ ^ n) atTop (𝓝 0) := fun n hn => by
    simpa [zero_pow hn.ne'] using hi.pow n
  have hex : Tendsto (fun y : ℝ => exp (-(y / 2))) atTop (𝓝 0) := by
    apply tendsto_exp_neg_atTop_nhds_zero.comp
    exact tendsto_id.atTop_div_const (by norm_num)
  have hy5 : Tendsto (fun y : ℝ => y ^ 5 * exp (-(y / 2))) atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := h.const_mul 32
    simp only [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp, id]; ring
  have hE : Tendsto (PhiE g) atTop (𝓝 0) := by
    have := ((hip 2 (by norm_num)).const_mul (4 * g ^ 2)).add (((hip 7 (by norm_num)).const_mul 128).add
      (hi.const_mul 2048))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun y => ?_
    unfold PhiE; ring
  have hR : Tendsto (fun y : ℝ => √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2)))) atTop (𝓝 0) := by
    have := (((hip 2 (by norm_num)).const_mul 2).add hex).const_mul (√(34 / π))
    simpa using this
  have hrho : Tendsto (fun y : ℝ => (32 * y⁻¹ ^ 4 + PhiE g y) * exp (PhiE g y) *
      (1 + √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2))))) atTop (𝓝 0) := by
    have h1 := ((hip 4 (by norm_num)).const_mul 32).add hE
    have h2 := (Real.continuous_exp.tendsto 0).comp hE
    have h3 := tendsto_const_nhds (x := (1 : ℝ)) |>.add hR
    have := (h1.mul h2).mul h3
    simpa using this
  have := ((((((hip 5 (by norm_num)).const_mul (3808 * π * √17 / c0g g)).add
    ((hip 4 (by norm_num)).const_mul (408 * π * √17 / c0g g))).add hrho).add hR).add
    (hy5.const_mul (2 * π * √17 / (12 * c0g g)))).add
    ((hip 5 (by norm_num)).const_mul (17 * √(2 * π) * exp (g ^ 2 / 2)))
  have := this.add ((hip 5 (by norm_num)).const_mul (3 / 2))
  simp only [mul_zero, add_zero] at this
  exact this.congr fun y => rfl

/-- The width of the typical range: `T = ⌊m^{3/5}⌋`. -/
noncomputable def Tm (m : ℕ) : ℕ := ⌊((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 3⌋₊

theorem y_pow_five (m : ℕ) : ((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num

set_option maxHeartbeats 1000000 in
theorem del_le_Phi1 {g : ℝ} (hg : 0 ≤ g) {m : ℕ} (hy : 3 ≤ (m : ℝ) ^ ((1 : ℝ) / 5)) :
    del1 g m (Tm m) + del2 g m + 3 / (2 * m) ≤ Phi1 g ((m : ℝ) ^ ((1 : ℝ) / 5)) := by
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hy0 : 0 < y := by linarith
  have hm : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hm0 : (0 : ℝ) < m := by rw [hm]; positivity
  set T := Tm m
  have hT1 : (T : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hT2 : y ^ 3 - 1 < T := by have := Nat.lt_floor_add_one (y ^ 3); simp only [T, Tm]; linarith
  have hy3 : 27 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
  have hTa : (T : ℝ) + 1 ≤ 2 * y ^ 3 := by linarith
  have hTb : y ^ 3 / 2 ≤ (T : ℝ) - 2 := by linarith
  have hTc : y ^ 3 / 2 ≤ (T : ℝ) - 1 := by linarith
  have hsm : y ^ 2 ≤ √(m : ℝ) := by
    rw [hm, show y ^ 5 = (y ^ 2) ^ 2 * y by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have : 1 ≤ √y := by rw [Real.le_sqrt (by norm_num) hy0.le]; linarith
    nlinarith [sq_nonneg y]
  have hc0 : 0 < c0g g := by unfold c0g; positivity
  have hyi : ∀ n : ℕ, y⁻¹ ^ n = 1 / y ^ n := fun n => by rw [inv_pow, one_div]
  -- the exponential pieces
  have hexp : ∀ d : ℝ, y ^ 3 / 2 ≤ d → exp (-(2 * d ^ 2 / m)) ≤ exp (-(y / 2)) := by
    intro d hd
    apply exp_le_exp.mpr
    rw [neg_le_neg_iff, hm, le_div_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (by positivity) hd 2
    nlinarith
  have hRT : RT m T ≤ 2 + y ^ 2 * exp (-(y / 2)) := by
    unfold RT
    have h1 := hexp _ hTb
    have h2 : (m : ℝ) / (2 * ((T : ℝ) - 2)) ≤ y ^ 2 := by
      rw [div_le_iff₀ (by linarith), hm]; nlinarith
    have : (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (2 * ((T : ℝ) - 2)) =
        (m : ℝ) / (2 * ((T : ℝ) - 2)) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) := by ring
    rw [this]
    have := mul_le_mul h2 h1 (exp_pos _).le (by positivity)
    linarith
  have hsq : √(π / 34) * y ^ 2 ≤ √(π * m / 34) := by
    rw [show π * (m : ℝ) / 34 = π / 34 * m by ring, Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_left hsm (Real.sqrt_nonneg _)
  have hRq : RT m T / √(π * m / 34) ≤ √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2))) := by
    have hRT0 : 0 ≤ RT m T := by unfold RT; have : 0 < 2 * ((T : ℝ) - 2) := by linarith
                                 positivity
    have hp : 0 < √(π / 34) := Real.sqrt_pos.mpr (by positivity)
    calc RT m T / √(π * m / 34) ≤ (2 + y ^ 2 * exp (-(y / 2))) / (√(π / 34) * y ^ 2) :=
          div_le_div₀ (by positivity) hRT (by positivity) hsq
      _ = √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2))) := by
          rw [hyi, show √(34 / π) = 1 / √(π / 34) by
            rw [Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by norm_num)]; field_simp]
          field_simp
  have hE : 2 * ((T : ℝ) + 1) * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / (m : ℝ) ^ 2 ≤ PhiE g y := by
    unfold PhiE
    rw [hyi, hyi, inv_eq_one_div, div_le_iff₀ (by positivity), hm]
    have h1 : ((T : ℝ) + 1) ^ 2 ≤ (2 * y ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hTa 2
    have hT0 : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
    have h2 : 2 * ((T : ℝ) + 1) * (g ^ 2 * y ^ 5 + 32 + 128 * ((T : ℝ) + 1) ^ 2) ≤
        2 * (2 * y ^ 3) * (g ^ 2 * y ^ 5 + 32 + 128 * (2 * y ^ 3) ^ 2) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have e : (4 * g ^ 2 * (1 / y ^ 2) + 128 * (1 / y ^ 7) + 2048 * (1 / y)) * (y ^ 5) ^ 2 =
        2 * (2 * y ^ 3) * (g ^ 2 * y ^ 5 + 32 + 128 * (2 * y ^ 3) ^ 2) := by field_simp; ring
    linarith
  have hA : 8 * ((T : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 ≤ 32 * y⁻¹ ^ 4 := by
    rw [hyi, hm, div_le_iff₀ (by positivity)]
    have h1 : ((T : ℝ) + 1) ^ 2 ≤ (2 * y ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hTa 2
    have e : 32 * (1 / y ^ 4) * (y ^ 5) ^ 2 = 8 * (2 * y ^ 3) ^ 2 := by field_simp; ring
    linarith
  have hEn : 0 ≤ 2 * ((T : ℝ) + 1) * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / (m : ℝ) ^ 2 := by
    positivity
  have hrho : rhoT g m T ≤ (32 * y⁻¹ ^ 4 + PhiE g y) * exp (PhiE g y) := by
    unfold rhoT
    exact mul_le_mul (by linarith) (exp_le_exp.mpr hE) (exp_pos _).le (by unfold PhiE; positivity)
  have hRq0 : 0 ≤ RT m T / √(π * m / 34) := by
    have : 0 < 2 * ((T : ℝ) - 2) := by linarith
    unfold RT; positivity
  have hrho0 : 0 ≤ rhoT g m T := by unfold rhoT; positivity
  have p3 : rhoT g m T * (1 + RT m T / √(π * m / 34)) ≤ (32 * y⁻¹ ^ 4 + PhiE g y) * exp (PhiE g y) *
      (1 + √(34 / π) * (2 * y⁻¹ ^ 2 + exp (-(y / 2)))) :=
    mul_le_mul hrho (by linarith) (by positivity) (by unfold PhiE; positivity)
  have p1 : 3808 * π * √17 / (c0g g * m) = 3808 * π * √17 / c0g g * y⁻¹ ^ 5 := by
    rw [hyi, hm]; field_simp
  have p2 : (2 * T + 1) * (136 * π * √17) / (c0g g * m * √(m : ℝ)) ≤ 408 * π * √17 / c0g g * y⁻¹ ^ 4 := by
    rw [hyi, div_le_iff₀ (by positivity)]
    have hk : 0 < 136 * π * √17 := by positivity
    have h1 : (2 * (T : ℝ) + 1) ≤ 3 * y ^ 3 := by nlinarith
    have h2 : y ^ 7 ≤ (m : ℝ) * √(m : ℝ) := by
      calc y ^ 7 = y ^ 5 * y ^ 2 := by ring
        _ = (m : ℝ) * y ^ 2 := by rw [hm]
        _ ≤ (m : ℝ) * √(m : ℝ) := mul_le_mul_of_nonneg_left hsm hm0.le
    have e : 408 * π * √17 / c0g g * (1 / y ^ 4) * (c0g g * m * √(m : ℝ)) =
        3 * (136 * π * √17) * ((m : ℝ) * √(m : ℝ)) / y ^ 4 := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have p5 : 2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g) ≤
      2 * π * √17 / (12 * c0g g) * (y ^ 5 * exp (-(y / 2))) := by
    have := hexp _ hTc
    calc 2 * π * √17 * m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (12 * c0g g)
        = 2 * π * √17 / (12 * c0g g) * ((m : ℝ) * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m))) := by ring
      _ ≤ 2 * π * √17 / (12 * c0g g) * (y ^ 5 * exp (-(y / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hm]; exact mul_le_mul_of_nonneg_left this hm0.le
  have p6 : del2 g m = 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
    unfold del2; rw [hyi, hm]; field_simp
  have p7 : 3 / (2 * (m : ℝ)) = 3 / 2 * y⁻¹ ^ 5 := by rw [hyi, hm]; field_simp
  unfold del1 Phi1
  rw [p1, p6, p7]
  linarith

/-- **Lemma B(1), uniformly in `M`** (paper §6.3): for fixed `g ≥ 0`, `λ = λ_m(1 + o(1))` uniformly
in `M ≥ 2`, in the window `|s − mμ| ≤ gσ√m` and in `|u| ≤ M`, `u ≡ s (mod 2)`. Only Lemma B0′
(proved) enters; no hypothesis. -/
theorem lemmaB1_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      |lamB M m s u / lamM M m - 1| ≤ ε := by
  have hev := (tendsto_Phi1 g).eventually (gt_mem_nhds (show (0 : ℝ) < min (ε / 2) (1 / 2) by positivity))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev
  set Y := max (max Y₁ 3) (g + 2)
  have hY0 : 0 ≤ Y := le_trans (by norm_num) (le_trans (le_max_right Y₁ 3) (le_max_left _ _))
  refine ⟨⌈Y ^ 5⌉₊, fun M m hM hm s u hw hu hsu => ?_⟩
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hm' : Y ^ 5 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hyY : Y ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hY0, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
      Real.rpow_one] at h
  have hy3 : 3 ≤ y := le_trans (le_trans (le_max_right Y₁ 3) (le_max_left _ _)) hyY
  have hyg : g + 2 ≤ y := le_trans (le_max_right _ _) hyY
  have hy1 : Y₁ ≤ y := le_trans (le_trans (le_max_left Y₁ 3) (le_max_left _ _)) hyY
  have hΦ := hY₁ y hy1
  have hmy : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hT1 : ((Tm m : ℕ) : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hT2 : y ^ 3 - 1 < (Tm m : ℝ) := by
    have := Nat.lt_floor_add_one (y ^ 3); simp only [Tm]; linarith
  have hy27 : 27 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
  have hT : 3 ≤ Tm m := by
    have : (3 : ℝ) < Tm m := by linarith
    exact_mod_cast this.le
  have hTm : 4 * Tm m + 8 ≤ m := by
    have : 4 * (Tm m : ℝ) + 8 ≤ m := by
      have h9 : (9 : ℝ) ≤ y ^ 2 := by nlinarith
      have : 9 * y ^ 3 ≤ y ^ 5 := by
        calc 9 * y ^ 3 ≤ y ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_right h9 (by positivity)
          _ = y ^ 5 := by ring
      rw [hmy]; linarith
    exact_mod_cast this
  have hsm : g + 2 ≤ √(m : ℝ) := by
    have : y ≤ √(m : ℝ) := by
      rw [Real.le_sqrt (by linarith) (Nat.cast_nonneg _), hmy]; nlinarith [sq_nonneg y]
    linarith
  have hD := del_le_Phi1 hg hy3
  have hD' : del1 g m (Tm m) + del2 g m + 3 / (2 * m) ≤ 1 / 2 :=
    hD.trans (le_of_lt (lt_of_lt_of_le hΦ (min_le_right _ _)))
  have h := lamB_rel hM hg hsm hw hu hsu hT hTm hD'
  refine h.trans ?_
  have : Phi1 g y < ε / 2 := lt_of_lt_of_le hΦ (min_le_left _ _)
  linarith

/-! ### The explicit rate `O(m^{−1/5})` -/

/-- `e^{−y/2} ≤ 2/y` for `y > 0`. -/
theorem exp_neg_half_le {y : ℝ} (hy : 0 < y) : exp (-(y / 2)) ≤ 2 * y⁻¹ := by
  have h := Real.add_one_le_exp (y / 2)
  have he : exp (-(y / 2)) * exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(y / 2))
  rw [le_mul_inv_iff₀ hy]
  nlinarith

/-- `y⁵ e^{−y/2} ≤ 2⁶·6!/y` for `y > 0`. -/
theorem pow_five_exp_le {y : ℝ} (hy : 0 < y) :
    y ^ 5 * exp (-(y / 2)) ≤ 2 ^ 6 * (Nat.factorial 6 : ℝ) * y⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (x := y / 2) (by positivity) 6
  have hf : (0 : ℝ) < Nat.factorial 6 := by exact_mod_cast Nat.factorial_pos 6
  have he : exp (-(y / 2)) * exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(y / 2))
  rw [div_le_iff₀ hf, div_pow] at h
  have h6 : y ^ 6 ≤ 2 ^ 6 * (Nat.factorial 6 : ℝ) * exp (y / 2) := by
    have : y ^ 6 / 2 ^ 6 ≤ exp (y / 2) * Nat.factorial 6 := h
    rw [div_le_iff₀ (by positivity)] at this; linarith
  rw [le_mul_inv_iff₀ hy]
  calc y ^ 5 * exp (-(y / 2)) * y = y ^ 6 * exp (-(y / 2)) := by ring
    _ ≤ 2 ^ 6 * (Nat.factorial 6 : ℝ) * exp (y / 2) * exp (-(y / 2)) :=
        mul_le_mul_of_nonneg_right h6 hE.le
    _ = 2 ^ 6 * (Nat.factorial 6 : ℝ) := by rw [mul_assoc _ (exp _), mul_comm (exp _), he, mul_one]

set_option maxHeartbeats 1000000 in
/-- The majorant of Lemma B(1) is `O(1/y)`: `Φ₁(y) ≤ C(g)/y` for `y ≥ 3`. -/
theorem Phi1_le_rate {g : ℝ} : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 3 ≤ y → Phi1 g y ≤ C * y⁻¹ := by
  have hc0 : 0 < c0g g := by unfold c0g; positivity
  obtain ⟨A5, hA5⟩ : ∃ A : ℝ, A = 3808 * π * √17 / c0g g := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A : ℝ, A = 408 * π * √17 / c0g g := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ A : ℝ, A = √(34 / π) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ A : ℝ, A = 2 * π * √17 / (12 * c0g g) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ A : ℝ, A = 17 * √(2 * π) * exp (g ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ A : ℝ, A = 4 * g ^ 2 + 128 + 2048 := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ A : ℝ, A = 2 ^ 6 * (Nat.factorial 6 : ℝ) := ⟨_, rfl⟩
  have hA5' : 0 ≤ A5 := by rw [hA5]; positivity
  have hA4' : 0 ≤ A4 := by rw [hA4]; positivity
  have hK' : 0 ≤ K := by rw [hK]; positivity
  have hB' : 0 ≤ B := by rw [hB]; positivity
  have hD' : 0 ≤ D := by rw [hD]; positivity
  have hP' : 0 ≤ P := by rw [hP]; positivity
  have hF' : 0 ≤ F := by rw [hF]; positivity
  obtain ⟨Q, hQ⟩ : ∃ A : ℝ, A = (32 + P) * exp P * (1 + 4 * K) := ⟨_, rfl⟩
  have hQ' : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨A5 + A4 + Q + 4 * K + B * F + D + 3 / 2, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = y⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ inv_pos.mpr hy0
  have ht13 : t ≤ 1 / 3 := by rw [ht]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht4 : t ^ 4 ≤ t := by nlinarith
  have ht5 : t ^ 5 ≤ t := by nlinarith
  have ht7 : t ^ 7 ≤ t := by nlinarith
  obtain ⟨e, he⟩ : ∃ A : ℝ, A = exp (-(y / 2)) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he2 : e ≤ 2 * t := by rw [he, ht]; exact exp_neg_half_le hy0
  obtain ⟨E, hE⟩ : ∃ A : ℝ, A = 4 * g ^ 2 * t ^ 2 + 128 * t ^ 7 + 2048 * t := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hEt : E ≤ P * t := by
    rw [hE, hP]; nlinarith [mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 4 * g ^ 2)]
  have hEP : E ≤ P := hEt.trans (mul_le_of_le_one_right hP' ht1)
  have hs : 2 * t ^ 2 + e ≤ 4 * t := by linarith
  have h3 : (32 * t ^ 4 + E) * exp E * (1 + K * (2 * t ^ 2 + e)) ≤ Q * t := by
    have a1 : 32 * t ^ 4 + E ≤ (32 + P) * t := by linarith
    have a2 : exp E ≤ exp P := Real.exp_le_exp.mpr hEP
    have a3 : 1 + K * (2 * t ^ 2 + e) ≤ 1 + 4 * K := by nlinarith [mul_le_mul_of_nonneg_left hs hK']
    calc (32 * t ^ 4 + E) * exp E * (1 + K * (2 * t ^ 2 + e))
        ≤ ((32 + P) * t) * exp P * (1 + 4 * K) := by
          apply mul_le_mul (mul_le_mul a1 a2 (Real.exp_pos _).le (by positivity)) a3
            (by positivity) (by positivity)
      _ = Q * t := by rw [hQ]; ring
  have h5 := pow_five_exp_le hy0
  rw [← hF, ← ht, ← he] at h5
  have hPhi : Phi1 g y = A5 * t ^ 5 + A4 * t ^ 4 + (32 * t ^ 4 + E) * exp E * (1 + K * (2 * t ^ 2 + e)) +
      K * (2 * t ^ 2 + e) + B * (y ^ 5 * e) + D * t ^ 5 + 3 / 2 * t ^ 5 := by
    rw [hA5, hA4, hK, hB, hD, hE, he, ht]; unfold Phi1 PhiE; ring
  rw [hPhi]
  have b1 := mul_le_mul_of_nonneg_left ht5 hA5'
  have b2 := mul_le_mul_of_nonneg_left ht4 hA4'
  have b4 := mul_le_mul_of_nonneg_left hs hK'
  have b5 := mul_le_mul_of_nonneg_left h5 hB'
  have b6 := mul_le_mul_of_nonneg_left ht5 hD'
  have hR : (A5 + A4 + Q + 4 * K + B * F + D + 3 / 2) * y⁻¹ =
      A5 * t + A4 * t + Q * t + K * (4 * t) + B * (F * t) + D * t + 3 / 2 * t := by rw [← ht]; ring
  rw [hR]
  linarith

/-- **Lemma B(1), uniformly in `M`, with the rate** (paper §6.3): there is `C(g)` such that for
`m ≥ m₀(g)`, all `M ≥ 2`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`, `u ≡ s (mod 2)`:
`|λ/λ_m − 1| ≤ C m^{−1/5}`. -/
theorem lemmaB1_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      |lamB M m s u / lamM M m - 1| ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C, hC0, hΦC⟩ := Phi1_le_rate (g := g)
  refine ⟨2 * C, by positivity, ?_⟩
  have hev := (tendsto_Phi1 g).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev
  set Y := max (max Y₁ 3) (g + 2)
  have hY0 : 0 ≤ Y := le_trans (by norm_num) (le_trans (le_max_right Y₁ 3) (le_max_left _ _))
  refine ⟨⌈Y ^ 5⌉₊, fun M m hM hm s u hw hu hsu => ?_⟩
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hm' : Y ^ 5 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hyY : Y ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hY0, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
      Real.rpow_one] at h
  have hy3 : 3 ≤ y := le_trans (le_trans (le_max_right Y₁ 3) (le_max_left _ _)) hyY
  have hyg : g + 2 ≤ y := le_trans (le_max_right _ _) hyY
  have hy1 : Y₁ ≤ y := le_trans (le_trans (le_max_left Y₁ 3) (le_max_left _ _)) hyY
  have hΦ := hY₁ y hy1
  have hmy : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hT1 : ((Tm m : ℕ) : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hT2 : y ^ 3 - 1 < (Tm m : ℝ) := by
    have := Nat.lt_floor_add_one (y ^ 3); simp only [Tm]; linarith
  have hy27 : 27 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
  have hT : 3 ≤ Tm m := by
    have : (3 : ℝ) < Tm m := by linarith
    exact_mod_cast this.le
  have hTm : 4 * Tm m + 8 ≤ m := by
    have : 4 * (Tm m : ℝ) + 8 ≤ m := by
      have h9 : (9 : ℝ) ≤ y ^ 2 := by nlinarith
      have : 9 * y ^ 3 ≤ y ^ 5 := by
        calc 9 * y ^ 3 ≤ y ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_right h9 (by positivity)
          _ = y ^ 5 := by ring
      rw [hmy]; linarith
    exact_mod_cast this
  have hsm : g + 2 ≤ √(m : ℝ) := by
    have : y ≤ √(m : ℝ) := by
      rw [Real.le_sqrt (by linarith) (Nat.cast_nonneg _), hmy]; nlinarith [sq_nonneg y]
    linarith
  have hD := del_le_Phi1 hg hy3
  have hD' : del1 g m (Tm m) + del2 g m + 3 / (2 * m) ≤ 1 / 2 := hD.trans hΦ.le
  have h := lamB_rel hM hg hsm hw hu hsu hT hTm hD'
  have hyr : y⁻¹ = (m : ℝ) ^ (-(1 / 5 : ℝ)) := by rw [hydef, Real.rpow_neg (Nat.cast_nonneg m)]
  have hb := hΦC y hy3
  rw [hyr] at hb
  refine h.trans ?_
  nlinarith

end ArcsAlgo.LLT
