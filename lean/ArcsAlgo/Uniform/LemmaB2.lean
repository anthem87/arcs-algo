module

public import ArcsAlgo.Uniform.B2fix
set_option autoImplicit false

/-!
# Lemma B(2) and B(3), uniformly in `M` (paper §6.3)

`lemmaB2_unif`: for fixed `g ≥ 0` and every `ε > 0` there is `m₀` such that for all `M ≥ 2`,
`m ≥ m₀`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`, `u ≡ s (mod 2)`:
`E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + ε)`.

`lemmaB3_unif`: in the same range, `Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + ε` (Chebyshev).

The proof follows the paper: pairs `(x, y)` split into the four classes `A = x ∖ y`, `B = y ∖ x`,
`C = x ∩ y`, `D = E ∖ (x ∪ y)` with independent sums (`pairP_eq`); Lemma B0′, uniform in `M`,
applies to each class (`quad_err`); for typical pairs the conditional density of `S_y` given
`S_x = a, S_E = s` is compared with that given `S_E = s` alone (`typ_ratio`, `pair_typ`); the
atypical pairs are selected by the three binomial counts `|x|, |y|, |x △ y|` and weigh `≤ M⁻³` each.
The typical range is `T = ⌊m^{3/5}⌋` and the bracket of `B2_fixed` is at most `Φ₂(m^{1/5}) → 1`.

As for Lemma B(1), the statement is the `o(1)` form, uniform in `M`; the proof gives an explicit
rate `O(m^{−1/5})`, the form `O(m^{−1/2+3η})` with `η = 1/10`, stated in `lemmaB2_rate`, `lemmaB3_rate`
(via `Phi2_le_rate`: `Φ₂(y) ≤ 1 + C(g)/y` for `y ≥ 4`). Only Lemma B0′ enters; no hypothesis.
-/

open Finset Real Filter Topology

@[expose] public section

namespace ArcsAlgo.LLT

/-- The majorant `Φ₂(y)` of the bracket of Lemma B(2), with `y = m^{1/5}`; `Φ₂ → 1`. -/
noncomputable def Phi2 (g y : ℝ) : ℝ :=
  (1 + 13 * y⁻¹ ^ 2) * (1 + 64 * y⁻¹ ^ 4) * exp (64 * (2 * y⁻¹ ^ 3 + 4 + g) ^ 2 * y⁻¹) *
      (1 + K1B * exp (g ^ 2 / 2) * y⁻¹ ^ 5) ^ 2 * (1 + 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5) +
    K2B * exp (g ^ 2 / 2) * y⁻¹ ^ 5 + K3B * exp (g ^ 2 / 2) * (y ^ 10 * exp (-(y / 2)))

theorem tendsto_Phi2 (g : ℝ) : Tendsto (Phi2 g) atTop (𝓝 1) := by
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hip : ∀ n : ℕ, 0 < n → Tendsto (fun y : ℝ => y⁻¹ ^ n) atTop (𝓝 0) := fun n hn => by
    simpa [zero_pow hn.ne'] using hi.pow n
  have hy10 : Tendsto (fun y : ℝ => y ^ 10 * exp (-(y / 2))) atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := h.const_mul 1024
    simp only [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp, id]; ring
  have c1 := (tendsto_const_nhds (x := (1 : ℝ))).add ((hip 2 (by norm_num)).const_mul 13)
  have c2 := (tendsto_const_nhds (x := (1 : ℝ))).add ((hip 4 (by norm_num)).const_mul 64)
  have c3 : Tendsto (fun y : ℝ => exp (64 * (2 * y⁻¹ ^ 3 + 4 + g) ^ 2 * y⁻¹)) atTop (𝓝 1) := by
    have h1 := ((((hip 3 (by norm_num)).const_mul 2).add_const (4 + g)).pow 2).const_mul 64
    have h2 := (h1.mul hi)
    have h3 := (Real.continuous_exp.tendsto _).comp h2
    simp only [mul_zero, exp_zero] at h3
    refine h3.congr fun y => ?_
    simp only [Function.comp]; ring_nf
  have c4 := ((tendsto_const_nhds (x := (1 : ℝ))).add
    ((hip 5 (by norm_num)).const_mul (K1B * exp (g ^ 2 / 2)))).pow 2
  have c5 := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((hip 5 (by norm_num)).const_mul (17 * √(2 * π) * exp (g ^ 2 / 2)))
  have c6 := (hip 5 (by norm_num)).const_mul (K2B * exp (g ^ 2 / 2))
  have c7 := hy10.const_mul (K3B * exp (g ^ 2 / 2))
  have := ((((c1.mul c2).mul c3).mul c4).mul c5).add c6 |>.add c7
  simp only [mul_zero, add_zero, one_pow, mul_one] at this
  refine this.congr fun y => ?_
  unfold Phi2; ring

set_option maxHeartbeats 1000000 in
theorem BrB_le_Phi2 {g : ℝ} (hg : 0 ≤ g) {m : ℕ} (hy : 4 ≤ (m : ℝ) ^ ((1 : ℝ) / 5)) :
    BrB g m (Tm m) ≤ Phi2 g ((m : ℝ) ^ ((1 : ℝ) / 5)) := by
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hy0 : 0 < y := by linarith
  have hm : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hm0 : (0 : ℝ) < m := by rw [hm]; positivity
  set T := Tm m
  have hT1 : (T : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hT2 : y ^ 3 - 1 < T := by have := Nat.lt_floor_add_one (y ^ 3); simp only [T, Tm]; linarith
  have hy3 : 64 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hyi : ∀ n : ℕ, y⁻¹ ^ n = 1 / y ^ n := fun n => by rw [inv_pow, one_div]
  have hsm : y ^ 2 ≤ √(m : ℝ) := by
    rw [hm, show y ^ 5 = (y ^ 2) ^ 2 * y by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have : 1 ≤ √y := by rw [Real.le_sqrt (by norm_num) hy0.le]; linarith
    nlinarith [sq_nonneg y]
  have hE := exp_pos (g ^ 2 / 2)
  -- the three factors of `F`
  have f1 : 13 / √(m : ℝ) ≤ 13 * y⁻¹ ^ 2 := by
    rw [hyi, mul_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsm
  have f2 : 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤ 64 * y⁻¹ ^ 4 := by
    rw [hyi, hm, div_le_iff₀ (by positivity)]
    have : (T : ℝ) ^ 2 ≤ (y ^ 3) ^ 2 := pow_le_pow_left₀ hT0 hT1 2
    have e : 64 * (1 / y ^ 4) * (y ^ 5) ^ 2 = 64 * (y ^ 3) ^ 2 := by field_simp
    linarith
  have f3 : 64 * (T : ℝ) * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2 ≤
      64 * (2 * y⁻¹ ^ 3 + 4 + g) ^ 2 * y⁻¹ := by
    rw [hyi, ← one_div, hm, div_le_iff₀ (by positivity)]
    have h1 : (2 + (4 + g) * T) ^ 2 ≤ (2 + (4 + g) * y ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by gcongr) 2
    have h2 : 64 * (T : ℝ) * (2 + (4 + g) * T) ^ 2 ≤ 64 * y ^ 3 * (2 + (4 + g) * y ^ 3) ^ 2 :=
      mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    have e : 64 * (2 * (1 / y ^ 3) + 4 + g) ^ 2 * (1 / y) * (y ^ 5) ^ 2 =
        64 * y ^ 3 * (2 + (4 + g) * y ^ 3) ^ 2 := by field_simp; ring
    linarith
  have hF : FacB g m T ≤ (1 + 13 * y⁻¹ ^ 2) * (1 + 64 * y⁻¹ ^ 4) *
      exp (64 * (2 * y⁻¹ ^ 3 + 4 + g) ^ 2 * y⁻¹) := by
    unfold FacB
    have : 0 ≤ 13 / √(m : ℝ) := by positivity
    have : 0 ≤ 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2 := by positivity
    gcongr
  -- the error terms
  have e1 : K1B * exp (g ^ 2 / 2) / m = K1B * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
    rw [hyi, hm]; field_simp
  have e2 : del2 g m = 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
    unfold del2; rw [hyi, hm]; field_simp
  have e3 : K2B * exp (g ^ 2 / 2) / m = K2B * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
    rw [hyi, hm]; field_simp
  have e4 : (m : ℝ) * √(m : ℝ) * exp (-(2 * (T : ℝ) ^ 2 / m)) ≤ y ^ 10 * exp (-(y / 2)) := by
    have h1 : (m : ℝ) * √(m : ℝ) ≤ y ^ 10 := by
      have : √(m : ℝ) ≤ m := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (1 : ℝ) ≤ m := by rw [hm]; nlinarith [pow_le_pow_left₀ (by norm_num) hy 5]
        nlinarith
      calc (m : ℝ) * √(m : ℝ) ≤ m * m := mul_le_mul_of_nonneg_left this hm0.le
        _ = y ^ 10 := by rw [hm]; ring
    have h2 : exp (-(2 * (T : ℝ) ^ 2 / m)) ≤ exp (-(y / 2)) := by
      apply exp_le_exp.mpr
      rw [neg_le_neg_iff, hm, le_div_iff₀ (by positivity)]
      have hTb : y ^ 3 / 2 ≤ (T : ℝ) := by linarith
      have := pow_le_pow_left₀ (by positivity) hTb 2
      nlinarith
    exact mul_le_mul h1 h2 (exp_pos _).le (by positivity)
  unfold BrB
  rw [e1, e2, e3]
  have hK3 : 0 ≤ K3B * exp (g ^ 2 / 2) := by unfold K3B; positivity
  have hK1 : 0 ≤ K1B * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by unfold K1B; positivity
  have hd : 0 ≤ 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by positivity
  have hF0 : 0 ≤ FacB g m T := by unfold FacB; positivity
  unfold Phi2
  have := mul_le_mul_of_nonneg_left e4 hK3
  gcongr

theorem lamM_pos {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) : 0 < lamM M m := by
  have hσ := sig2_pos hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
  have h2 : 0 < √(2 * π * m) := Real.sqrt_pos.mpr (by positivity)
  exact lt_of_lt_of_le (by positivity) (lamM_ge hM hm)

/-- **Lemma B(2), uniformly in `M`** (paper §6.3): for fixed `g ≥ 0` and every `ε > 0` there is
`m₀` such that for all `M ≥ 2`, `m ≥ m₀`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`, `u ≡ s (mod 2)`:
`E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + ε)`. Only Lemma B0′ enters (proved, through the
four class sums and the three binomial counts `|x|, |y|, |x △ y|`); no hypothesis. -/
theorem lemmaB2_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      m2B M m s u ≤ lamB M m s u * (1 + if u = 0 then 1 else 0) + lamB M m s u ^ 2 * (1 + ε) := by
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg (ε := 1 / 2) (by norm_num)
  have hev1 := (tendsto_Phi2 g).eventually (gt_mem_nhds (show (1 : ℝ) < 1 + ε by linarith))
  have hd0 : Tendsto (fun y : ℝ => 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5) atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 5).const_mul (17 * √(2 * π) * exp (g ^ 2 / 2))
    simpa using this
  have hev2 := hd0.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp (hev1.and hev2)
  set Y := max Y₁ 4
  have hY0 : 0 ≤ Y := le_trans (by norm_num) (le_max_right Y₁ 4)
  refine ⟨max m₁ ⌈Y ^ 5⌉₊, fun M m hM hm s u hw hu hsu => ?_⟩
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hm' : Y ^ 5 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hm)
  have hyY : Y ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hY0, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
      Real.rpow_one] at h
  have hy4 : 4 ≤ y := le_trans (le_max_right _ _) hyY
  have hy1 : Y₁ ≤ y := le_trans (le_max_left _ _) hyY
  obtain ⟨hΦ, hdy⟩ := hY₁ y hy1
  have hmy : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hT1 : ((Tm m : ℕ) : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hm32 : 32 ≤ m := by
    have : (32 : ℝ) ≤ m := by rw [hmy]; nlinarith [pow_le_pow_left₀ (by norm_num) hy4 5]
    exact_mod_cast this
  have hTm : 16 * Tm m ≤ m := by
    have : 16 * (Tm m : ℝ) ≤ m := by
      have h16 : (16 : ℝ) ≤ y ^ 2 := by nlinarith
      have : 16 * y ^ 3 ≤ y ^ 5 := by
        calc 16 * y ^ 3 ≤ y ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_right h16 (by positivity)
          _ = y ^ 5 := by ring
      rw [hmy]; linarith
    exact_mod_cast this
  -- `λ ≥ λ_m/2`
  have hl := h₁ M m hM (le_trans (le_max_left _ _) hm) s u hw hu hsu
  have hlm0 : 0 < lamM M m := lamM_pos hM (by omega)
  have hlam : lamM M m / 2 ≤ lamB M m s u := by
    have := (abs_le.mp hl).1
    rw [div_sub_one hlm0.ne', le_div_iff₀ hlm0] at this; linarith
  have hd : del2 g m ≤ 1 / 2 := by
    have : del2 g m = 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
      unfold del2; rw [inv_pow, hmy]; field_simp
    rw [this]; exact hdy
  have hB := B2_fixed hM hm32 hTm hg hw hu hsu hlam hd
  have hBr := BrB_le_Phi2 hg hy4
  refine hB.trans ?_
  have : lamB M m s u ^ 2 * BrB g m (Tm m) ≤ lamB M m s u ^ 2 * (1 + ε) :=
    mul_le_mul_of_nonneg_left (hBr.trans hΦ.le) (sq_nonneg _)
  linarith

/-- **Lemma B(3), uniformly in `M`** (paper §6.3): `Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + ε` for
`m ≥ m₀`, by Chebyshev (`p0B_le`) and Lemma B(2). -/
theorem lemmaB3_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      p0B M m s u ≤ 2 / lamB M m s u + ε := by
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg (ε := 1 / 2) (by norm_num)
  obtain ⟨m₂, h₂⟩ := lemmaB2_unif hg hε
  refine ⟨max (max m₁ m₂) 1, fun M m hM hm s u hw hu hsu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hl := h₁ M m hM hm1 s u hw hu hsu
  have hlm0 : 0 < lamM M m := lamM_pos hM hm0
  have hlam : 0 < lamB M m s u := by
    have := (abs_le.mp hl).1
    rw [div_sub_one hlm0.ne', le_div_iff₀ hlm0] at this; linarith
  have h0 := p0B_le hlam
  have h2 := h₂ M m hM hm2 s u hw hu hsu
  have hi : (if u = 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hi0 : 0 ≤ (if u = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hl2 : 0 < lamB M m s u ^ 2 := by positivity
  have : m2B M m s u / lamB M m s u ^ 2 - 1 ≤ 2 / lamB M m s u + ε := by
    rw [div_sub_one hl2.ne', div_le_iff₀ hl2]
    have e : (2 / lamB M m s u + ε) * lamB M m s u ^ 2 = 2 * lamB M m s u + ε * lamB M m s u ^ 2 := by
      field_simp
    rw [e]
    nlinarith
  linarith

/-! ### The explicit rate `O(m^{−1/5})` -/

theorem one_add_mul_mul_le {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + a * t) * (1 + b * t) ≤ 1 + (a + b + a * b) * t := by
  have hab := mul_nonneg ha hb
  have : a * b * t ^ 2 ≤ a * b * t := mul_le_mul_of_nonneg_left (by nlinarith) hab
  nlinarith

/-- `e^x − 1 ≤ x e^x`. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) : exp x - 1 ≤ x * exp x := by
  have h := Real.add_one_le_exp (-x)
  have he := Real.exp_pos x
  have : exp (-x) * exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- `y^{10} e^{−y/2} ≤ 2^{11}·11!/y` for `y > 0`. -/
theorem pow_ten_exp_le {y : ℝ} (hy : 0 < y) :
    y ^ 10 * exp (-(y / 2)) ≤ 2 ^ 11 * (Nat.factorial 11 : ℝ) * y⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (x := y / 2) (by positivity) 11
  have hf : (0 : ℝ) < Nat.factorial 11 := by exact_mod_cast Nat.factorial_pos 11
  have he : exp (-(y / 2)) * exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(y / 2))
  rw [div_le_iff₀ hf, div_pow] at h
  -- `y^11 ≤ 2^11 · 11! · e^{y/2}`
  have h11 : y ^ 11 ≤ 2 ^ 11 * (Nat.factorial 11 : ℝ) * exp (y / 2) := by
    have : y ^ 11 / 2 ^ 11 ≤ exp (y / 2) * Nat.factorial 11 := h
    rw [div_le_iff₀ (by positivity)] at this; linarith
  rw [le_mul_inv_iff₀ hy]
  calc y ^ 10 * exp (-(y / 2)) * y = y ^ 11 * exp (-(y / 2)) := by ring
    _ ≤ 2 ^ 11 * (Nat.factorial 11 : ℝ) * exp (y / 2) * exp (-(y / 2)) :=
        mul_le_mul_of_nonneg_right h11 hE.le
    _ = 2 ^ 11 * (Nat.factorial 11 : ℝ) := by rw [mul_assoc _ (exp _), mul_comm (exp _), he, mul_one]

set_option maxHeartbeats 1000000 in
/-- The bracket majorant of Lemma B(2) is `1 + O(1/y)`: `Φ₂(y) ≤ 1 + C(g)/y` for `y ≥ 4`. -/
theorem Phi2_le_rate {g : ℝ} (hg : 0 ≤ g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 4 ≤ y → Phi2 g y ≤ 1 + C * y⁻¹ := by
  obtain ⟨e, hed⟩ : ∃ e, e = exp (g ^ 2 / 2) := ⟨_, rfl⟩
  have he : 0 ≤ e := hed ▸ (Real.exp_pos _).le
  have hK1 : 0 ≤ K1B := by unfold K1B; positivity
  have hK2 : 0 ≤ K2B := by unfold K2B; positivity
  have hK3 : 0 ≤ K3B := by unfold K3B; positivity
  obtain ⟨c0, hc0d⟩ : ∃ c0 : ℝ, c0 = 64 * (5 + g) ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := by rw [hc0d]; positivity
  obtain ⟨a3, ha3d⟩ : ∃ a3 : ℝ, a3 = c0 * exp c0 := ⟨_, rfl⟩
  obtain ⟨a4, ha4d⟩ : ∃ a4 : ℝ, a4 = K1B * e := ⟨_, rfl⟩
  obtain ⟨a5, ha5d⟩ : ∃ a5 : ℝ, a5 = 17 * √(2 * π) * e := ⟨_, rfl⟩
  have ha3 : 0 ≤ a3 := by rw [ha3d]; exact mul_nonneg hc0 (Real.exp_pos _).le
  have ha4 : 0 ≤ a4 := by rw [ha4d]; exact mul_nonneg hK1 he
  have ha5 : 0 ≤ a5 := by rw [ha5d]; positivity
  obtain ⟨b12, hb12d⟩ : ∃ b : ℝ, b = 13 + 64 + 13 * 64 := ⟨_, rfl⟩
  obtain ⟨b123, hb123d⟩ : ∃ b : ℝ, b = b12 + a3 + b12 * a3 := ⟨_, rfl⟩
  obtain ⟨b1234, hb1234d⟩ : ∃ b : ℝ, b = b123 + a4 + b123 * a4 := ⟨_, rfl⟩
  obtain ⟨b12344, hb12344d⟩ : ∃ b : ℝ, b = b1234 + a4 + b1234 * a4 := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b' : ℝ, b' = b12344 + a5 + b12344 * a5 := ⟨_, rfl⟩
  have hb12 : 0 ≤ b12 := by rw [hb12d]; norm_num
  have hb123 : 0 ≤ b123 := by rw [hb123d]; positivity
  have hb1234 : 0 ≤ b1234 := by rw [hb1234d]; positivity
  have hb12344 : 0 ≤ b12344 := by rw [hb12344d]; positivity
  have hb : 0 ≤ b := by rw [hbd]; positivity
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = 2 ^ 11 * (Nat.factorial 11 : ℝ) := ⟨_, rfl⟩
  have hD : 0 ≤ D := by rw [hDd]; positivity
  refine ⟨b + K2B * e + K3B * e * D, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = y⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ inv_pos.mpr hy0
  have ht14 : t ≤ 1 / 4 := by rw [ht]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith
  have ht4 : t ^ 4 ≤ t := by nlinarith
  have ht5 : t ^ 5 ≤ t := by nlinarith
  have ht3' : 2 * t ^ 3 ≤ 1 := by nlinarith
  have f1 : 1 + 13 * t ^ 2 ≤ 1 + 13 * t := by linarith
  have f2 : 1 + 64 * t ^ 4 ≤ 1 + 64 * t := by linarith
  have f3 : exp (64 * (2 * t ^ 3 + 4 + g) ^ 2 * t) ≤ 1 + a3 * t := by
    obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = 64 * (2 * t ^ 3 + 4 + g) ^ 2 * t := ⟨_, rfl⟩
    rw [← hxd]
    have hsq : (2 * t ^ 3 + 4 + g) ^ 2 ≤ (5 + g) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hx0 : 0 ≤ x := by rw [hxd]; positivity
    have hx : x ≤ c0 * t := by
      rw [hxd, hc0d]; exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
    have hxc : x ≤ c0 := hx.trans (mul_le_of_le_one_right hc0 ht1)
    have h1 := exp_sub_one_le_mul_exp x
    have h2 : x * exp x ≤ c0 * t * exp c0 :=
      mul_le_mul hx (Real.exp_le_exp.mpr hxc) (Real.exp_pos _).le (by positivity)
    have : c0 * t * exp c0 = a3 * t := by rw [ha3d]; ring
    linarith
  have f4 : 1 + K1B * e * t ^ 5 ≤ 1 + a4 * t := by
    rw [ha4d]; linarith [mul_le_mul_of_nonneg_left ht5 (mul_nonneg hK1 he)]
  have f5 : 1 + 17 * √(2 * π) * e * t ^ 5 ≤ 1 + a5 * t := by
    have : 0 ≤ 17 * √(2 * π) * e := by positivity
    rw [ha5d]; linarith [mul_le_mul_of_nonneg_left ht5 this]
  have p12 : (1 + 13 * t ^ 2) * (1 + 64 * t ^ 4) ≤ 1 + b12 * t := by
    have := (mul_le_mul f1 f2 (by positivity) (by positivity)).trans
      (one_add_mul_mul_le (by norm_num : (0 : ℝ) ≤ 13) (by norm_num : (0 : ℝ) ≤ 64) ht0.le ht1)
    rw [hb12d]; exact this
  have p123 := (mul_le_mul p12 f3 (Real.exp_pos _).le (by positivity)).trans
    (one_add_mul_mul_le hb12 ha3 ht0.le ht1)
  rw [← hb123d] at p123
  have p1234 := (mul_le_mul p123 f4 (by positivity) (by positivity)).trans
    (one_add_mul_mul_le hb123 ha4 ht0.le ht1)
  rw [← hb1234d] at p1234
  have p12344 := (mul_le_mul p1234 f4 (by positivity) (by positivity)).trans
    (one_add_mul_mul_le hb1234 ha4 ht0.le ht1)
  rw [← hb12344d] at p12344
  have p := (mul_le_mul p12344 f5 (by positivity) (by positivity)).trans
    (one_add_mul_mul_le hb12344 ha5 ht0.le ht1)
  rw [← hbd] at p
  have hlast := pow_ten_exp_le hy0
  rw [← hDd, ← ht] at hlast
  have hK2t : K2B * e * t ^ 5 ≤ K2B * e * t := mul_le_mul_of_nonneg_left ht5 (mul_nonneg hK2 he)
  have hK3t : K3B * e * (y ^ 10 * exp (-(y / 2))) ≤ K3B * e * (D * t) :=
    mul_le_mul_of_nonneg_left hlast (mul_nonneg hK3 he)
  have hPhi : Phi2 g y = (1 + 13 * t ^ 2) * (1 + 64 * t ^ 4) * exp (64 * (2 * t ^ 3 + 4 + g) ^ 2 * t) *
      (1 + K1B * e * t ^ 5) * (1 + K1B * e * t ^ 5) * (1 + 17 * √(2 * π) * e * t ^ 5) +
      K2B * e * t ^ 5 + K3B * e * (y ^ 10 * exp (-(y / 2))) := by
    unfold Phi2; rw [← hed, ← ht]; ring
  have hR : 1 + (b + K2B * e + K3B * e * D) * y⁻¹ = 1 + b * t + K2B * e * t + K3B * e * (D * t) := by
    rw [← ht]; ring
  rw [hPhi, hR]
  linarith

/-- **Lemma B(2), uniformly in `M`, with the rate** (paper §6.3): there is `C(g)` such that for
`m ≥ m₀(g)`, all `M ≥ 2`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`, `u ≡ s (mod 2)`:
`E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + C m^{−1/5})`. -/
theorem lemmaB2_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      m2B M m s u ≤ lamB M m s u + lamB M m s u * (if u = 0 then 1 else 0) +
        lamB M m s u ^ 2 * (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ))) := by
  obtain ⟨C, hC0, hΦC⟩ := Phi2_le_rate hg
  refine ⟨C, hC0, ?_⟩
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg (ε := 1 / 2) (by norm_num)
  have hd0 : Tendsto (fun y : ℝ => 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5) atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 5).const_mul (17 * √(2 * π) * exp (g ^ 2 / 2))
    simpa using this
  have hev2 := hd0.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev2
  set Y := max Y₁ 4
  have hY0 : 0 ≤ Y := le_trans (by norm_num) (le_max_right Y₁ 4)
  refine ⟨max m₁ ⌈Y ^ 5⌉₊, fun M m hM hm s u hw hu hsu => ?_⟩
  set y := (m : ℝ) ^ ((1 : ℝ) / 5) with hydef
  have hm' : Y ^ 5 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hm)
  have hyY : Y ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hY0, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
      Real.rpow_one] at h
  have hy4 : 4 ≤ y := le_trans (le_max_right _ _) hyY
  have hy1 : Y₁ ≤ y := le_trans (le_max_left _ _) hyY
  have hdy := hY₁ y hy1
  have hmy : (m : ℝ) = y ^ 5 := (y_pow_five m).symm
  have hT1 : ((Tm m : ℕ) : ℝ) ≤ y ^ 3 := Nat.floor_le (by positivity)
  have hm32 : 32 ≤ m := by
    have : (32 : ℝ) ≤ m := by rw [hmy]; nlinarith [pow_le_pow_left₀ (by norm_num) hy4 5]
    exact_mod_cast this
  have hTm : 16 * Tm m ≤ m := by
    have : 16 * (Tm m : ℝ) ≤ m := by
      have h16 : (16 : ℝ) ≤ y ^ 2 := by nlinarith
      have : 16 * y ^ 3 ≤ y ^ 5 := by
        calc 16 * y ^ 3 ≤ y ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_right h16 (by positivity)
          _ = y ^ 5 := by ring
      rw [hmy]; linarith
    exact_mod_cast this
  have hl := h₁ M m hM (le_trans (le_max_left _ _) hm) s u hw hu hsu
  have hlm0 : 0 < lamM M m := lamM_pos hM (by omega)
  have hlam : lamM M m / 2 ≤ lamB M m s u := by
    have := (abs_le.mp hl).1
    rw [div_sub_one hlm0.ne', le_div_iff₀ hlm0] at this; linarith
  have hd : del2 g m ≤ 1 / 2 := by
    have : del2 g m = 17 * √(2 * π) * exp (g ^ 2 / 2) * y⁻¹ ^ 5 := by
      unfold del2; rw [inv_pow, hmy]; field_simp
    rw [this]; exact hdy
  have hB := B2_fixed hM hm32 hTm hg hw hu hsu hlam hd
  have hBr := (BrB_le_Phi2 hg hy4).trans (hΦC y hy4)
  have hyr : y⁻¹ = (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [hydef, Real.rpow_neg (Nat.cast_nonneg m)]
  rw [hyr] at hBr
  refine hB.trans ?_
  have : lamB M m s u ^ 2 * BrB g m (Tm m) ≤ lamB M m s u ^ 2 * (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ))) :=
    mul_le_mul_of_nonneg_left hBr (sq_nonneg _)
  nlinarith

/-- **Lemma B(3), uniformly in `M`, with the rate** (paper §6.3): there is `C(g)` such that for
`m ≥ m₀(g)`, in the same range, `Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + C m^{−1/5}` (Chebyshev and
`lemmaB2_rate`). -/
theorem lemmaB3_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      p0B M m s u ≤ 2 / lamB M m s u + C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C, hC0, m₂, h₂⟩ := lemmaB2_rate hg
  refine ⟨C, hC0, ?_⟩
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg (ε := 1 / 2) (by norm_num)
  refine ⟨max (max m₁ m₂) 1, fun M m hM hm s u hw hu hsu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hl := h₁ M m hM hm1 s u hw hu hsu
  have hlm0 : 0 < lamM M m := lamM_pos hM hm0
  have hlam : 0 < lamB M m s u := by
    have := (abs_le.mp hl).1
    rw [div_sub_one hlm0.ne', le_div_iff₀ hlm0] at this; linarith
  have h0 := p0B_le hlam
  have h2 := h₂ M m hM hm2 s u hw hu hsu
  set r := C * (m : ℝ) ^ (-(1 / 5 : ℝ))
  have hi : (if u = 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hl2 : 0 < lamB M m s u ^ 2 := by positivity
  have : m2B M m s u / lamB M m s u ^ 2 - 1 ≤ 2 / lamB M m s u + r := by
    rw [div_sub_one hl2.ne', div_le_iff₀ hl2]
    have e : (2 / lamB M m s u + r) * lamB M m s u ^ 2 = 2 * lamB M m s u + r * lamB M m s u ^ 2 := by
      field_simp
    rw [e]
    nlinarith
  linarith

end ArcsAlgo.LLT
