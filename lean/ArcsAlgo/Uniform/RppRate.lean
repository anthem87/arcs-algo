module

public import ArcsAlgo.Uniform.RppAsymp
set_option autoImplicit false

/-!
# Theorem R″ with the rate (paper §6.7)

The paper's `p` carries `O(m^{−1/5})` in `6 ln(mM)(1 + 2/λ_m + O(m^{−1/5}))` and a factor
`1 + o(1)`; `succB_unif` and `thmRpp_gen` have the factor `1/(1 + ε)` with `m₀(g, ε)`. Here the
rate is explicit, from Lemmas B(1), B(2) with the rate and Lemma V with the rate.

* `lemmaV_core`: the proof of Lemma V (`lemmaV`) with the two relative errors as hypotheses:
  from `λ ≥ (1 − e)λ_m`, `del2 g m ≤ e ≤ 1/4` and `1 ≤ F(1 − e)²`,
  `D_eq/λ ≤ 0.72 e^{g²/2} m(3ψ + ψ²)·F`.
* `lemmaV_rate`: `D_eq/λ ≤ 0.72 e^{g²/2} m(3ψ + ψ²)(1 + C m^{−1/5})` for `m ≥ m₀(g)`.
* `pRate`: `p_rate = [(2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C m^{−1/5})]⁻¹
  (1 − C m^{−1/5})`.
* `succB_rate`: a round succeeds with probability `≥ p_rate`, for `m ≥ m₀(g)`, uniformly in
  `M ≥ 2`, `P₀ ≥ 100` and the window.
* `thmRpp_rate`: Theorem R″ in general form with `p_rate`:
  `Pr(every round fails) ≤ (1 − (1 − 2e^{−g²/6}) p_rate)^R`.

The only hypothesis is that of Lemma K (`RosserSchoenfeld`, cited). `thmRpp` is unchanged.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

section core

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
/-- The proof of Lemma V with the relative errors as hypotheses: if `λ ≥ (1 − e)λ_m`,
`del2 g m ≤ e ≤ 1/4` and `1 ≤ F(1 − e)²`, then `D_eq/λ ≤ 0.72 e^{g²/2} m (3ψ + ψ²)·F`. -/
theorem lemmaV_core {g : ℝ} {M : ℕ} (hM : 2 ≤ M) (hm0 : 2 ≤ m) (A : Finset (Fin m))
    (hA : A.card = m / 2) {s u a : ℤ} (ha : 2 * a = s + u)
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) {e F : ℝ} (he1 : e ≤ 1 / 4)
    (hlam : (1 - e) * lamM M m ≤ lamB M m s u) (hdel : del2 g m ≤ e) (h1e : 1 ≤ F * (1 - e) ^ 2) :
    DeqA M m A a s / lamB M m s u ≤
      0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) * F := by
  have hF0 : 0 < F := by
    by_contra h; push Not at h
    have : F * (1 - e) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)
    linarith
  have hM0 : 0 < M := by omega
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hσ := sig2_pos hM
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsu : (2 : ℤ) ∣ u - s := ⟨a - s, by linarith⟩
  -- the halves are non-empty
  have hAne : A.Nonempty := card_pos.mp (by omega)
  have hBne : Aᶜ.Nonempty := card_pos.mp (by rw [card_compl, Fintype.card_fin]; omega)
  have hlm := lamM_pos hM (by omega : 1 ≤ m)
  have hgm0 := gm_ge hM (by omega : 1 ≤ m) hw
  have hgm : 0 < gaussB M m s := lt_of_lt_of_le (by positivity) hgm0
  have hrel := law_rel hM hm0 hw
  have hp : (1 - e) * gaussB M m s ≤ lawS M m s := by
    have := (abs_le.mp hrel).1
    rw [div_sub_one hgm.ne', le_div_iff₀ hgm] at this
    have := mul_le_mul_of_nonneg_right hdel hgm.le
    linarith
  have hp0 : 0 < lawS M m s := lt_of_lt_of_le (by have : 0 < 1 - e := by linarith
                                                  positivity) hp
  have hlam0 : 0 < lamB M m s u := lt_of_lt_of_le (by have : 0 < 1 - e := by linarith
                                                      positivity) hlam
  -- the sum over the pairs
  have hT := sum_pairPA hM0 hAne hBne a s
  rw [hA] at hT
  set ψ := √((2 : ℝ) ^ m) / M
  have hψ2 : ψ ^ 2 = 2 ^ m / (M : ℝ) ^ 2 := by
    simp only [ψ]; rw [div_pow, Real.sq_sqrt (by positivity)]
  have hT' : 2 ^ m * (2 ^ (m - m / 2) + 2 ^ (m / 2) + 1) / (M : ℝ) ^ 3 + 4 ^ m / (M : ℝ) ^ 4 ≤
      2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) := by
    have h3 := three_halves m
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4, hψ2]
    simp only [ψ]
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have : 2 ^ m * (2 ^ (m - m / 2) + 2 ^ (m / 2) + 1) / (M : ℝ) ^ 3 ≤
        2 ^ m * (3 * √((2 : ℝ) ^ m)) / (M : ℝ) ^ 3 := by gcongr
    have e : 2 ^ m / (M : ℝ) ^ 2 * (3 * (√((2 : ℝ) ^ m) / M) + 2 ^ m / (M : ℝ) ^ 2) =
        2 ^ m * (3 * √((2 : ℝ) ^ m)) / (M : ℝ) ^ 3 + 2 ^ m * 2 ^ m / (M : ℝ) ^ 4 := by
      field_simp
    rw [e]; linarith
  -- `p λ ≥ (1 − e)² g_m(s) λ_m`
  have hpl : (1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m ≤
      lawS M m s * lamB M m s u := by
    have h1 : 0 < 1 - e := by linarith
    calc (1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m
        = ((1 - e) * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ))))) *
          ((1 - e) * lamM M m) := by ring
      _ ≤ ((1 - e) * gaussB M m s) * ((1 - e) * lamM M m) := by
          gcongr; rw [Real.exp_neg]; exact hgm0
      _ ≤ lawS M m s * lamB M m s u := mul_le_mul hp hlam (by positivity) hp0.le
  -- the constants
  have hσM : √(sig2 M) ≤ M / √12 := by
    rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
    unfold sig2; linarith
  have hcM : cMB M ≤ 5 / 8 := by
    unfold cMB
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : 1 / (6 * (M : ℝ) ^ 2) ≤ 1 / 24 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hlamM : 2 ^ m / (M * √(2 * π * m * (5 / 8))) * 2 ≤ lamM M m := by
    unfold lamM
    have hc0 : 0 < cMB M := by unfold cMB; positivity
    have hs1 : √(2 * π * m * cMB M) ≤ √(2 * π * m * (5 / 8)) := Real.sqrt_le_sqrt (by
      have : 0 < 2 * π * m := by positivity
      nlinarith)
    rw [pow_succ]
    have : 0 < √(2 * π * m * cMB M) := Real.sqrt_pos.mpr (by positivity)
    calc 2 ^ m / (↑M * √(2 * π * ↑m * (5 / 8))) * 2 = 2 ^ m * 2 / (↑M * √(2 * π * ↑m * (5 / 8))) := by ring
      _ ≤ 2 ^ m * 2 / (↑M * √(2 * π * ↑m * cMB M)) := by gcongr
  -- assembling
  unfold DeqA
  rw [div_div, div_le_iff₀ (mul_pos hp0 hlam0)]
  refine hT.trans (hT'.trans ?_)
  have hK : (1 : ℝ) ≤ 0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8))) := by
    rw [le_div_iff₀ (by positivity), ← Real.sqrt_mul (by positivity)]
    have h12 : (3.46 : ℝ) ≤ √12 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [one_mul, Real.sqrt_le_left (by positivity)]
    have hpi : π * π < 3.15 * 3.15 := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2
    have h12' : (3.46 : ℝ) * 3.46 ≤ √12 * √12 := mul_self_le_mul_self (by norm_num) h12
    have : 2 * π * (2 * π * (5 / 8)) ≤ (0.72 * (2 * 3.46)) ^ 2 := by nlinarith
    nlinarith
  have hsm : √(2 * π * m * (5 / 8)) = √(2 * π * (5 / 8)) * √(m : ℝ) := by
    rw [show 2 * π * m * (5 / 8) = 2 * π * (5 / 8) * m by ring, Real.sqrt_mul (by positivity)]
  have hmm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hmR.le
  have hψ0 : 0 ≤ 3 * ψ + ψ ^ 2 := by simp only [ψ]; positivity
  have hE : exp (g ^ 2 / 2) * exp (-(g ^ 2 / 2)) = 1 := by rw [← exp_add]; simp
  -- `2^m/M² (3ψ+ψ²) ≤ R · (1−e)² g λ_m`, then `≤ R · p λ`
  have hlow : 2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) ≤
      0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) * F *
        ((1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m) := by
    have hlam2 : (1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (M / √12 * √(m : ℝ)))) *
        (2 ^ m / (M * √(2 * π * m * (5 / 8))) * 2) ≤
        (1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m := by
      have : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
      gcongr
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hlam2 (by positivity))
    rw [hsm]
    have heq : 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) * F *
        ((1 - e) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (M / √12 * √(m : ℝ)))) *
          (2 ^ m / (M * (√(2 * π * (5 / 8)) * √(m : ℝ))) * 2)) =
        2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) *
          (F * (1 - e) ^ 2 * (0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8))))) *
          (exp (g ^ 2 / 2) * exp (-(g ^ 2 / 2))) * (m / (√(m : ℝ) * √(m : ℝ))) := by
      field_simp
    rw [heq, hE, hmm, div_self hmR.ne', mul_one, mul_one]
    have hA0 : 0 ≤ 2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) := by positivity
    have : 1 ≤ F * (1 - e) ^ 2 * (0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8)))) := by
      nlinarith
    nlinarith
  refine hlow.trans ?_
  apply mul_le_mul_of_nonneg_left hpl
  positivity

end core

open ArcsAlgo ArcsAlgo.PrimeK

/-- `K m^{−1/5} ≤ 1/2` as soon as `m ≥ (2K + 1)⁵`. -/
theorem rate_le_half {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : (2 * K + 1) ^ 5 ≤ (m : ℝ)) :
    K * (m : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 / 2 := by
  set r := (m : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK0 : (0 : ℝ) < 2 * K + 1 := by positivity
  have hy : 2 * K + 1 ≤ (m : ℝ) ^ ((1 : ℝ) / 5) := by
    have h := Real.rpow_le_rpow (by positivity) hm (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
      Real.rpow_one] at h
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hrK : r * (2 * K + 1) ≤ 1 := by
    rw [hr, Real.rpow_neg hm0.le, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hy
  nlinarith

/-- `1/m ≤ m^{−1/5}` for `m ≥ 1`. -/
theorem inv_le_rate {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) / m ≤ (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-- **Lemma V with the rate** (paper §6.7): there is `C(g)` such that for `m ≥ m₀(g)`, uniformly
in `M ≥ 2` and in the window, `D_eq/λ ≤ 0.72 e^{g²/2} m (3ψ + ψ²)(1 + C m^{−1/5})`,
`ψ = 2^{m/2}/M`. From Lemma B(1) with the rate and `del2 g m = O(1/m)` in `lemmaV_core`. -/
theorem lemmaV_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      DeqA M m A a s / lamB M m s u ≤
        0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) *
          (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ))) := by
  obtain ⟨C₁, hC₁, m₁, h₁⟩ := lemmaB1_rate hg
  set c := 17 * √(2 * π) * exp (g ^ 2 / 2) with hcdef
  have hc : 0 ≤ c := by positivity
  refine ⟨6 * (C₁ + c), by positivity, max (max m₁ 2) ⌈(2 * (2 * (C₁ + c)) + 1) ^ 5⌉₊,
    fun M m hM hm A hA s u a ha hw hu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm0 : 2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmK : (2 * (2 * (C₁ + c)) + 1) ^ 5 ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hm)
  set r := (m : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrK := rate_le_half (by positivity : 0 ≤ 2 * (C₁ + c)) hmK
  set e := (C₁ + c) * r with hedef
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 / 4 := by simp only [hedef]; nlinarith
  have hsu : (2 : ℤ) ∣ u - s := ⟨a - s, by linarith⟩
  have hlm := lamM_pos hM (by omega : 1 ≤ m)
  have hlam : (1 - e) * lamM M m ≤ lamB M m s u := by
    have h := (abs_le.mp (h₁ M m hM hm1 s u hw hu hsu)).1
    rw [div_sub_one hlm.ne', le_div_iff₀ hlm] at h
    have hce : C₁ * r ≤ e := by simp only [hedef]; nlinarith [mul_nonneg hc hr0]
    nlinarith
  have hdel : del2 g m ≤ e := by
    have hinv := inv_le_rate (by omega : 1 ≤ m)
    unfold del2
    calc 17 * √(2 * π) * exp (g ^ 2 / 2) / (m : ℝ) = c * (1 / (m : ℝ)) := by rw [hcdef]; ring
      _ ≤ c * r := mul_le_mul_of_nonneg_left hinv hc
      _ ≤ e := by simp only [hedef]; nlinarith [mul_nonneg hC₁ hr0]
  have h1e : 1 ≤ (1 + 6 * (C₁ + c) * r) * (1 - e) ^ 2 := by
    have h6 : 6 * (C₁ + c) * r = 6 * e := by simp only [hedef]; ring
    rw [h6]
    nlinarith [mul_nonneg he0 (by linarith : (0 : ℝ) ≤ 4 - 11 * e), mul_nonneg (mul_nonneg he0 he0) he0]
  exact lemmaV_core hM hm0 A hA ha hw he1 hlam hdel h1e

/-- `p_rate` of Theorem R″ (paper §6.7), `r = m^{−1/5}`, `ψ = 2^{m/2}/M`:
`p_rate = [(2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C r)]⁻¹ (1 − C r)`. -/
noncomputable def pRate (g C : ℝ) (M m P₀ : ℕ) : ℝ :=
  (2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) +
    6 * log (m * M) * (1 + 2 / lamM M m + C * (m : ℝ) ^ (-(1 / 5 : ℝ))))⁻¹ *
    (1 - C * (m : ℝ) ^ (-(1 / 5 : ℝ)))

/-- The algebra of `p_rate`: from `λ ≥ (1 − x₁)λ_m`, `D_eq ≤ λV(1 + a)`, `E Z² ≤ 2λ + λ²(1 + b)`
and `x₁ + a + b ≤ x ≤ 1/2`,
`[P(1 + V)/λ_m + ℓ(1 + 2/λ_m + x)]⁻¹(1 − x) ≤ λ²/(P(λ + D_eq) + ℓ E Z²)`. -/
theorem pRate_alg {l L P V lg D m2 x₁ a b x : ℝ} (hL : 0 < L) (hP : 0 < P) (hV : 0 ≤ V)
    (hlg : 0 ≤ lg) (hx₁ : 0 ≤ x₁) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : x₁ + a + b ≤ x)
    (hx : x ≤ 1 / 2) (hl : (1 - x₁) * L ≤ l) (hD0 : 0 ≤ D) (hD : D ≤ l * V * (1 + a))
    (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 2 * l + l ^ 2 * (1 + b)) :
    (P / L * (1 + V) + lg * (1 + 2 / L + x))⁻¹ * (1 - x) ≤ l ^ 2 / (P * (l + D) + lg * m2) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 < 1 - x₁ := by linarith
  have hl0 : 0 < l := lt_of_lt_of_le (mul_pos hx1 hL) hl
  set y := l / L with hydef
  have hy : 1 - x₁ ≤ y := by rw [hydef, le_div_iff₀ hL]; exact hl
  have hQ : 0 < P / L * (1 + V) + lg * (1 + 2 / L + x) := by
    have h1 : 0 < P / L * (1 + V) := by positivity
    have h2 : 0 ≤ lg * (1 + 2 / L + x) := mul_nonneg hlg (by have := div_pos two_pos hL; linarith)
    linarith
  have hDen : 0 < P * (l + D) + lg * m2 := by
    have h1 : 0 < P * (l + D) := mul_pos hP (by linarith)
    have h2 : 0 ≤ lg * m2 := mul_nonneg hlg hm20
    linarith
  -- the `P` part
  have k1 : P * (l + D) * (1 - x) ≤ P * (1 + V) * l * y := by
    have e1 : l + D ≤ l * (1 + V) * (1 + a) := by
      nlinarith [mul_nonneg hl0.le ha, mul_nonneg (mul_nonneg hl0.le hV) ha]
    have e2 : (1 + a) * (1 - x) ≤ 1 - x₁ := by nlinarith [mul_nonneg ha hx0]
    have e3 : 0 ≤ 1 - x := by linarith
    calc P * (l + D) * (1 - x) ≤ P * (l * (1 + V) * (1 + a)) * (1 - x) := by gcongr
      _ = P * (1 + V) * l * ((1 + a) * (1 - x)) := by ring
      _ ≤ P * (1 + V) * l * (1 - x₁) := by gcongr
      _ ≤ P * (1 + V) * l * y := by gcongr
  -- the `ℓ` part
  have k2 : lg * m2 * (1 - x) ≤ lg * (2 * l * y + l ^ 2 * (1 + x)) := by
    have e3 : 0 ≤ 1 - x := by linarith
    have e4 : m2 * (1 - x) ≤ 2 * l * y + l ^ 2 * (1 + x) := by
      have f1 : m2 * (1 - x) ≤ (2 * l + l ^ 2 * (1 + b)) * (1 - x) := by gcongr
      have f2 : 2 * l * (1 - x) ≤ 2 * l * y := by nlinarith
      have f3 : l ^ 2 * ((1 + b) * (1 - x)) ≤ l ^ 2 * (1 + x) := by
        gcongr; nlinarith [mul_nonneg hb hx0]
      nlinarith
    calc lg * m2 * (1 - x) = lg * (m2 * (1 - x)) := by ring
      _ ≤ lg * (2 * l * y + l ^ 2 * (1 + x)) := mul_le_mul_of_nonneg_left e4 hlg
  have hid : l ^ 2 * (P / L * (1 + V) + lg * (1 + 2 / L + x)) =
      P * (1 + V) * l * y + lg * (2 * l * y + l ^ 2 * (1 + x)) := by
    rw [hydef]; field_simp; ring
  rw [inv_mul_eq_div, div_le_div_iff₀ hQ hDen, hid]
  nlinarith

/-- `0 ≤ p_rate ≤ 1` when `C m^{−1/5} ≤ 1/2`. -/
theorem pRate_mem (g : ℝ) {C : ℝ} {M m P₀ : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m)
    (hx : C * (m : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 / 2) (hx0 : 0 ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ))) :
    0 ≤ pRate g C M m P₀ ∧ pRate g C M m P₀ ≤ 1 := by
  have hL := lamM_pos hM hm
  have hmM : (2 : ℝ) ≤ m * M := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hlg : log 2 ≤ log (m * M) := log_le_log (by norm_num) hmM
  have h2 := Real.log_two_gt_d9
  set x := C * (m : ℝ) ^ (-(1 / 5 : ℝ))
  set Q := 2 * (P₀ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) +
    6 * log (m * M) * (1 + 2 / lamM M m + x) with hQdef
  have hQ1 : 1 ≤ Q := by
    have h1 : 0 ≤ 2 * (P₀ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) := by positivity
    have h3 : 0 ≤ 2 / lamM M m := by positivity
    have h4 : 1 ≤ 6 * log (m * M) * (1 + 2 / lamM M m + x) := by nlinarith
    linarith
  have hQ0 : 0 < Q := by linarith
  have hpr : pRate g C M m P₀ = Q⁻¹ * (1 - x) := rfl
  rw [hpr]
  have hinv : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
  have hinv0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ0.le
  constructor
  · exact mul_nonneg hinv0 (by linarith)
  · nlinarith

set_option maxHeartbeats 1000000 in
/-- **A round of Theorem R″, with the rate** (paper §6.7): there is `C(g)` such that for
`m ≥ m₀(g)`, all `M ≥ 2`, `P₀ ≥ 100`, `|A| = ⌊m/2⌋`, and `s` in the window with `|u| ≤ M`,
`u ≡ s (mod 2)`: `Pr(round succeeds | S_E = s) ≥ p_rate` (`pRate`). Lemmas J, K′, B(1), B(2) and V
with the rate; the only hypothesis is that of Lemma K (Rosser–Schoenfeld). -/
theorem succB_rate (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ →
      ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      (2 : ℤ) ∣ u - s → pRate g C M m P₀ ≤ succB M m P₀ A s a := by
  obtain ⟨C₁, hC₁, m₁, h₁⟩ := lemmaB1_rate hg
  obtain ⟨C₂, hC₂, m₂, h₂⟩ := lemmaB2_rate hg
  obtain ⟨C₃, hC₃, m₃, h₃⟩ := lemmaV_rate hg
  set C := C₁ + C₂ + C₃ with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, max (max m₁ m₂) (max m₃ ⌈(2 * C + 1) ^ 5⌉₊),
    fun M m P₀ hM hm hP A hA s u a ha hw hu hsu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : m₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hmK : (2 * C + 1) ^ 5 ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  have hm0 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := le_trans (one_le_pow₀ (by linarith)) hmK
    exact_mod_cast this
  set r := (m : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx := rate_le_half hC hmK
  have hL := lamM_pos hM hm0
  have hl : (1 - C₁ * r) * lamM M m ≤ lamB M m s u := by
    have h := (abs_le.mp (h₁ M m hM hm1 s u hw hu hsu)).1
    rw [div_sub_one hL.ne', le_div_iff₀ hL] at h
    linarith
  have hC1x : C₁ * r ≤ 1 / 2 := by
    have : C₁ * r ≤ C * r := mul_le_mul_of_nonneg_right (by simp only [hCdef]; linarith) hr0
    linarith
  have hl0 : 0 < lamB M m s u := lt_of_lt_of_le (mul_pos (by linarith) hL) hl
  have hV := h₃ M m hM hm3 A hA s u a ha hw hu
  rw [div_le_iff₀ hl0] at hV
  have hB2 := h₂ M m hM hm2 s u hw hu hsu
  have hi : (if u = 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hm2' : m2B M m s u ≤ 2 * lamB M m s u + lamB M m s u ^ 2 * (1 + C₂ * r) := by
    nlinarith [mul_le_mul_of_nonneg_left hi hl0.le]
  have hm20 : 0 ≤ m2B M m s u := by unfold m2B; positivity
  have hP0 : (0 : ℝ) < 2 * P₀ := by
    have : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
    linarith
  have hlg : 0 ≤ log (m * M) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith)
  have hV0 : 0 ≤ 0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) := by
    positivity
  have halg := pRate_alg (P := 2 * P₀) (lg := 6 * log (m * M)) (x₁ := C₁ * r) (a := C₃ * r)
    (b := C₂ * r) (x := C * r) hL hP0 hV0 (by positivity) (by positivity) (by positivity)
    (by positivity) (by simp only [hCdef]; linarith) hx hl (DeqA_nonneg M m A a s) (by linarith)
    hm20 hm2'
  exact halg.trans (succB_ge hRS hP (by omega : 0 < M) (by omega : 0 < m) A ha)

set_option maxHeartbeats 2000000 in
/-- **Theorem R″ with the rate, general form** (paper §6.7): the setting of `thmRpp_gen`
(`R` blocks, a target that looks only at `w_G` and the block sums, halves with `|A| = ⌊m/2⌋`,
`P₀ ≥ 100`). There is `C(g)` such that for `m ≥ m₀(g)`, uniformly in `M ≥ 2`, on the event
`|T − S/2| ≤ S_G/2 − RmM`: `Pr(every round fails) ≤ (1 − (1 − 2e^{−g²/6}) p_rate)^R`, each round
succeeding with probability `≥ p_rate` (`succB_rate`). The only hypothesis is that of Lemma K
(Rosser–Schoenfeld). -/
theorem thmRpp_rate (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M h m R P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ →
      ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤
        (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m P₀) ^ R := by
  obtain ⟨C, hC, m₀, h₀⟩ := succB_rate hRS hg
  refine ⟨C, hC, max m₀ ⌈(2 * C + 1) ^ 5⌉₊, fun M h m R P₀ hM hm hP A hA T K hK => ?_⟩
  have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hmK : (2 * C + 1) ^ 5 ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hm)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := le_trans (one_le_pow₀ (by linarith)) hmK
    exact_mod_cast this
  have hx := rate_le_half hC hmK
  have hx0 : 0 ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  obtain ⟨hp0, hp1⟩ := pRate_mem g (P₀ := P₀) hM hm1 hx hx0
  set p := pRate g C M m P₀
  have hround : ∀ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
      (if condRp m wG (bsum wB) (T wG (bsum wB)) then
        ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0) ≤
      ((1 - (1 - 2 * exp (-(g ^ 2 / 6))) * p) * (M : ℝ) ^ m) ^ R := by
    intro wG
    refine rounds_fail_filt hM hm1 hg A wG (T wG) K hp0 hp1 ?_
    intro b hbm j hw hc
    have hb : ∀ k, 0 ≤ b k ∧ b k ≤ m * M := by
      intro k
      have := (Fintype.mem_piFinset.mp hbm) k
      unfold I0 at this; rw [mem_Icc] at this; exact this
    have hcR := condR_round wG hb hc j (hK j b)
    obtain ⟨hu, hpar⟩ := residR_bound wG hcR
    have ha : 2 * aRp wG (T wG b) b (K j b) j = b j + uRp wG (T wG b) b (K j b) j := by
      unfold aRp uRp; omega
    exact h₀ M m P₀ hM hm0 hP A hA (b j) _ _ ha hw hu hpar
  have hsum := sum_le_sum fun wG (_ : wG ∈ (univ : Finset (Fin h → Fin M))) => hround wG
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  simp only [Fintype.card_fun, Fintype.card_fin] at hsum
  push_cast at hsum
  rw [div_le_iff₀ (by positivity)]
  refine hsum.trans (le_of_eq ?_)
  rw [mul_pow]; ring

/-- `C m^{−1/5} ≤ η` as soon as `m ≥ (C/η + 1)⁵`. -/
theorem rate_le {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) {m : ℕ} (hm : (C / η + 1) ^ 5 ≤ (m : ℝ)) :
    C * (m : ℝ) ^ (-(1 / 5 : ℝ)) ≤ η := by
  have h := rate_le_half (K := C / (2 * η)) (by positivity) (m := m)
    (by rw [show 2 * (C / (2 * η)) + 1 = C / η + 1 by field_simp]; exact hm)
  have e : C * (m : ℝ) ^ (-(1 / 5 : ℝ)) = 2 * η * (C / (2 * η) * (m : ℝ) ^ (-(1 / 5 : ℝ))) := by
    field_simp
  rw [e]; nlinarith

/-- The least `m ≥ 1` with `σ⁴m² ≤ 8^m` (that is, `2^m ≥ (σ√m)^{4/3}`) satisfies `Hm` (`M ≥ 4`). -/
theorem Hm_of_isLeast {M m : ℕ} (hM : 4 ≤ M)
    (h : IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m) : Hm M m := by
  obtain ⟨⟨hm1, hm⟩, hmin⟩ := h
  have hσ1 : 1 ≤ sig2 M := by
    unfold sig2; have : (4 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  refine ⟨hm, ?_⟩
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hlt : (8 : ℝ) ^ (m - 1) < sig2 M ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 := by
      by_contra hc; push Not at hc
      have := hmin ⟨by omega, hc⟩
      omega
    have e : (8 : ℝ) ^ m = 8 * 8 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have hle : ((m - 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le m 1) 2
    have : 0 ≤ sig2 M ^ 2 := sq_nonneg _
    rw [e]; nlinarith
  · have hm1' : m = 1 := le_antisymm h1 hm1
    rw [hm1']; simp only [pow_one, Nat.cast_one, one_pow, mul_one]
    nlinarith

/-- `p_rate ≥ p·(1 − Cr)/(1 + Cr)`, `r = m^{−1/5}`, with `p` of `pRpp`. -/
theorem pRate_ge (g : ℝ) {C : ℝ} {M m P₀ : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m)
    (hx0 : 0 ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ))) (hx : C * (m : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 / 2) :
    pRpp g M m P₀ * ((1 - C * (m : ℝ) ^ (-(1 / 5 : ℝ))) / (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ)))) ≤
      pRate g C M m P₀ := by
  have hL := lamM_pos hM hm
  have hlg : 0 ≤ log (m * M) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith)
  set x := C * (m : ℝ) ^ (-(1 / 5 : ℝ))
  set A := 2 * (P₀ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2))
  set Lg := 6 * log (m * M)
  have hA : 0 ≤ A := by positivity
  have hLg : 0 ≤ Lg := by positivity
  have h2L : 0 ≤ 2 / lamM M m := by positivity
  set Q := A + Lg * (1 + 2 / lamM M m)
  have hQ : 0 < Q := by
    have : 0 < Lg * (1 + 2 / lamM M m) ∨ 0 < A := by
      by_cases h : 0 < Lg
      · left; positivity
      · right
        have hlg0 : Lg = 0 := le_antisymm (not_lt.mp h) hLg
        have hmM : (2 : ℝ) ≤ m * M := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          have : (2 : ℝ) ≤ M := by exact_mod_cast hM
          nlinarith
        have : 0 < log ((m : ℝ) * M) := Real.log_pos (by linarith)
        simp only [Lg] at hlg0; linarith
    rcases this with h | h <;> nlinarith
  have hpR : pRpp g M m P₀ = 1 / Q := rfl
  have hpr : pRate g C M m P₀ = (A + Lg * (1 + 2 / lamM M m + x))⁻¹ * (1 - x) := rfl
  have hQ' : A + Lg * (1 + 2 / lamM M m + x) ≤ Q * (1 + x) := by
    have : Lg ≤ Q := by simp only [Q]; nlinarith
    nlinarith
  have hQ'0 : 0 < A + Lg * (1 + 2 / lamM M m + x) := by nlinarith
  rw [hpR, hpr, inv_mul_eq_div, one_div_mul_eq_div, div_div,
    div_le_div_iff₀ (mul_pos (by linarith) hQ) hQ'0]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Theorem R″** (paper §6.7), from the rate form (`thmRpp_rate`). Fix `g ≥ 0` with
`2e^{−g²/6} < 1` (say `g = 3`). Take `m` the least integer `≥ 1` with `2^m ≥ (σ√m)^{4/3}`,
written `σ⁴m² ≤ 8^m`, `P₀ = ⌊λ_m/2⌋`, halves with `|A| = ⌊m/2⌋`. There is `C(g) ≥ 0` such that:
(1) `p_rate ≥ (1 − ε)/(6 ln(mM))` for every `ε > 0` and `M ≥ M₀(g, ε)`, i.e.
`p_rate ≥ (1 − o(1))/(6 ln(mM))` as `M → ∞`; (2) for every `δ > 0`, for `M ≥ M₀(g, δ)` and
`R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p_rate)⌉` rounds, the probability that
`|T − S/2| ≤ S_G/2 − RmM` and every round fails is at most `δ`. The only hypothesis is that of
Lemma K (Rosser–Schoenfeld). The running time is not formalized. -/
theorem thmRpp_asymp (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) (hge : 2 * exp (-(g ^ 2 / 6)) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M m : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        (1 - ε) / (6 * log (m * M)) ≤ pRate g C M m ⌊lamM M m / 2⌋₊) ∧
      ∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M h m R : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        R = ⌈log (1 / δ) / ((1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m ⌊lamM M m / 2⌋₊)⌉₊ →
        ∀ A : Finset (Fin m), A.card = m / 2 →
        ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
        (∀ j b, j ∉ K j b) →
        (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
            (if condRp m wG (bsum wB) (T wG (bsum wB)) then
              ∏ j, (1 - sPr ⌊lamM M m / 2⌋₊ A (wB j)
                (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
          ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤ δ := by
  obtain ⟨C, hC, m₀, h₀⟩ := thmRpp_rate hRS hg
  refine ⟨C, hC, ?_, ?_⟩
  · -- (1): `p_rate ≥ (1 − ε)/(6 ln(mM))`
    intro ε hε
    set η := min ε (1 / 2) / 3 with hηdef
    have hη0 : 0 < η := by positivity
    have hη1 : η ≤ 1 / 6 := by have := min_le_right ε (1 / 2); rw [hηdef]; linarith
    have hηε : 3 * η ≤ ε := by have := min_le_left ε (1 / 2); rw [hηdef]; linarith
    obtain ⟨M₁, h₁⟩ := params_Rpp g hη0 (by linarith) (max ⌈(C / η + 1) ^ 5⌉₊ ⌈(2 * C + 1) ^ 5⌉₊)
    refine ⟨max M₁ 4, fun M m hM hmin => ?_⟩
    have hM4 : 4 ≤ M := le_trans (le_max_right _ _) hM
    have hm1 : 1 ≤ m := hmin.1.1
    obtain ⟨hmk, -, hp⟩ := h₁ M m (le_trans (le_max_left _ _) hM) hm1 (Hm_of_isLeast hM4 hmin)
    have hr0 : 0 ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hxη := rate_le hC hη0 (m := m)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hmk))
    have hx := rate_le_half hC (m := m)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hmk))
    have hge' := pRate_ge g (P₀ := ⌊lamM M m / 2⌋₊) (by omega : 2 ≤ M) hm1 hr0 hx
    set x := C * (m : ℝ) ^ (-(1 / 5 : ℝ))
    have hmM : (2 : ℝ) ≤ m * M := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have : (4 : ℝ) ≤ M := by exact_mod_cast hM4
      nlinarith
    have hLg : 0 < 6 * log ((m : ℝ) * M) := by have := Real.log_pos (by linarith : (1 : ℝ) < m * M); positivity
    have hfr : 1 - 2 * η ≤ (1 - x) / (1 + x) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have hp0 : 0 ≤ pRpp g M m ⌊lamM M m / 2⌋₊ := pRpp_nonneg g (by omega) hm1
    have h1 : (1 - η) / (6 * log (m * M)) * (1 - 2 * η) ≤
        pRpp g M m ⌊lamM M m / 2⌋₊ * ((1 - x) / (1 + x)) :=
      mul_le_mul hp (by linarith) (by linarith) hp0
    have h2 : (1 - ε) / (6 * log (m * M)) ≤ (1 - η) / (6 * log (m * M)) * (1 - 2 * η) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hLg]; nlinarith
    linarith
  · -- (2): `δ`
    intro δ hδ
    obtain ⟨M₁, h₁⟩ := params_Rpp g (ε := 1 / 2) (by norm_num) (by norm_num) (max m₀ ⌈(2 * C + 1) ^ 5⌉₊)
    refine ⟨max M₁ 4, fun M h m R hM hmin hR A hA T K hK => ?_⟩
    have hM4 : 4 ≤ M := le_trans (le_max_right _ _) hM
    have hm1 : 1 ≤ m := hmin.1.1
    obtain ⟨hmk, hP, -⟩ := h₁ M m (le_trans (le_max_left _ _) hM) hm1 (Hm_of_isLeast hM4 hmin)
    have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hmk
    have hx := rate_le_half hC (m := m)
      (le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hmk))
    have hr0 : 0 ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine (h₀ M h m R ⌊lamM M m / 2⌋₊ (by omega) hm0 hP A hA T K hK).trans ?_
    obtain ⟨hp0, hp1⟩ := pRate_mem g (P₀ := ⌊lamM M m / 2⌋₊) (by omega : 2 ≤ M) hm1 hx hr0
    -- `p_rate > 0`
    have hpos : 0 < pRate g C M m ⌊lamM M m / 2⌋₊ := by
      have hge0 := pRate_ge g (P₀ := ⌊lamM M m / 2⌋₊) (by omega : 2 ≤ M) hm1 hr0 hx
      have hpR : 0 < pRpp g M m ⌊lamM M m / 2⌋₊ := by
        have hL := lamM_pos (by omega : 2 ≤ M) hm1
        have hmM : (2 : ℝ) ≤ m * M := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have : (4 : ℝ) ≤ M := by exact_mod_cast hM4
          nlinarith
        have : 0 < log ((m : ℝ) * M) := Real.log_pos (by linarith)
        unfold pRpp; positivity
      have : 0 < (1 - C * (m : ℝ) ^ (-(1 / 5 : ℝ))) / (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ))) :=
        div_pos (by linarith) (by linarith)
      exact lt_of_lt_of_le (mul_pos hpR this) hge0
    set p := pRate g C M m ⌊lamM M m / 2⌋₊
    have he : 0 < 1 - 2 * exp (-(g ^ 2 / 6)) := by linarith
    set x := (1 - 2 * exp (-(g ^ 2 / 6))) * p
    have hx0 : 0 < x := mul_pos he hpos
    have hx1 : x ≤ 1 := by
      have : 1 - 2 * exp (-(g ^ 2 / 6)) ≤ 1 := by linarith [Real.exp_pos (-(g ^ 2 / 6))]
      nlinarith
    refine pow_le_delta hx1 hδ ?_
    have hc := Nat.le_ceil (log (1 / δ) / x)
    rw [← hR] at hc
    rw [div_le_iff₀ hx0] at hc
    linarith

end ArcsAlgo.LLT
