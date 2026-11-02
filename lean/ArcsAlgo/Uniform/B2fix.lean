module

public import ArcsAlgo.Uniform.Sum2
public import ArcsAlgo.Uniform.LemmaB1
set_option autoImplicit false

/-!
# Lemma B(2) for fixed `M, m, T` (paper §6.3)

`B2_fixed`: if `λ ≥ λ_m/2` (from Lemma B(1)) and `δ₂ ≤ 1/2`, then
`E[Z(u)² | S_E = s] ≤ λ(1 + 1[u = 0]) + λ²·Br(g, m, T)`, with
`Br = F(1 + K₁e^{g²/2}/m)²(1 + δ₂) + K₂e^{g²/2}/m + K₃e^{g²/2} m^{3/2} e^{−2T²/m}` (`BrB`).
The lower bounds `λ ≥ 2^m/(4σ√(2πm))` (`lamM_ge`) and `g_m(s) ≥ e^{−g²/2}/(σ√(2πm))` (`gm_ge`)
turn the absolute errors of `B2_sum` into relative ones, uniformly in `M ≥ 2`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem gm_ge {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} {s : ℤ}
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) :
    (exp (g ^ 2 / 2))⁻¹ / (√(2 * π) * (√(sig2 M) * √(m : ℝ))) ≤ gaussB M m s := by
  have hσ := sig2_pos hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsσ := Real.sqrt_pos.mpr hσ
  have hsm := Real.sqrt_pos.mpr hm0
  have hz : zB M m s ^ 2 ≤ g ^ 2 := by
    unfold zB tB
    rw [div_pow, div_le_iff₀ (by positivity), mul_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs, mul_pow, mul_pow] at h
    linarith
  unfold gaussB
  have e : √(2 * π * m * sig2 M) = √(2 * π) * (√(sig2 M) * √(m : ℝ)) := by
    rw [show 2 * π * m * sig2 M = (2 * π) * (sig2 M * m) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul hσ.le]
  rw [e, one_div_mul_eq_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Real.exp_neg]
  exact exp_le_exp.mpr (by linarith)

theorem lamM_ge {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) :
    2 ^ m / (2 * √(sig2 M) * √(2 * π * m)) ≤ lamM M m := by
  have hσ := sig2_pos hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨hMσ, -⟩ := sqrt_sig_ge hM
  have hc0 : 0 < cMB M := by unfold cMB; positivity
  have hc1 : cMB M ≤ 1 := by
    unfold cMB
    have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : 1 / (6 * (M : ℝ) ^ 2) ≤ 1 / 24 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  unfold lamM
  have hs1 : √(2 * π * m * cMB M) ≤ √(2 * π * m) := Real.sqrt_le_sqrt (by
    have : 0 < 2 * π * m := by positivity
    nlinarith)
  have hpos : 0 < (M : ℝ) * √(2 * π * m * cMB M) := by
    have : 0 < √(2 * π * m * cMB M) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [div_le_div_iff₀ (by have : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
                          have : 0 < √(2 * π * m) := Real.sqrt_pos.mpr (by positivity)
                          positivity) hpos]
  have : (M : ℝ) * √(2 * π * m * cMB M) ≤ 4 * √(sig2 M) * √(2 * π * m) :=
    mul_le_mul hMσ hs1 (Real.sqrt_nonneg _) (by positivity)
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [pow_succ]
  nlinarith

/-- An elementary ratio inequality. -/
theorem ratio_B2 {p gm S1 S2 F Δ X Z i η1 d η2 η3 : ℝ} (hp : 0 < p) (hgm : 0 < gm) (hS1 : 0 < S1)
    (hF : 0 ≤ F) (hi : 0 ≤ i) (hη1 : 0 ≤ η1) (hΔ0 : 0 ≤ Δ)
    (hS2 : S2 ≤ S1 * (1 + i) + F / gm * (S1 + Δ) ^ 2 + X + Z)
    (hΔ : Δ ≤ η1 * S1) (hpg : p ≤ (1 + d) * gm) (hX : X ≤ η2 * ((S1 / p) ^ 2 * p))
    (hZ : Z ≤ η3 * ((S1 / p) ^ 2 * p)) :
    S2 / p ≤ S1 / p * (1 + i) + (S1 / p) ^ 2 * (F * (1 + η1) ^ 2 * (1 + d) + η2 + η3) := by
  set lam := S1 / p
  have hS1e : S1 = lam * p := by simp only [lam]; field_simp
  have hsq : (S1 + Δ) ^ 2 ≤ S1 ^ 2 * (1 + η1) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by nlinarith) 2
  have hF2 : F / gm * (S1 + Δ) ^ 2 ≤ F / gm * (S1 ^ 2 * (1 + η1) ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (div_nonneg hF hgm.le)
  have hFp : F / gm * (S1 ^ 2 * (1 + η1) ^ 2) ≤ lam ^ 2 * (F * (1 + η1) ^ 2 * (1 + d)) * p := by
    rw [hS1e]
    have : F / gm * ((lam * p) ^ 2 * (1 + η1) ^ 2) = lam ^ 2 * (F * (1 + η1) ^ 2) * (p / gm) * p := by
      field_simp
    rw [this]
    have h1 : p / gm ≤ 1 + d := by rw [div_le_iff₀ hgm]; linarith
    have h2 : 0 ≤ lam ^ 2 * (F * (1 + η1) ^ 2) := by positivity
    calc lam ^ 2 * (F * (1 + η1) ^ 2) * (p / gm) * p ≤ lam ^ 2 * (F * (1 + η1) ^ 2) * (1 + d) * p := by
          gcongr
      _ = _ := by ring
  rw [div_le_iff₀ hp]
  have : S1 * (1 + i) = lam * (1 + i) * p := by rw [hS1e]; ring
  have e : (lam * (1 + i) + lam ^ 2 * (F * (1 + η1) ^ 2 * (1 + d) + η2 + η3)) * p =
      lam * (1 + i) * p + lam ^ 2 * (F * (1 + η1) ^ 2 * (1 + d)) * p + η2 * (lam ^ 2 * p) +
        η3 * (lam ^ 2 * p) := by ring
  rw [e]
  linarith

/-- The constants of the error terms. -/
noncomputable def K1B : ℝ := 3808 * 16 * π
noncomputable def K2B : ℝ := 3162 * 1024 * 64 * π * √(2 * π)
noncomputable def K3B : ℝ := 384 * π * √(2 * π)

/-- The bracket `F(1 + η₁)²(1 + δ₂) + η₂ + η₃` of Lemma B(2). -/
noncomputable def BrB (g : ℝ) (m T : ℕ) : ℝ :=
  FacB g m T * (1 + K1B * exp (g ^ 2 / 2) / m) ^ 2 * (1 + del2 g m) +
    K2B * exp (g ^ 2 / 2) / m +
    K3B * exp (g ^ 2 / 2) * ((m : ℝ) * √(m : ℝ) * exp (-(2 * (T : ℝ) ^ 2 / m)))

set_option maxHeartbeats 2000000 in
/-- **Lemma B(2) for fixed `M, m, T`**: if `λ ≥ λ_m/2` and `δ₂ ≤ 1/2`, then
`E[Z(u)² | S_E = s] ≤ λ(1 + 1[u = 0]) + λ²·Br(g, m, T)`. -/
theorem B2_fixed {M m T : ℕ} (hM : 2 ≤ M) (hm : 32 ≤ m) (hTm : 16 * T ≤ m) {g : ℝ} (hg : 0 ≤ g)
    {s u : ℤ} (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M)
    (hsu : (2 : ℤ) ∣ u - s) (hlam : lamM M m / 2 ≤ lamB M m s u) (hd : del2 g m ≤ 1 / 2) :
    m2B M m s u ≤ lamB M m s u * (1 + if u = 0 then 1 else 0) +
      lamB M m s u ^ 2 * BrB g m T := by
  obtain ⟨k, hk⟩ := hsu
  set a := s + k with ha'
  have ha : 2 * a = s + u := by rw [ha']; linarith
  have hM0 : 0 < M := by omega
  have hσ := sig2_pos hM
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hs := Real.sqrt_pos.mpr hσ
  have hsm := Real.sqrt_pos.mpr hm0
  have hπ := pi_pos
  have h2π : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hss : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hσ.le
  have hsm2 : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  have h2πm : √(2 * π * m) = √(2 * π) * √(m : ℝ) := Real.sqrt_mul (by positivity) _
  have h2π2 : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  set gm := gaussB M m s
  set p := lawS M m s
  have hgm0 := gm_ge hM hm1 hw
  have hgm : 0 < gm := lt_of_lt_of_le (by positivity) hgm0
  have hrel := law_rel hM (by omega) hw
  have hpg : p ≤ (1 + del2 g m) * gm := by
    have := (abs_le.mp hrel).2
    rw [div_sub_one hgm.ne', div_le_iff₀ hgm] at this; linarith
  have hpg2 : gm / 2 ≤ p := by
    have := (abs_le.mp hrel).1
    rw [div_sub_one hgm.ne', le_div_iff₀ hgm] at this
    have := mul_le_mul_of_nonneg_right hd hgm.le
    linarith
  have hp : 0 < p := by linarith
  -- `λ` and `E[Z²]` as sums
  have hlamE : lamB M m s u = (∑ x : Finset (Fin m), Rx M m x a s) / p := by
    rw [lamB_eq hM s u a ha]; unfold Rx
    rw [sum_card (fun k => lawS M k a * lawS M (m - k) (s - a))]
  have hm2E : m2B M m s u = (∑ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s) / p := by
    rw [← sumZ2_eq s u a ha]
    unfold m2B
    rw [cntS_eq hM0, div_div]
  set S1 := ∑ x : Finset (Fin m), Rx M m x a s
  set S2 := ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s
  have hS2 := B2_sum hM hm hTm hg ha hw hu
  -- lower bounds
  have hlm := lamM_ge hM hm1
  set L0 := 2 ^ m / (2 * √(sig2 M) * √(2 * π * m))
  have hL0 : 0 < L0 := by positivity
  have hlam' : L0 / 2 ≤ S1 / p := by rw [← hlamE]; linarith
  have hS1 : (L0 / 2) * (gm / 2) ≤ S1 := by
    have h1 : S1 = S1 / p * p := by field_simp
    rw [h1]; exact mul_le_mul hlam' hpg2 (by linarith) (by linarith)
  have hS1g : (L0 / 2) * ((exp (g ^ 2 / 2))⁻¹ / (√(2 * π) * (√(sig2 M) * √(m : ℝ))) / 2) ≤ S1 :=
    le_trans (by gcongr) hS1
  have hS1p : 0 < S1 := lt_of_lt_of_le (mul_pos (half_pos hL0) (by positivity)) hS1g
  have hl2p : (L0 / 2) * ((L0 / 2) * ((exp (g ^ 2 / 2))⁻¹ / (√(2 * π) * (√(sig2 M) * √(m : ℝ))) / 2)) ≤
      (S1 / p) ^ 2 * p := by
    have : (S1 / p) ^ 2 * p = S1 / p * S1 := by field_simp
    rw [this]; exact mul_le_mul hlam' hS1g (by positivity) (by positivity)
  have hE0 := exp_pos (g ^ 2 / 2)
  have e1 : √(π * 2) ^ 2 = π * 2 := Real.sq_sqrt (by positivity)
  -- the three error terms
  have hΔ : 2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) ≤ K1B * exp (g ^ 2 / 2) / m * S1 := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS1g (by unfold K1B; positivity))
    simp only [L0, K1B]
    rw [h2πm]
    field_simp
    simp only [hss, hsm2, h2π2, e1]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
  have hX : 4 ^ m * ErrB M m ≤ K2B * exp (g ^ 2 / 2) / m * ((S1 / p) ^ 2 * p) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hl2p (by unfold K2B; positivity))
    simp only [L0, K2B, ErrB]
    rw [h2πm, Real.sqrt_div' _ (by norm_num), show √(16 : ℝ) = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4]
    field_simp
    simp only [hss, hsm2, h2π2, e1]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
  have hZ : 6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) / (M : ℝ) ^ 3 ≤
      K3B * exp (g ^ 2 / 2) * ((m : ℝ) * √(m : ℝ) * exp (-(2 * (T : ℝ) ^ 2 / m))) *
        ((S1 / p) ^ 2 * p) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hl2p (by unfold K3B; positivity))
    obtain ⟨hMσ, -⟩ := sqrt_sig_ge hM
    have hσM : √(sig2 M) ≤ M := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      rw [Real.sqrt_le_left (by positivity)]; unfold sig2; nlinarith
    have hσ3 : √(sig2 M) ^ 3 ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ hs.le hσM 3
    have hT := exp_pos (-(2 * (T : ℝ) ^ 2 / m))
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    calc 6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) / (M : ℝ) ^ 3 ≤
        6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) / √(sig2 M) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hσ3
      _ = _ := by
          simp only [L0, K3B]
          rw [h2πm, e4]
          field_simp
          simp only [hss, hsm2, h2π2, e1] at *
          ring
  have hR := ratio_B2 hp hgm hS1p (by unfold FacB; positivity) (by split_ifs <;> norm_num)
    (by unfold K1B; positivity) (by positivity) hS2 hΔ hpg hX hZ
  rw [hm2E, hlamE]
  calc S2 / p ≤ S1 / p * (1 + if u = 0 then 1 else 0) + (S1 / p) ^ 2 *
        (FacB g m T * (1 + K1B * exp (g ^ 2 / 2) / m) ^ 2 * (1 + del2 g m) +
          K2B * exp (g ^ 2 / 2) / m +
          K3B * exp (g ^ 2 / 2) * ((m : ℝ) * √(m : ℝ) * exp (-(2 * (T : ℝ) ^ 2 / m)))) := hR
    _ = _ := by unfold BrB; ring

end ArcsAlgo.LLT
