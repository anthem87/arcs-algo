module

public import ArcsAlgo.Uniform.Quad
set_option autoImplicit false

/-!
# The Gaussian comparison for typical pairs (paper §6.3, proof of Lemma B(2))

* `qg_le`: the Gaussian four-class sum is at most
  `g_{k₁}(a) g_{m−k₁}(s − a) φ(a; ν, v)(1 + 2/√(2πw))`: the density of `(S_x, S_E)` times the
  density of `S_y` given `S_x = a` and `S_E = s`.
* `gaussB_pair`: `g_k(a) g_{m−k}(s − a) = g_m(s) φ(a; ks/m, σ²k(m − k)/m)`, the density of `S_y`
  given `S_E = s`.
* `typ_ratio`: for typical class sizes (`|k₁ − m/2|, |k₂ − m/2|, |A + B − m/2| ≤ T`, `16T ≤ m`)
  the two conditional densities differ by at most `(1 + 64T²/m²) e^{64TY²/(σ²m²)}`: the
  conditional covariance is `σ²(C − k₁k₂/m)` with `|C − k₁k₂/m| ≤ T`, so the correlation is
  `O(T/m)` and the shift of the mean is `O(TY/m)`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- The Gaussian four-class sum, after the integral over `c`. -/
theorem qg_le {M m : ℕ} (hM : 2 ≤ M) {α β γ δ : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (hγ : 1 ≤ γ)
    (hδ : 1 ≤ δ) (hsum : α + β + γ + δ = m) (a s : ℤ) (I : Finset ℤ) :
    ∑ c ∈ I, gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) * gaussB M δ (s - 2 * a + c) ≤
      gaussB M (α + γ) a * gaussB M (m - (α + γ)) (s - a) *
        gd ((γ : ℝ) * a / ((γ : ℝ) + α) + (β : ℝ) * ((s : ℝ) - a) / ((β : ℝ) + δ))
          (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α) + (β : ℝ) * δ / ((β : ℝ) + δ))) a *
        (1 + 2 / √(2 * π * ((sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α))) *
          (sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ))) /
          (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α)) + sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ)))))) := by
  have hσ := sig2_pos hM
  have hA : (0 : ℝ) < α := by exact_mod_cast hα
  have hB : (0 : ℝ) < β := by exact_mod_cast hβ
  have hC : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hD : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨c3, h⟩ := four_gauss hA hB hC hD hσ (muW M) a s
  set W := (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α))) * (sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ))) /
          (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α)) + sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ)))
  have hW : 0 < W := by positivity
  set K := gd (((γ : ℝ) + α) * muW M) (((γ : ℝ) + α) * sig2 M) a *
    gd (((β : ℝ) + δ) * muW M) (((β : ℝ) + δ) * sig2 M) ((s : ℝ) - a) *
    gd ((γ : ℝ) * a / ((γ : ℝ) + α) + (β : ℝ) * ((s : ℝ) - a) / ((β : ℝ) + δ))
      (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α) + (β : ℝ) * δ / ((β : ℝ) + δ))) a
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (gd_nonneg _ _ _) (gd_nonneg _ _ _)) (gd_nonneg _ _ _)
  have hterm : ∀ c ∈ I, gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) *
      gaussB M δ (s - 2 * a + c) = K * gd c3 W c := by
    intro c _
    rw [gaussB_eq_gd hM hγ, gaussB_eq_gd hM hα, gaussB_eq_gd hM hβ, gaussB_eq_gd hM hδ]
    push_cast
    rw [h c]
  rw [sum_congr rfl hterm, ← mul_sum]
  have h1 := gd_sum_le hW c3 I
  have e1 : gaussB M (α + γ) a = gd (((γ : ℝ) + α) * muW M) (((γ : ℝ) + α) * sig2 M) a := by
    rw [gaussB_eq_gd hM (by omega)]; push_cast; ring_nf
  have e2 : gaussB M (m - (α + γ)) (s - a) =
      gd (((β : ℝ) + δ) * muW M) (((β : ℝ) + δ) * sig2 M) ((s : ℝ) - a) := by
    rw [show m - (α + γ) = β + δ by omega, gaussB_eq_gd hM (by omega)]; push_cast; ring_nf
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h1 hK

theorem gd_pair_real {k m σ2 μ : ℝ} (hk : 0 < k) (hkm : k < m) (hσ : 0 < σ2) (a s : ℝ) :
    gd (k * μ) (k * σ2) a * gd ((m - k) * μ) ((m - k) * σ2) (s - a) =
      gd (m * μ) (m * σ2) s * gd (k * s / m) (σ2 * k * (m - k) / m) a := by
  have hmk : 0 < m - k := by linarith
  have hm : 0 < m := by linarith
  rw [gd_mul (mul_pos hk hσ) (mul_pos hmk hσ) s a]
  have e1 : k * μ + (m - k) * μ = m * μ := by ring
  have e2 : k * σ2 + (m - k) * σ2 = m * σ2 := by ring
  have e3 : (k * μ * ((m - k) * σ2) + (s - (m - k) * μ) * (k * σ2)) / (k * σ2 + (m - k) * σ2) =
      k * s / m := by rw [e2]; field_simp; ring
  have e4 : k * σ2 * ((m - k) * σ2) / (k * σ2 + (m - k) * σ2) = σ2 * k * (m - k) / m := by
    rw [e2]; field_simp
  rw [e3, e4, e1, e2]

/-- `g_k(a) g_{m−k}(s − a) = g_m(s) φ(a; ks/m, σ²k(m − k)/m)`. -/
theorem gaussB_pair {M m k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (a s : ℤ) :
    gaussB M k a * gaussB M (m - k) (s - a) =
      gaussB M m s * gd ((k : ℝ) * s / m) (sig2 M * k * ((m : ℝ) - k) / m) a := by
  have hσ := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkm' : (k : ℝ) < m := by exact_mod_cast (by omega : k < m)
  have hc : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  rw [gaussB_eq_gd hM hk, gaussB_eq_gd hM (by omega), gaussB_eq_gd hM (by omega), hc]
  have h := gd_pair_real (μ := muW M) hk0 hkm' hσ (a : ℝ) (s : ℝ)
  push_cast
  exact h

theorem id_Vv {A B C D σ2 : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    σ2 * (B + C) * ((A + B + C + D) - (B + C)) / (A + B + C + D) -
      σ2 * (C * A / (C + A) + B * D / (B + D)) =
    σ2 * (A + B + C + D) * (C - (C + A) * (B + C) / (A + B + C + D)) ^ 2 /
      ((C + A) * ((A + B + C + D) - (C + A))) := by
  have e : (A + B + C + D) - (C + A) = B + D := by ring
  rw [e]
  have h1 : C + A ≠ 0 := by positivity
  have h2 : B + D ≠ 0 := by positivity
  have h3 : A + B + C + D ≠ 0 := by positivity
  field_simp; ring

theorem id_nu {A B C D a s : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    C * a / (C + A) + B * (s - a) / (B + D) - (B + C) * s / (A + B + C + D) =
    (C - (C + A) * (B + C) / (A + B + C + D)) * (A + B + C + D) /
      ((C + A) * ((A + B + C + D) - (C + A))) * (a - (C + A) * s / (A + B + C + D)) := by
  have e : (A + B + C + D) - (C + A) = B + D := by ring
  rw [e]
  have h1 : C + A ≠ 0 := by positivity
  have h2 : B + D ≠ 0 := by positivity
  have h3 : A + B + C + D ≠ 0 := by positivity
  field_simp; ring

theorem id_Dm {A B C D : ℝ} (hm : 0 < A + B + C + D) :
    (C - (C + A) * (B + C) / (A + B + C + D)) * (A + B + C + D) =
      -((A + B + C + D) * (A + B - (A + B + C + D) / 2) / 2) -
        (C + A - (A + B + C + D) / 2) * (B + C - (A + B + C + D) / 2) := by
  have h3 : A + B + C + D ≠ 0 := hm.ne'
  field_simp; ring

set_option maxHeartbeats 1000000 in
/-- **The pointwise Gaussian comparison for typical pairs** (paper §6.3, proof of Lemma B(2)):
given `S_E = s`, the density of `S_y` given `S_x = a` against that of `S_y` alone. With
`|k₁ − m/2|, |k₂ − m/2|, |A + B − m/2| ≤ T`, `16T ≤ m`, and `|a − k_i s/m| ≤ Y`,
`φ(a; ν, v) ≤ (1 + 64T²/m²) e^{64TY²/(σ²m²)} φ(a; k₂s/m, σ²k₂(m − k₂)/m)`. -/
theorem typ_ratio {A B C D σ2 T Y a s : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hσ : 0 < σ2) (hT : 0 ≤ T) (hTm : 16 * T ≤ A + B + C + D)
    (h1 : |C + A - (A + B + C + D) / 2| ≤ T) (h2 : |B + C - (A + B + C + D) / 2| ≤ T)
    (h3 : |A + B - (A + B + C + D) / 2| ≤ T)
    (hY1 : |a - (C + A) * s / (A + B + C + D)| ≤ Y) (hY2 : |a - (B + C) * s / (A + B + C + D)| ≤ Y) :
    gd (C * a / (C + A) + B * (s - a) / (B + D)) (σ2 * (C * A / (C + A) + B * D / (B + D))) a ≤
      (1 + 64 * T ^ 2 / (A + B + C + D) ^ 2) *
        exp (64 * T * Y ^ 2 / (σ2 * (A + B + C + D) ^ 2)) *
        gd ((B + C) * s / (A + B + C + D)) (σ2 * (B + C) * ((A + B + C + D) - (B + C)) / (A + B + C + D)) a := by
  set m := A + B + C + D with hm
  set k1 := C + A
  set k2 := B + C
  have hm0 : 0 < m := by positivity
  set ν := C * a / (C + A) + B * (s - a) / (B + D)
  set v := σ2 * (C * A / (C + A) + B * D / (B + D))
  set ν' := k2 * s / m
  set V := σ2 * k2 * (m - k2) / m
  set Dd := C - k1 * k2 / m
  have hv : 0 < v := by positivity
  have hk1 : k1 * (m - k1) = m ^ 2 / 4 - (k1 - m / 2) ^ 2 := by ring
  have hk2 : k2 * (m - k2) = m ^ 2 / 4 - (k2 - m / 2) ^ 2 := by ring
  have hT2 : T ^ 2 ≤ m ^ 2 / 256 := by nlinarith
  have hq1 : (k1 - m / 2) ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp h1; nlinarith
  have hq2 : (k2 - m / 2) ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp h2; nlinarith
  have hK1 : m ^ 2 / 8 ≤ k1 * (m - k1) := by rw [hk1]; nlinarith
  have hK2 : m ^ 2 / 8 ≤ k2 * (m - k2) := by rw [hk2]; nlinarith
  have hBD : B + D = m - k1 := by simp only [m, k1]; ring
  have hVv : V - v = σ2 * m * Dd ^ 2 / (k1 * (m - k1)) := id_Vv hA hB hC hD
  have hνν : ν - ν' = Dd * m / (k1 * (m - k1)) * (a - k1 * s / m) := id_nu hA hB hC hD
  -- `|D| ≤ T`
  have hDm : Dd * m = -(m * (A + B - m / 2) / 2) - (k1 - m / 2) * (k2 - m / 2) := id_Dm hm0
  have hD : |Dd| ≤ T := by
    have e1 : |(k1 - m / 2) * (k2 - m / 2)| ≤ T * T := by
      rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hT
    have e2 : |Dd * m| ≤ m * T / 2 + T * T := by
      rw [hDm]
      calc |-(m * (A + B - m / 2) / 2) - (k1 - m / 2) * (k2 - m / 2)|
          ≤ |m * (A + B - m / 2) / 2| + |(k1 - m / 2) * (k2 - m / 2)| := by
            rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
        _ ≤ m * T / 2 + T * T := by
            gcongr
            rw [abs_div, abs_mul, abs_of_pos hm0, abs_two]
            have := mul_le_mul_of_nonneg_left h3 hm0.le
            linarith
    rw [abs_mul, abs_of_pos hm0] at e2
    have : T * T ≤ m * T / 16 := by nlinarith
    by_contra hc; push Not at hc
    nlinarith
  have hD2 : Dd ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp hD; nlinarith [sq_abs Dd, abs_nonneg Dd]
  -- the variances
  have hV : σ2 * m / 8 ≤ V := by
    simp only [V]; rw [le_div_iff₀ hm0]
    have : σ2 * (m ^ 2 / 8) ≤ σ2 * (k2 * (m - k2)) := mul_le_mul_of_nonneg_left hK2 hσ.le
    nlinarith
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  set ρ := 64 * T ^ 2 / m ^ 2
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ : ρ ≤ 1 / 4 := by simp only [ρ]; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hVv' : V - v ≤ ρ * V := by
    rw [hVv]
    have hk1p : 0 < k1 * (m - k1) := lt_of_lt_of_le (by positivity) hK1
    calc σ2 * m * Dd ^ 2 / (k1 * (m - k1)) ≤ σ2 * m * T ^ 2 / (m ^ 2 / 8) := by
          apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hK1
      _ = ρ * (σ2 * m / 8) := by simp only [ρ]; field_simp; ring
      _ ≤ ρ * V := mul_le_mul_of_nonneg_left hV hρ0
  have hvV : v ≤ V := by
    have hk1p' : 0 < k1 * (m - k1) := lt_of_lt_of_le (by positivity) hK1
    have : 0 ≤ V - v := by rw [hVv]; positivity
    linarith
  have hsq : √(V / v) ≤ 1 + ρ := by
    rw [Real.sqrt_le_left (by linarith), div_le_iff₀ hv]
    have : V * (1 - ρ) ≤ v := by linarith
    nlinarith [mul_nonneg hρ0 hV0.le, mul_nonneg (mul_nonneg hρ0 hρ0) hV0.le]
  -- the exponent
  have hk1p : 0 < k1 * (m - k1) := lt_of_lt_of_le (by positivity) hK1
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hY1
  have hdiff : |ν - ν'| ≤ 8 * T * Y / m := by
    rw [hνν, abs_mul, abs_div, abs_mul, abs_of_pos hm0, abs_of_pos hk1p]
    calc |Dd| * m / (k1 * (m - k1)) * |a - k1 * s / m| ≤ T * m / (m ^ 2 / 8) * Y := by
          gcongr
      _ = 8 * T * Y / m := by field_simp
  have hexp : |ν - ν'| * |a - ν'| / V ≤ 64 * T * Y ^ 2 / (σ2 * m ^ 2) := by
    calc |ν - ν'| * |a - ν'| / V ≤ (8 * T * Y / m) * Y / (σ2 * m / 8) := by
          apply div_le_div₀ (by positivity) (mul_le_mul hdiff hY2 (abs_nonneg _) (by positivity))
            (by positivity) hV
      _ = 64 * T * Y ^ 2 / (σ2 * m ^ 2) := by field_simp; ring
  have hr := gd_ratio (ν := ν) (ν' := ν') hv hvV a
  calc gd ν v a ≤ √(V / v) * exp (|ν - ν'| * |a - ν'| / V) * gd ν' V a := hr
    _ ≤ (1 + ρ) * exp (64 * T * Y ^ 2 / (σ2 * m ^ 2)) * gd ν' V a := by
        gcongr
        exact gd_nonneg _ _ _

end ArcsAlgo.LLT
