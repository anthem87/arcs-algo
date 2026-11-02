module

public import ArcsAlgo.Uniform.G1
public import ArcsAlgo.Uniform.Unif
set_option autoImplicit false

/-!
# One typical term of the first moment (paper §6.3, Lemma B(1))

* `pp_gg`: `|p_k(a)p_{m−k}(b) − g_k(a)g_{m−k}(b)| ≤ 3808/(σ²m²)` for `m/4 ≤ k ≤ 3m/4`, by Lemma B0′.
* `gg_le`: `g_k(a) g_{m−k}(b) ≤ 4/(σ²m)`.
* `term_approx`: the term `C(m,k) p_k(a) p_{m−k}(s−a)` against `2^m B₀ e^{−α(k−c)²}`, combining
  Lemma B0′, the binomial (B0′ with `M = 2`) and the frozen variance. All constants are uniform
  in `M`.
-/

open Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- The product of the two local probabilities against the product of their Gaussians:
`|p_k(a) p_{m−k}(b) − g_k(a) g_{m−k}(b)| ≤ 3808/(σ²m²)` for `m/4 ≤ k ≤ 3m/4`, `k, m − k ≥ 2`. -/
theorem pp_gg {M m k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (hmk : k + 2 ≤ m) (h1 : m ≤ 4 * k)
    (h2 : 4 * k ≤ 3 * m) (a b : ℤ) :
    |lawS M k a * lawS M (m - k) b - gaussB M k a * gaussB M (m - k) b| ≤
      3808 / (sig2 M * (m : ℝ) ^ 2) := by
  have hσ := sig2_pos hM
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  have hmk' : (2 : ℝ) ≤ (m : ℝ) - k := by
    have : (k : ℝ) + 2 ≤ m := by exact_mod_cast hmk
    linarith
  have h1' : (m : ℝ) ≤ 4 * k := by exact_mod_cast h1
  have h2' : 4 * (k : ℝ) ≤ 3 * m := by exact_mod_cast h2
  have hm0 : (0 : ℝ) < m := by linarith
  have hk2 : 2 ≤ m - k := by omega
  set σ := √(sig2 M)
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hσ
  have hσσ : σ * σ = sig2 M := Real.mul_self_sqrt hσ.le
  set sk := √(k : ℝ)
  set sl := √((m : ℝ) - k)
  have hsk0 : 0 < sk := Real.sqrt_pos.mpr (by linarith)
  have hsl0 : 0 < sl := Real.sqrt_pos.mpr (by linarith)
  have hskk : sk * sk = k := Real.mul_self_sqrt (by linarith)
  have hsll : sl * sl = (m : ℝ) - k := Real.mul_self_sqrt (by linarith)
  -- the four ingredients
  have e1 := lemmaB0'_gauss hM hk a
  have e2 := lemmaB0'_gauss hM hk2 b
  rw [hc] at e2
  have c1 := CB_le hM hk
  have c2 := CB_le hM hk2
  have q2 := lawS_le_max hM hk2 b
  rw [hc] at q2
  have g1 := gaussB_le hM (by omega : 1 ≤ k) a
  have hp2 : 0 ≤ lawS M (m - k) b := by unfold lawS; positivity
  have hg1 : 0 ≤ gaussB M k a := by unfold gaussB; positivity
  have ee1 : |lawS M k a - gaussB M k a| ≤ 17 / (σ * (k * sk)) :=
    e1.trans (div_le_div_of_nonneg_right c1 (by positivity))
  have ee2 : |lawS M (m - k) b - gaussB M (m - k) b| ≤ 17 / (σ * (((m : ℝ) - k) * sl)) :=
    e2.trans (div_le_div_of_nonneg_right c2 (by positivity))
  have hsplit : lawS M k a * lawS M (m - k) b - gaussB M k a * gaussB M (m - k) b =
      (lawS M k a - gaussB M k a) * lawS M (m - k) b +
        gaussB M k a * (lawS M (m - k) b - gaussB M (m - k) b) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hp2, abs_of_nonneg hg1]
  have t1 : |lawS M k a - gaussB M k a| * lawS M (m - k) b ≤
      17 / (σ * (k * sk)) * (13 / (σ * sl)) :=
    mul_le_mul ee1 q2 hp2 (by positivity)
  have t2 : gaussB M k a * |lawS M (m - k) b - gaussB M (m - k) b| ≤
      1 / (σ * sk) * (17 / (σ * (((m : ℝ) - k) * sl))) :=
    mul_le_mul g1 ee2 (abs_nonneg _) (by positivity)
  have hkl' : (m : ℝ) / 4 ≤ sk * sl := by
    rw [← Real.sqrt_mul (by linarith)]
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hk4 : (m : ℝ) / 4 ≤ k := by linarith
  have hl4 : (m : ℝ) / 4 ≤ (m : ℝ) - k := by linarith
  have hd1 : sig2 M * ((m : ℝ) ^ 2 / 16) ≤ σ * (k * sk) * (σ * sl) := by
    rw [show σ * (k * sk) * (σ * sl) = (σ * σ) * (k * (sk * sl)) by ring, hσσ]
    apply mul_le_mul_of_nonneg_left _ hσ.le
    have := mul_le_mul hk4 hkl' (by positivity) (by linarith)
    linarith
  have hd2 : sig2 M * ((m : ℝ) ^ 2 / 16) ≤ σ * sk * (σ * (((m : ℝ) - k) * sl)) := by
    rw [show σ * sk * (σ * (((m : ℝ) - k) * sl)) = (σ * σ) * (((m : ℝ) - k) * (sk * sl)) by ring, hσσ]
    apply mul_le_mul_of_nonneg_left _ hσ.le
    have := mul_le_mul hl4 hkl' (by positivity) (by linarith)
    linarith
  have hpos : 0 < sig2 M * ((m : ℝ) ^ 2 / 16) := by positivity
  have b1 : 17 / (σ * (k * sk)) * (13 / (σ * sl)) ≤ 3536 / (sig2 M * (m : ℝ) ^ 2) := by
    rw [div_mul_div_comm]
    calc 17 * 13 / (σ * (k * sk) * (σ * sl)) ≤ 17 * 13 / (sig2 M * ((m : ℝ) ^ 2 / 16)) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hd1
      _ = 3536 / (sig2 M * (m : ℝ) ^ 2) := by field_simp; ring
  have b2 : 1 / (σ * sk) * (17 / (σ * (((m : ℝ) - k) * sl))) ≤ 272 / (sig2 M * (m : ℝ) ^ 2) := by
    rw [div_mul_div_comm]
    calc 1 * 17 / (σ * sk * (σ * (((m : ℝ) - k) * sl))) ≤ 1 * 17 / (sig2 M * ((m : ℝ) ^ 2 / 16)) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hd2
      _ = 272 / (sig2 M * (m : ℝ) ^ 2) := by field_simp; ring
  have : (3536 : ℝ) / (sig2 M * (m : ℝ) ^ 2) + 272 / (sig2 M * (m : ℝ) ^ 2) =
      3808 / (sig2 M * (m : ℝ) ^ 2) := by ring
  linarith

/-- `g_k(a) g_{m−k}(b) ≤ 4/(σ²m)` for `m/4 ≤ k ≤ 3m/4`. -/
theorem gg_le {M m k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (hmk : k + 1 ≤ m) (h1 : m ≤ 4 * k)
    (h2 : 4 * k ≤ 3 * m) (a b : ℤ) :
    gaussB M k a * gaussB M (m - k) b ≤ 4 / (sig2 M * m) := by
  have hσ := sig2_pos hM
  have hc : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  have h1' : (m : ℝ) ≤ 4 * k := by exact_mod_cast h1
  have h2' : 4 * (k : ℝ) ≤ 3 * m := by exact_mod_cast h2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by linarith
  have g1 := gaussB_le hM hk a
  have g2 := gaussB_le hM (by omega : 1 ≤ m - k) b
  rw [hc] at g2
  have hg2 : 0 ≤ gaussB M (m - k) b := by unfold gaussB; positivity
  have hσ0 := Real.sqrt_pos.mpr hσ
  have hkl : (m : ℝ) / 4 ≤ √(k : ℝ) * √((m : ℝ) - k) := by
    rw [← Real.sqrt_mul (by linarith)]
    apply Real.le_sqrt_of_sq_le; nlinarith
  calc gaussB M k a * gaussB M (m - k) b ≤ 1 / (√(sig2 M) * √(k : ℝ)) *
        (1 / (√(sig2 M) * √((m : ℝ) - k))) := mul_le_mul g1 g2 hg2 (by positivity)
    _ = 1 / (√(sig2 M) * √(sig2 M) * (√(k : ℝ) * √((m : ℝ) - k))) := by field_simp
    _ ≤ 1 / (sig2 M * ((m : ℝ) / 4)) := by
        rw [Real.mul_self_sqrt hσ.le]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hkl hσ.le)
    _ = 4 / (sig2 M * m) := by field_simp

/-- **One typical term of the first moment.** For `m/4 ≤ k ≤ 3m/4`, `k, m − k ≥ 2`, `2a = s + u`:
`|C(m,k) p_k(a) p_{m−k}(s−a) − 2^m B₀ e^{−α(k−c)²}| ≤
  C(m,k)·3808/(σ²m²) + 2^m·136/(σ²m²√m) + ρ_k 2^m B₀ e^{−α(k−c)²}`. -/
theorem term_approx {M m k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (hmk : k + 2 ≤ m) (h1 : m ≤ 4 * k)
    (h2 : 4 * k ≤ 3 * m) (s u a : ℤ) (ha : 2 * a = s + u) :
    |(m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a)) -
        2 ^ m * (B0c M m s u * exp (-(alB M m * ((k : ℝ) - cB M m u) ^ 2)))| ≤
      (m.choose k : ℝ) * (3808 / (sig2 M * (m : ℝ) ^ 2)) + 2 ^ m * (136 / (sig2 M * (m : ℝ) ^ 2 * √(m : ℝ))) +
      (8 * ((k : ℝ) - m / 2) ^ 2 / m ^ 2 + 4 * |(k : ℝ) - m / 2| *
          ((a - k * muW M) ^ 2 + ((s - a : ℤ) - ((m : ℝ) - k) * muW M) ^ 2) / (sig2 M * m ^ 2)) *
        exp (4 * |(k : ℝ) - m / 2| *
          ((a - k * muW M) ^ 2 + ((s - a : ℤ) - ((m : ℝ) - k) * muW M) ^ 2) / (sig2 M * m ^ 2)) *
        (2 ^ m * (B0c M m s u * exp (-(alB M m * ((k : ℝ) - cB M m u) ^ 2)))) := by
  have hσ := sig2_pos hM
  have hm2 : 2 ≤ m := by omega
  have h1' : (m : ℝ) ≤ 4 * k := by exact_mod_cast h1
  have h2' : 4 * (k : ℝ) ≤ 3 * m := by exact_mod_cast h2
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  have haR : (a : ℝ) = ((s : ℝ) + u) / 2 := by
    have : (2 : ℝ) * a = s + u := by exact_mod_cast ha
    linarith
  have hsaR : ((s - a : ℤ) : ℝ) = ((s : ℝ) - u) / 2 := by push_cast; linarith
  have hG : gaussB M k a * gaussB M (m - k) (s - a) = gPair (sig2 M) m k ((a : ℝ) - k * muW M)
      (((s - a : ℤ) : ℝ) - ((m : ℝ) - k) * muW M) :=
    gaussB_mul (m := m) (k := k) hM (by omega) (by omega) a (s - a)
  have hbG₀ : binG m k * gPair0 (sig2 M) m ((a : ℝ) - k * muW M)
      (((s - a : ℤ) : ℝ) - ((m : ℝ) - k) * muW M) =
      B0c M m s u * exp (-(alB M m * ((k : ℝ) - cB M m u) ^ 2)) := by
    rw [haR, hsaR]; exact binG_mul_gPair0 hM (by omega) s u k
  rw [← hbG₀]
  have hXG := pp_gg hM hk hmk h1 h2 a (s - a)
  have hGle := gg_le hM (by omega) (by omega) h1 h2 a (s - a)
  have hfr := gPair_freeze (A₁ := (a : ℝ) - k * muW M)
    (A₂ := ((s - a : ℤ) : ℝ) - ((m : ℝ) - k) * muW M) hσ
    (by linarith : (m : ℝ) / 4 ≤ k) (by linarith) hm0
  rw [← hG] at hfr
  have hbin := binom_gauss hm2 k
  have hG0 : 0 ≤ gaussB M k a * gaussB M (m - k) (s - a) := by unfold gaussB; positivity
  generalize lawS M k a * lawS M (m - k) (s - a) = X at hXG ⊢
  generalize gaussB M k a * gaussB M (m - k) (s - a) = G at hXG hGle hfr hG0 ⊢
  generalize gPair0 (sig2 M) m ((a : ℝ) - k * muW M)
    (((s - a : ℤ) : ℝ) - ((m : ℝ) - k) * muW M) = G₀ at hfr ⊢
  generalize ((a : ℝ) - k * muW M) ^ 2 + (((s - a : ℤ) : ℝ) - ((m : ℝ) - k) * muW M) ^ 2 = Asq
    at hfr ⊢
  have hb0 : 0 ≤ binG m k := by unfold binG; positivity
  generalize binG m k = b at hbin hb0 ⊢
  have hC0 : (0 : ℝ) ≤ (m.choose k : ℝ) := by positivity
  generalize (m.choose k : ℝ) = C at hbin hC0 ⊢
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hsplit : C * X - 2 ^ m * (b * G₀) = C * (X - G) + 2 ^ m * (C / 2 ^ m - b) * G +
      2 ^ m * b * (G - G₀) := by field_simp; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg hC0]; exact mul_le_mul_of_nonneg_left hXG hC0
  · rw [abs_mul, abs_mul, abs_of_pos h2m, abs_of_nonneg hG0]
    calc 2 ^ m * |C / 2 ^ m - b| * G ≤ 2 ^ m * (34 / (m * √(m : ℝ))) * (4 / (sig2 M * m)) := by
          gcongr
      _ = 2 ^ m * (136 / (sig2 M * (m : ℝ) ^ 2 * √(m : ℝ))) := by
          have : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
          field_simp; ring
  · rw [abs_mul, abs_mul, abs_of_pos h2m, abs_of_nonneg hb0]
    calc 2 ^ m * b * |G - G₀| ≤ 2 ^ m * b * ((8 * ((k : ℝ) - m / 2) ^ 2 / m ^ 2 +
          4 * |(k : ℝ) - m / 2| * Asq / (sig2 M * m ^ 2)) *
          exp (4 * |(k : ℝ) - m / 2| * Asq / (sig2 M * m ^ 2)) * G₀) := by
          gcongr
      _ = _ := by ring
end ArcsAlgo.LLT
