module

public import ArcsAlgo.SecondMoment.LemmaB
public import ArcsAlgo.LocalLimit.LemmaB0
public import ArcsAlgo.Uniform.Freeze
public import ArcsAlgo.Uniform.Binom
set_option autoImplicit false

/-!
# The Gaussian identities behind Lemma B(1) (paper §6.3)

* `gaussB_le`: `g_k(v) ≤ 1/(σ√k)`; `gaussB_mul`: `g_k(a) g_{m−k}(b)` is `gPair`.
* `binG_mul_gPair0` (completing the square): `b(x) g₀(x) = B₀ e^{−α(x − c)²}` with
  `α = 2Ew²/(mσ²)` and `c = m/2 + μu/(2Ew²)`.
* `main_term_eq`: `2^m B₀ √(π/α) = λ_m e^{−Q₁/2} g_m(s)`; this is where `c_M` of `λ_m` comes from.
-/

open Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem ew2_eq (M : ℕ) : ew2 M = sig2 M + muW M ^ 2 := by
  unfold ew2 sig2 muW; ring

theorem gaussB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (v : ℤ) :
    gaussB M k v ≤ 1 / (√(sig2 M) * √(k : ℝ)) := by
  have hσ := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold gaussB
  have : √(2 * π * k * sig2 M) = √(2 * π) * (√(k : ℝ) * √(sig2 M)) := by
    rw [show 2 * π * k * sig2 M = (2 * π) * ((k : ℝ) * sig2 M) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity) (sig2 M)]
  have h2π : 1 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith [Real.pi_gt_three]
  have he : exp (-(zB M k v ^ 2 / 2)) ≤ 1 := exp_le_one_iff.mpr (by
    have := sq_nonneg (zB M k v); linarith)
  have h1 : 0 < √(k : ℝ) * √(sig2 M) := by positivity
  rw [this]
  calc 1 / (√(2 * π) * (√(k : ℝ) * √(sig2 M))) * exp (-(zB M k v ^ 2 / 2))
      ≤ 1 / (1 * (√(k : ℝ) * √(sig2 M))) * 1 := by gcongr
    _ = 1 / (√(sig2 M) * √(k : ℝ)) := by ring

theorem gaussB_mul {M m k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (a b : ℤ) :
    gaussB M k a * gaussB M (m - k) b =
      gPair (sig2 M) m k (a - k * muW M) (b - ((m : ℝ) - k) * muW M) := by
  have hσ := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmk : (0 : ℝ) < (m : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hkm
    linarith
  have hc : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  unfold gaussB gPair zB tB
  rw [hc]
  have e1 : √(2 * π * k * sig2 M) * √(2 * π * ((m : ℝ) - k) * sig2 M) =
      2 * π * sig2 M * √(k * ((m : ℝ) - k)) := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * π * k * sig2 M * (2 * π * ((m : ℝ) - k) * sig2 M) =
        (2 * π * sig2 M) ^ 2 * (k * ((m : ℝ) - k)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsk : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hσ.le
  have hk2 : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  have hm2 : √((m : ℝ) - k) ^ 2 = (m : ℝ) - k := Real.sq_sqrt hmk.le
  rw [mul_mul_mul_comm, one_div_mul_one_div, e1, ← exp_add]
  congr 2
  rw [div_pow, div_pow, mul_pow, mul_pow, hsk, hk2, hm2]
  field_simp
  ring

/-- `α = 2Ew²/(mσ²)`. -/
noncomputable def alB (M m : ℕ) : ℝ := 2 * ew2 M / (m * sig2 M)

/-- The centre `m/2 + μu/(2Ew²)`. -/
noncomputable def cB (M m : ℕ) (u : ℤ) : ℝ := m / 2 + muW M * u / (2 * ew2 M)

/-- The constant `B₀ = √(2/(πm)) (πσ²m)⁻¹ e^{−t²/(2mσ²)} e^{−u²/(2m Ew²)}`. -/
noncomputable def B0c (M m : ℕ) (s u : ℤ) : ℝ :=
  √(2 / (π * m)) * (1 / (π * sig2 M * m)) * exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) *
    exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M)))

/-- **Completing the square**: `b(x)·g₀(x) = B₀ e^{−α(x − c)²}`. -/
theorem binG_mul_gPair0 {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) (s u : ℤ) (x : ℝ) :
    binG m x * gPair0 (sig2 M) m (((s : ℝ) + u) / 2 - x * muW M)
        (((s : ℝ) - u) / 2 - ((m : ℝ) - x) * muW M) =
      B0c M m s u * exp (-(alB M m * (x - cB M m u) ^ 2)) := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hew := ew2_eq M
  have hexp : -(2 * (x - m / 2) ^ 2 / m) + -(((((s : ℝ) + u) / 2 - x * muW M) ^ 2 +
      (((s : ℝ) - u) / 2 - ((m : ℝ) - x) * muW M) ^ 2) / (m * sig2 M)) =
      (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M)) + -((u : ℝ) ^ 2 / (2 * m * ew2 M))) +
        -(2 * ew2 M / (m * sig2 M) * (x - (m / 2 + muW M * u / (2 * ew2 M))) ^ 2) := by
    rw [hew]; field_simp; ring
  calc binG m x * gPair0 (sig2 M) m (((s : ℝ) + u) / 2 - x * muW M)
        (((s : ℝ) - u) / 2 - ((m : ℝ) - x) * muW M)
      = √(2 / (π * m)) * (1 / (π * sig2 M * m)) * exp (-(2 * (x - m / 2) ^ 2 / m) +
          -(((((s : ℝ) + u) / 2 - x * muW M) ^ 2 +
          (((s : ℝ) - u) / 2 - ((m : ℝ) - x) * muW M) ^ 2) / (m * sig2 M))) := by
        unfold binG gPair0; rw [exp_add]; ring
    _ = _ := by
        rw [hexp]; unfold B0c alB cB; rw [exp_add, exp_add]; ring

/-- **The main term is `λ_m e^{−Q₁/2} g_m(s)`**: `2^m B₀ √(π/α) = λ_m e^{−Q₁/2} g_m(s)`. -/
theorem main_term_eq {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) (s u : ℤ) :
    2 ^ m * B0c M m s u * √(π / alB M m) =
      lamM M m * exp (-(1 / 2) * smQ1 M m u) * gaussB M m s := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hπ := pi_pos
  -- the square roots
  have s1 : √(2 / (π * m)) * √(π / alB M m) = √(sig2 M) / √(ew2 M) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div hσ.le]
    congr 1; unfold alB; field_simp
  have s2 : (M : ℝ) * √(2 * π * m * cMB M) = √(2 * π) * √(ew2 M) * √(m : ℝ) := by
    have : (M : ℝ) ^ 2 * cMB M = ew2 M := by unfold cMB ew2; field_simp; ring
    have hcM : 0 < cMB M := by unfold cMB; positivity
    calc (M : ℝ) * √(2 * π * m * cMB M) = √((M : ℝ) ^ 2) * √(2 * π * m * cMB M) := by
          rw [Real.sqrt_sq hM0.le]
      _ = √((M : ℝ) ^ 2 * (2 * π * m * cMB M)) := (Real.sqrt_mul (by positivity) _).symm
      _ = √(2 * π * ew2 M * m) := by congr 1; rw [← this]; ring
      _ = √(2 * π) * √(ew2 M) * √(m : ℝ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have s3 : √(2 * π * m * sig2 M) = √(2 * π) * √(m : ℝ) * √(sig2 M) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hz : zB M m s ^ 2 / 2 = ((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M) := by
    unfold zB tB
    rw [div_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hm0.le]; field_simp
  have hq : (1 / 2) * smQ1 M m u = (u : ℝ) ^ 2 / (2 * m * ew2 M) := by
    unfold smQ1; field_simp
  have h2π : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hsσ : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hσ.le
  have hsm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  unfold lamM gaussB B0c
  rw [s2, s3, neg_mul, hq, hz]
  have hA : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
  have hB : 0 < √(ew2 M) := Real.sqrt_pos.mpr he
  have hC : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hD : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  calc 2 ^ m * (√(2 / (π * m)) * (1 / (π * sig2 M * m)) *
        exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) *
        exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M)))) * √(π / alB M m)
      = 2 ^ m * (√(2 / (π * m)) * √(π / alB M m)) * (1 / (π * sig2 M * m)) *
        exp (-(((s : ℝ) - m * muW M) ^ 2 / (2 * m * sig2 M))) *
        exp (-((u : ℝ) ^ 2 / (2 * m * ew2 M))) := by ring
    _ = _ := by
      rw [s1, pow_succ]
      field_simp
      have h2π' : √(π * 2) ^ 2 = π * 2 := Real.sq_sqrt (by positivity)
      simp only [h2π, h2π', hsσ, hsm]; ring

end ArcsAlgo.LLT
