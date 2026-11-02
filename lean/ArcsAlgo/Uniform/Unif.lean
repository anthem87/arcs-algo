module

public import ArcsAlgo.LocalLimit.LemmaB0
public import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false

/-!
# Uniform consequences of Lemma B0′ (paper §6.3)

* `CB_le`: the constant of Lemma B0′ is bounded uniformly, `C(k, M) ≤ 17` for `M, k ≥ 2`.
* `lawS_le_max`: `Pr(S_k = v) ≤ 13/(σ√k)` for `k ≥ 2`, uniformly in `M ≥ 2` and `v`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem sq_mul_exp_neg_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) : x ^ 2 * exp (-(c * x)) ≤ 2 / c ^ 2 := by
  have h := quadratic_le_exp_of_nonneg (mul_nonneg hc.le hx)
  have he : exp (-(c * x)) * exp (c * x) = 1 := by rw [← exp_add]; simp
  have hpos := exp_pos (c * x)
  rw [le_div_iff₀ (by positivity)]
  have : x ^ 2 * c ^ 2 ≤ 2 * exp (c * x) := by nlinarith [mul_nonneg hc.le hx]
  calc x ^ 2 * exp (-(c * x)) * c ^ 2 = (x ^ 2 * c ^ 2) * exp (-(c * x)) := by ring
    _ ≤ (2 * exp (c * x)) * exp (-(c * x)) := by gcongr
    _ = 2 := by rw [mul_assoc, mul_comm (exp _), he, mul_one]

theorem inv_sqrt_two_pow (n : ℕ) : (1 / √2) ^ n = exp (-(log 2 / 2 * n)) := by
  have : 1 / √2 = exp (-(log 2 / 2)) := by
    rw [exp_neg, ← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), exp_log (by positivity), one_div]
  rw [this, ← exp_nat_mul]; ring_nf

/-- **The constant of Lemma B0′ is bounded uniformly**: `C(k, M) ≤ 17` for `M, k ≥ 2`. -/
theorem CB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) : CB M k ≤ 17 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hsk : (k : ℝ) * √(k : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : √(k : ℝ) ≤ k := by
      have := Real.sqrt_le_sqrt (show (k : ℝ) ≤ k * k by nlinarith)
      rwa [Real.sqrt_mul_self hk0] at this
    nlinarith
  have hl2 : (0.69 : ℝ) < log 2 := by have := Real.log_two_gt_d9; linarith
  -- the q_M term
  have hq := qM_le hM
  have hq0 := (qM_pos hM).le
  have h1 : qM M ^ (k - 2) ≤ 2 * (1 / √2) ^ k := by
    have : (1 / √2 : ℝ) ^ k = (1 / √2) ^ (k - 2) * (1 / √2) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this, show ((1 : ℝ) / √2) ^ 2 = 1 / 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    have := pow_le_pow_left₀ hq0 hq (k - 2)
    linarith
  have hc1 : (k : ℝ) ^ 2 * (1 / √2) ^ k ≤ 2 / (log 2 / 2) ^ 2 := by
    rw [inv_sqrt_two_pow]; exact sq_mul_exp_neg_le (by positivity) hk0
  have hc1' : 2 / (log 2 / 2) ^ 2 ≤ 16.9 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hA : (k : ℝ) * √(k : ℝ) * (qM M ^ (k - 2) / √12) ≤ 9.8 := by
    have h12 : (3.46 : ℝ) ≤ √12 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hpos : 0 ≤ qM M ^ (k - 2) := pow_nonneg hq0 _
    calc (k : ℝ) * √(k : ℝ) * (qM M ^ (k - 2) / √12) ≤ (k : ℝ) ^ 2 * (2 * (1 / √2) ^ k) / 3.46 := by
          rw [mul_div_assoc']
          apply div_le_div₀ (by positivity) _ (by norm_num) h12
          exact mul_le_mul hsk h1 hpos (by positivity)
      _ ≤ 9.8 := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  -- the exponential term
  have hB : (k : ℝ) * √(k : ℝ) * ((0.41 / k + 0.11) * exp (-0.308 * k)) ≤ 6.7 := by
    have h2 : 0.41 / (k : ℝ) + 0.11 ≤ 0.315 := by
      rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]; nlinarith
    have h3 : (k : ℝ) ^ 2 * exp (-(0.308 * k)) ≤ 2 / 0.308 ^ 2 := sq_mul_exp_neg_le (by norm_num) hk0
    have he := (exp_pos (-0.308 * k)).le
    calc (k : ℝ) * √(k : ℝ) * ((0.41 / k + 0.11) * exp (-0.308 * k))
        ≤ (k : ℝ) ^ 2 * (0.315 * exp (-(0.308 * k))) := by
          rw [show -(0.308 * (k : ℝ)) = -0.308 * k by ring]
          apply mul_le_mul hsk (mul_le_mul_of_nonneg_right h2 he) (by positivity) (by positivity)
      _ = 0.315 * ((k : ℝ) ^ 2 * exp (-(0.308 * k))) := by ring
      _ ≤ 0.315 * (2 / 0.308 ^ 2) := by gcongr
      _ ≤ 6.7 := by norm_num
  have hC : 0.0599 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) ≤ 0.1 := by
    have : ((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1) ≤ 5 / 3 := by
      rw [div_le_iff₀ (by nlinarith)]; nlinarith
    linarith
  have hD : 0.34 / (k : ℝ) ≤ 0.17 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  unfold CB
  rw [mul_add]
  linarith

/-- `max_v Pr(S_k = v) ≤ 13/(σ√k)` for `k ≥ 2`, uniformly in `M ≥ 2` (from Lemma B0′). -/
theorem lawS_le_max {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (v : ℤ) :
    lawS M k v ≤ 13 / (√(sig2 M) * √(k : ℝ)) := by
  have hσ := sig2_pos hM
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsσ := Real.sqrt_pos.mpr hσ
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have h := lemmaB0'_gauss hM hk v
  have hg : gaussB M k v ≤ 1 / (√(sig2 M) * √(k : ℝ)) := by
    unfold gaussB
    have : √(2 * π * k * sig2 M) = √(2 * π) * (√(k : ℝ) * √(sig2 M)) := by
      rw [show 2 * π * k * sig2 M = (2 * π) * ((k : ℝ) * sig2 M) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity) (sig2 M)]
    have h2π : 1 ≤ √(2 * π) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith [Real.pi_gt_three]
    have he : Real.exp (-(zB M k v ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := sq_nonneg (zB M k v); linarith)
    rw [this]
    calc 1 / (√(2 * π) * (√(k : ℝ) * √(sig2 M))) * Real.exp (-(zB M k v ^ 2 / 2))
        ≤ 1 / (1 * (√(k : ℝ) * √(sig2 M))) * 1 := by
          gcongr
      _ = 1 / (√(sig2 M) * √(k : ℝ)) := by ring
  have hC : CB M k / (√(sig2 M) * (k * √(k : ℝ))) ≤ 12 / (√(sig2 M) * √(k : ℝ)) := by
    have hCB := CB_le hM hk
    calc CB M k / (√(sig2 M) * (k * √(k : ℝ))) ≤ 17 / (√(sig2 M) * (k * √(k : ℝ))) := by
          gcongr
      _ = (17 / k) / (√(sig2 M) * √(k : ℝ)) := by field_simp
      _ ≤ 12 / (√(sig2 M) * √(k : ℝ)) := by
          gcongr; rw [div_le_iff₀ (by linarith)]; linarith
  have := (abs_le.mp h).2
  have h13 : 1 / (√(sig2 M) * √(k : ℝ)) + 12 / (√(sig2 M) * √(k : ℝ)) =
      13 / (√(sig2 M) * √(k : ℝ)) := by ring
  linarith

end ArcsAlgo.LLT
