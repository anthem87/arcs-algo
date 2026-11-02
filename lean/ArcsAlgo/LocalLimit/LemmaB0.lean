module

public import ArcsAlgo.LocalLimit.Assembly
set_option autoImplicit false

/-!
# Lemma B0′: a local limit theorem uniform in the size of the weights (paper §6.2)

`lemmaB0'`: for independent uniform weights in `{1, …, M}`, `M ≥ 2`, and `k ≥ 2`,
`|Pr(S_k = v) − g_k(v)(1 + κ₄He₄(z)/(24σ⁴k))|
  ≤ 0.34/(σk^{5/2}) + σ⁻¹(q_M^{k−2}/√12 + (0.41/k + 0.11)e^{−0.308k})`.

`lemmaB0'_gauss`: `|Pr(S_k = v) − g_k(v)| ≤ C(k, M)/(σk^{3/2})` with
`C(k, M) = 0.0599(M² + 1)/(M² − 1) + 0.34/k + k^{3/2}(q_M^{k−2}/√12 + (0.41/k + 0.11)e^{−0.308k})`,
using `|He₄(z)|e^{−z²/2} ≤ 3` (`abs_He4_mul_exp_le`).

The proof follows the paper. Fourier inversion (`lawS_eq_integral_fC`) splits into three ranges:
`|θ| ≤ π/M` (`norm_main_le`, giving `0.146 + 0.19 ≤ 0.34`), `π/M ≤ |θ| ≤ π` (`norm_mid_le`) and
the Gaussian tails (`norm_tails_le`). The Gaussian main term and the Edgeworth term are exact
Fourier integrals (`edgeB_eq`).
-/

open Real Complex MeasureTheory Set

@[expose] public section

namespace ArcsAlgo.LLT

/-- `t = v − kμ`. -/
noncomputable def tB (M k : ℕ) (v : ℤ) : ℝ := (v : ℝ) - k * muW M

/-- `z = (v − kμ)/(σ√k)`. -/
noncomputable def zB (M k : ℕ) (v : ℤ) : ℝ := tB M k v / (√(sig2 M) * √(k : ℝ))

/-- The Hermite polynomial `He₄(z) = z⁴ − 6z² + 3`. -/
def He4 (z : ℝ) : ℝ := z ^ 4 - 6 * z ^ 2 + 3

/-- `g_k(v) = (2πkσ²)^{−1/2} e^{−z²/2}`. -/
noncomputable def gaussB (M k : ℕ) (v : ℤ) : ℝ :=
  1 / √(2 * π * k * sig2 M) * Real.exp (-(zB M k v ^ 2 / 2))

/-- The Edgeworth approximation `g_k(v)(1 + κ₄He₄(z)/(24σ⁴k))`. -/
noncomputable def edgeB (M k : ℕ) (v : ℤ) : ℝ :=
  gaussB M k v * (1 + kap4 M * He4 (zB M k v) / (24 * sig2 M ^ 2 * k))

lemma edgeB_real {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (v : ℤ) :
    edgeB M k v = 1 / (2 * π) * (√(π / (k * sig2 M / 2)) *
      Real.exp (-(tB M k v) ^ 2 / (4 * (k * sig2 M / 2))) *
      (1 + k * kap4 M / 24 * (3 / (4 * (k * sig2 M / 2) ^ 2) -
        3 * tB M k v ^ 2 / (4 * (k * sig2 M / 2) ^ 3) + tB M k v ^ 4 / (16 * (k * sig2 M / 2) ^ 4)))) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hz2 : zB M k v ^ 2 = tB M k v ^ 2 / (sig2 M * k) := by
    rw [zB, div_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hk0.le]
  have hz4 : zB M k v ^ 4 = (tB M k v ^ 2 / (sig2 M * k)) ^ 2 := by rw [← hz2]; ring
  have hsq : √(π / (k * sig2 M / 2)) = √(2 * π) / (√k * √(sig2 M)) := by
    rw [show π / (k * sig2 M / 2) = 2 * π / (k * sig2 M) by field_simp,
      Real.sqrt_div (by positivity), Real.sqrt_mul hk0.le]
  have hsq2 : √(2 * π * k * sig2 M) = √(2 * π) * √k * √(sig2 M) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have h2π : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hr : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  have hσ : 0 < √(sig2 M) := Real.sqrt_pos.mpr hs
  have h2p : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  rw [edgeB, gaussB, He4, hz4, hz2, hsq, hsq2]
  have he : Real.exp (-(tB M k v ^ 2 / (sig2 M * k) / 2)) =
      Real.exp (-(tB M k v) ^ 2 / (4 * (k * sig2 M / 2))) := by
    congr 1; field_simp; ring
  rw [he]
  field_simp
  rw [h2π]
  ring

lemma edgeB_eq {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (v : ℤ) :
    ((edgeB M k v : ℝ) : ℂ) = 1 / (2 * π) * (G (k * sig2 M / 2) (tB M k v) 0 +
      ((k * kap4 M / 24 : ℝ) : ℂ) * G (k * sig2 M / 2) (tB M k v) 4) := by
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) * sig2 M / 2 := by positivity
  rw [G_four ha, G_zero ha, edgeB_real hM hk]
  have hP : ((π / (k * sig2 M / 2) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      cexp (-(tB M k v : ℂ) ^ 2 / (4 * ((k * sig2 M / 2 : ℝ) : ℂ))) =
      ((√(π / (k * sig2 M / 2)) * Real.exp (-(tB M k v) ^ 2 / (4 * (k * sig2 M / 2))) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_exp]
    push_cast; ring_nf
  rw [hP]
  generalize hP' : √(π / (k * sig2 M / 2)) * Real.exp (-(tB M k v) ^ 2 / (4 * (k * sig2 M / 2))) = P
  generalize tB M k v = t
  generalize (k : ℝ) * sig2 M / 2 = a
  generalize (k : ℝ) * kap4 M / 24 = B
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **Lemma B0′** (paper §6.2). Let `w₁, w₂, …` be independent and uniform in `{1, …, M}`,
`M ≥ 2`, with `μ = (M+1)/2`, `σ² = (M²−1)/12`, `κ₄ = −(M⁴−1)/120`, `z = (v − kμ)/(σ√k)`,
`g_k(v) = (2πkσ²)^{−1/2}e^{−z²/2}` and `q_M = 1/(M sin(π/(2M)))`. For `k ≥ 2` and every `v`,
`|Pr(S_k = v) − g_k(v)(1 + κ₄He₄(z)/(24σ⁴k))|
  ≤ 0.34/(σk^{5/2}) + σ⁻¹(q_M^{k−2}/√12 + (0.41/k + 0.11)e^{−0.308k})`,
where `k^{5/2}` is written `k²√k`. -/
theorem lemmaB0' {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (v : ℤ) :
    |lawS M k v - edgeB M k v| ≤ 0.34 / (√(sig2 M) * k ^ 2 * √(k : ℝ)) +
      (qM M ^ (k - 2) / √12 + (0.41 / k + 0.11) * Real.exp (-0.308 * k)) / √(sig2 M) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set t := tB M k v with htdef
  set a := (k : ℝ) * sig2 M / 2 with hadef
  set B := (k : ℝ) * kap4 M / 24 with hBdef
  set θ0 := π / M with hθ0def
  have ha : 0 < a := by positivity
  have hθ0 : 0 < θ0 := by positivity
  have hθπ : θ0 ≤ π := div_le_self hπ.le (by exact_mod_cast (by omega : 1 ≤ M))
  have hlaw : ((lawS M k v : ℝ) : ℂ) = 1 / (2 * π) * ∫ θ in (-π)..π, PhiB M k t θ := by
    have h := lawS_eq_integral_fC (M := M) (by omega) k v
    have hrw : (fun θ : ℝ => ((fC M θ ^ k : ℝ) : ℂ) * cexp (-(I * ((v : ℝ) - k * muW M) * θ))) =
        PhiB M k t := by
      funext θ; simp only [PhiB, eph, htdef, tB]; push_cast; ring
    rw [hrw] at h; exact h
  have hedge : ((edgeB M k v : ℝ) : ℂ) = 1 / (2 * π) * ∫ θ, PsiB a B t θ := by
    rw [integral_PsiB ha, edgeB_eq hM hk1]
  have hΦ : ∀ x y : ℝ, IntervalIntegrable (PhiB M k t) volume x y :=
    fun x y => (continuous_PhiB M k t).intervalIntegrable x y
  have hΨ := integrable_PsiB ha B t
  have hI : ∫ θ in (-π)..π, PhiB M k t θ = (∫ θ in (-π)..(-θ0), PhiB M k t θ) +
      (∫ θ in (-θ0)..θ0, PhiB M k t θ) + ∫ θ in θ0..π, PhiB M k t θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hΦ _ _) (hΦ _ _),
      intervalIntegral.integral_add_adjacent_intervals (hΦ _ _) (hΦ _ _)]
  have hJ : ∫ θ, PsiB a B t θ = (∫ θ in Iic (-θ0), PsiB a B t θ) +
      ((∫ θ in (-θ0)..θ0, PsiB a B t θ) + ∫ θ in Ioi θ0, PsiB a B t θ) := by
    rw [intervalIntegral.integral_interval_add_Ioi hΨ.integrableOn hΨ.integrableOn,
      intervalIntegral.integral_Iic_add_Ioi hΨ.integrableOn hΨ.integrableOn]
  have hsub : (∫ θ in (-θ0)..θ0, PhiB M k t θ) - ∫ θ in (-θ0)..θ0, PsiB a B t θ =
      ∫ θ in (-θ0)..θ0, (PhiB M k t θ - PsiB a B t θ) :=
    (intervalIntegral.integral_sub (hΦ _ _) hΨ.intervalIntegrable).symm
  set X := (∫ θ in (-θ0)..θ0, (PhiB M k t θ - PsiB a B t θ)) +
    (∫ θ in (-π)..(-θ0), PhiB M k t θ) + (∫ θ in θ0..π, PhiB M k t θ) -
    (∫ θ in Iic (-θ0), PsiB a B t θ) - ∫ θ in Ioi θ0, PsiB a B t θ with hX
  have hdiff : ((lawS M k v - edgeB M k v : ℝ) : ℂ) = 1 / (2 * π) * X := by
    rw [Complex.ofReal_sub, hlaw, hedge, hI, hJ, hX, ← hsub]; ring
  have hmain := norm_main_le hM hk1 t
  have hmid := norm_mid_le hM hk t
  obtain ⟨hT1, hT2⟩ := norm_tails_le ha hθ0 B t
  have hXle : ‖X‖ ≤ ((k * kap4 M / 24) ^ 2 / 2 * mom 8 a +
        65 * cL * k * sig2 M ^ 3 * mom 6 (k * sig2 M * (1 / 2 - deltaL))) +
      qM M ^ (k - 2) * (2 * π / M) +
      2 * (Real.exp (-a * θ0 ^ 2) / (2 * a * θ0) + |B| *
        (Real.exp (-a * θ0 ^ 2) * (θ0 ^ 3 / (2 * a) + 3 * θ0 / (4 * a ^ 2) +
          3 / (8 * a ^ 3 * θ0)))) := by
    rw [hX]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _).trans ?_
    linarith
  have habs : |lawS M k v - edgeB M k v| = 1 / (2 * π) * ‖X‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, norm_mul]
    congr 1
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg hπ.le]
  rw [habs]
  have t1 := term_one_le hM hk1
  have t2 := term_two_le hM hk1
  have t3 := term_mid_le hM k
  have t4 := term_tail_le hM hk
  have h2π : 0 ≤ 1 / (2 * π) := by positivity
  have hfin := mul_le_mul_of_nonneg_left hXle h2π
  have hσ : 0 < √(sig2 M) := Real.sqrt_pos.mpr hs
  have hr : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  have e1 : 0.146 / (√(sig2 M) * k ^ 2 * √(k : ℝ)) + 0.19 / (√(sig2 M) * k ^ 2 * √(k : ℝ)) ≤
      0.34 / (√(sig2 M) * k ^ 2 * √(k : ℝ)) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have e2 : qM M ^ (k - 2) / (√12 * √(sig2 M)) = qM M ^ (k - 2) / √12 / √(sig2 M) := by
    rw [div_div]
  rw [add_div, ← e2]
  simp only [hadef, hBdef, hθ0def] at hfin t4 ⊢
  linarith [hfin, t1, t2, t3, t4, e1]

/-- `|He₄(z)| e^{−z²/2} ≤ 3`, with equality at `z = 0`. -/
lemma abs_He4_mul_exp_le (z : ℝ) : |He4 z| * Real.exp (-(z ^ 2 / 2)) ≤ 3 := by
  set u := z ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg z
  have hH : He4 z = u ^ 2 - 6 * u + 3 := by rw [He4, hu]; ring
  have hE := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ u / 2) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hE
  norm_num at hE
  have hpos := Real.exp_pos (u / 2)
  have hprod : Real.exp (-(z ^ 2 / 2)) * Real.exp (u / 2) = 1 := by
    rw [← Real.exp_add, hu]; simp
  have hle : |He4 z| ≤ 3 * Real.exp (u / 2) := by
    rw [hH, abs_le]; constructor
    · nlinarith [sq_nonneg (u - 9 / 4)]
    · nlinarith [sq_nonneg (u - 10), mul_nonneg hu0 (sq_nonneg (u - 10))]
  have hq := Real.exp_pos (-(z ^ 2 / 2))
  calc |He4 z| * Real.exp (-(z ^ 2 / 2)) ≤ 3 * Real.exp (u / 2) * Real.exp (-(z ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hle hq.le
    _ = 3 := by rw [mul_assoc, mul_comm (Real.exp _), hprod, mul_one]

/-- The constant `C(k, M)` of Lemma B0′. -/
noncomputable def CB (M k : ℕ) : ℝ :=
  0.0599 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) + 0.34 / k +
    k * √(k : ℝ) * (qM M ^ (k - 2) / √12 + (0.41 / k + 0.11) * Real.exp (-0.308 * k))

/-- **Lemma B0′, second part**: `|Pr(S_k = v) − g_k(v)| ≤ C(k, M)/(σk^{3/2})`
(`k^{3/2}` written `k√k`). The constant `0.0599 = (1.2/24)·3/√(2π)` is the first Edgeworth term
at `z = 0`. -/
theorem lemmaB0'_gauss {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (v : ℤ) :
    |lawS M k v - gaussB M k v| ≤ CB M k / (√(sig2 M) * (k * √(k : ℝ))) := by
  have hπ := Real.pi_pos
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hσ : 0 < √(sig2 M) := Real.sqrt_pos.mpr hs
  have hr : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
  have hrk : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  have hσs : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hs.le
  have hmain := lemmaB0' hM hk v
  -- the Edgeworth term
  have hed : |edgeB M k v - gaussB M k v| ≤
      0.0599 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) / (√(sig2 M) * (k * √(k : ℝ))) := by
    have e : edgeB M k v - gaussB M k v = 1 / √(2 * π * k * sig2 M) *
        (Real.exp (-(zB M k v ^ 2 / 2)) * He4 (zB M k v)) * (kap4 M / (24 * sig2 M ^ 2 * k)) := by
      rw [edgeB, gaussB]; ring
    have hsq2 : √(2 * π * k * sig2 M) = √(2 * π) * √k * √(sig2 M) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have h2p : 2.505 ≤ √(2 * π) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d4]
    have hK : |kap4 M| / sig2 M ^ 2 = 1.2 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) := by
      rw [abs_of_nonpos (kap4_nonpos hM)]
      have h1 : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      unfold kap4 sig2; field_simp; ring
    have hHe := abs_He4_mul_exp_le (zB M k v)
    rw [e, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / √(2 * π * k * sig2 M)),
      abs_mul, abs_of_pos (Real.exp_pos _), mul_comm (Real.exp _), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 24 * sig2 M ^ 2 * k), hsq2]
    have hR : 0 ≤ ((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1) := by
      apply div_nonneg (by positivity); nlinarith
    have hK' : |kap4 M| / (24 * sig2 M ^ 2 * k) =
        1.2 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) / (24 * k) := by
      rw [← hK]; field_simp
    rw [hK']
    set R := ((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)
    calc 1 / (√(2 * π) * √k * √(sig2 M)) * (|He4 (zB M k v)| * Real.exp (-(zB M k v ^ 2 / 2))) *
          (1.2 * R / (24 * k))
        ≤ 1 / (√(2 * π) * √k * √(sig2 M)) * 3 * (1.2 * R / (24 * k)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hHe (by positivity)
      _ = (0.15 / √(2 * π)) * R / (√(sig2 M) * (k * √(k : ℝ))) := by field_simp; ring
      _ ≤ 0.0599 * R / (√(sig2 M) * (k * √(k : ℝ))) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hR
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have htri : |lawS M k v - gaussB M k v| ≤
      |lawS M k v - edgeB M k v| + |edgeB M k v - gaussB M k v| := abs_sub_le _ _ _
  have hP : 0 < √(sig2 M) * (k * √(k : ℝ)) := by positivity
  have e1 : 0.34 / (√(sig2 M) * k ^ 2 * √(k : ℝ)) = (0.34 / k) / (√(sig2 M) * (k * √(k : ℝ))) := by
    field_simp
  have e2 : (qM M ^ (k - 2) / √12 + (0.41 / k + 0.11) * Real.exp (-0.308 * k)) / √(sig2 M) =
      (k * √(k : ℝ) * (qM M ^ (k - 2) / √12 + (0.41 / k + 0.11) * Real.exp (-0.308 * k))) /
        (√(sig2 M) * (k * √(k : ℝ))) := by
    field_simp
  rw [e1, e2] at hmain
  have : CB M k / (√(sig2 M) * (k * √(k : ℝ))) =
      0.0599 * (((M : ℝ) ^ 2 + 1) / ((M : ℝ) ^ 2 - 1)) / (√(sig2 M) * (k * √(k : ℝ))) +
      (0.34 / k) / (√(sig2 M) * (k * √(k : ℝ))) +
      (k * √(k : ℝ) * (qM M ^ (k - 2) / √12 + (0.41 / k + 0.11) * Real.exp (-0.308 * k))) /
        (√(sig2 M) * (k * √(k : ℝ))) := by
    rw [CB, add_div, add_div]
  rw [this]
  linarith

end ArcsAlgo.LLT
