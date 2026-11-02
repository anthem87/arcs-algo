module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false

/-!
# Theorem E(2), the core: the Gaussian integrals (paper §3.5, Proposition C)

* `Mk k ξ = ∫ v^k e^{−v²/2 − iξv} dv`: `M₁ = −iξM₀`, `M_{n+2} = −iξM_{n+1} + (n+1)M_n` (integrate a
  derivative), so `i^k M_k = He_k(ξ) M₀` for `k ≤ 6` (`mk_He`), and `M₀ = √(2π)e^{−ξ²/2}` (`Mk_zero`).
* `gauss_He`: `(2π)^{−1} ∫ (iσ)^k e^{iκ₁σ − s²σ²/2 − iTσ} dσ = He_k(z)φ(z)/s^{k+1}`, `z = (T − κ₁)/s`.
* `Am k = ∫ |v|^k e^{−v²/2}` and `absmom_scale`: `∫ |σ|^k e^{−s²σ²/2} = A_k/s^{k+1}`.

No hypothesis.
-/

open Complex MeasureTheory Real

@[expose] public section

namespace ArcsAlgo.Edge

/-- `g_ξ(v) = e^{−v²/2 − iξv}`. -/
noncomputable def gE (ξ v : ℝ) : ℂ := Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v)

/-- `M_k(ξ) = ∫ v^k e^{−v²/2 − iξv} dv`. -/
noncomputable def Mk (k : ℕ) (ξ : ℝ) : ℂ := ∫ v : ℝ, (v : ℂ) ^ k * gE ξ v

theorem norm_gE (ξ v : ℝ) : ‖gE ξ v‖ = Real.exp (-v ^ 2 / 2) := by
  unfold gE; rw [Complex.norm_exp]; congr 1
  simp [Complex.sub_re, Complex.mul_re, sq]

theorem integrable_pow_gauss (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun v : ℝ => |v| ^ k * Real.exp (-b * v ^ 2) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ)) (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

theorem integrable_mom (k : ℕ) (ξ : ℝ) : Integrable fun v : ℝ => (v : ℂ) ^ k * gE ξ v := by
  refine Integrable.mono' (integrable_pow_gauss k (by norm_num : (0 : ℝ) < 1 / 2)) ?_ ?_
  · unfold gE; fun_prop
  · refine Filter.Eventually.of_forall fun v => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_gE]
    rw [show -v ^ 2 / 2 = -(1 / 2) * v ^ 2 by ring]

theorem hasDerivAt_ofReal (v : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := by
  simpa using (hasDerivAt_id v).ofReal_comp

theorem hasDerivAt_gE (ξ v : ℝ) : HasDerivAt (gE ξ) ((-(v : ℂ) - I * ξ) * gE ξ v) v := by
  have hv := hasDerivAt_ofReal v
  have hq : HasDerivAt (fun x : ℝ => -(x : ℂ) ^ 2 / 2 - I * ξ * x) (-(v : ℂ) - I * ξ) v := by
    have := ((hv.pow 2).neg.div_const 2).sub (hv.const_mul (I * ξ))
    convert this using 1; simp; ring
  have := hq.cexp
  unfold gE; convert this using 1; ring

/-- `M_1 = −iξ M_0` and `M_{n+2} = −iξ M_{n+1} + (n+1) M_n` (integrate the derivative of `v^k g`). -/
theorem Mk_one (ξ : ℝ) : Mk 1 ξ = -I * ξ * Mk 0 ξ := by
  have hd := fun v => hasDerivAt_gE ξ v
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ (by simpa using integrable_mom 0 ξ)
  · have e : (fun v : ℝ => (-(v : ℂ) - I * ξ) * gE ξ v) =
        fun v : ℝ => -((v : ℂ) ^ 1 * gE ξ v) + (-I * ξ) * ((v : ℂ) ^ 0 * gE ξ v) := by ext v; ring
    have hA : Integrable (fun v : ℝ => -((v : ℂ) ^ 1 * gE ξ v)) := (integrable_mom 1 ξ).neg
    have hB : Integrable (fun v : ℝ => (-I * ξ) * ((v : ℂ) ^ 0 * gE ξ v)) := (integrable_mom 0 ξ).const_mul _
    rw [e, integral_add hA hB, integral_neg, integral_const_mul] at h0
    unfold Mk; linear_combination -h0
  · have e : (fun v : ℝ => (-(v : ℂ) - I * ξ) * gE ξ v) =
        fun v : ℝ => -((v : ℂ) ^ 1 * gE ξ v) + (-I * ξ) * ((v : ℂ) ^ 0 * gE ξ v) := by ext v; ring
    rw [e]; exact (integrable_mom 1 ξ).neg.add ((integrable_mom 0 ξ).const_mul _)

theorem Mk_succ_succ (n : ℕ) (ξ : ℝ) : Mk (n + 2) ξ = -I * ξ * Mk (n + 1) ξ + (n + 1) * Mk n ξ := by
  have hd : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) ^ (n + 1) * gE ξ v)
      ((n + 1) * ((v : ℂ) ^ n * gE ξ v) - (v : ℂ) ^ (n + 2) * gE ξ v + (-I * ξ) * ((v : ℂ) ^ (n + 1) * gE ξ v)) v := by
    intro v
    have h1 := ((hasDerivAt_ofReal v).pow (n + 1)).mul (hasDerivAt_gE ξ v)
    convert h1 using 1
    simp; ring
  have hI : Integrable fun v : ℝ =>
      (n + 1) * ((v : ℂ) ^ n * gE ξ v) - (v : ℂ) ^ (n + 2) * gE ξ v + (-I * ξ) * ((v : ℂ) ^ (n + 1) * gE ξ v) :=
    (((integrable_mom n ξ).const_mul _).sub (integrable_mom (n + 2) ξ)).add ((integrable_mom (n + 1) ξ).const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hI (integrable_mom (n + 1) ξ)
  have hA : Integrable (fun v : ℝ => (n + 1) * ((v : ℂ) ^ n * gE ξ v) - (v : ℂ) ^ (n + 2) * gE ξ v) :=
    ((integrable_mom n ξ).const_mul _).sub (integrable_mom (n + 2) ξ)
  have hB : Integrable (fun v : ℝ => (-I * ξ) * ((v : ℂ) ^ (n + 1) * gE ξ v)) :=
    (integrable_mom (n + 1) ξ).const_mul _
  have hA1 : Integrable (fun v : ℝ => (n + 1) * ((v : ℂ) ^ n * gE ξ v)) := (integrable_mom n ξ).const_mul _
  rw [integral_add hA hB, integral_sub hA1 (integrable_mom (n + 2) ξ),
    integral_const_mul, integral_const_mul] at h0
  unfold Mk; linear_combination -h0

/-- `m_k = i^k M_k` satisfies the Hermite recursion `m_{n+2} = ξ m_{n+1} − (n+1) m_n`. -/
theorem mk_rec (n : ℕ) (ξ : ℝ) :
    I ^ (n + 2) * Mk (n + 2) ξ = ξ * (I ^ (n + 1) * Mk (n + 1) ξ) - (n + 1) * (I ^ n * Mk n ξ) := by
  rw [Mk_succ_succ]
  have e1 : I ^ (n + 2) = -I ^ n := by rw [pow_add, I_sq]; ring
  have e2 : I ^ (n + 2) * (-I) = I ^ (n + 1) := by
    rw [show n + 2 = n + 1 + 1 from rfl, pow_succ]; linear_combination (-(I ^ (n + 1))) * I_mul_I
  linear_combination (ξ : ℂ) * Mk (n + 1) ξ * e2 + (n + 1) * Mk n ξ * e1

/-- The probabilists' Hermite polynomials `He₀, …, He₆`. -/
noncomputable def He : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun z => z
  | 2 => fun z => z ^ 2 - 1
  | 3 => fun z => z ^ 3 - 3 * z
  | 4 => fun z => z ^ 4 - 6 * z ^ 2 + 3
  | 5 => fun z => z ^ 5 - 10 * z ^ 3 + 15 * z
  | 6 => fun z => z ^ 6 - 15 * z ^ 4 + 45 * z ^ 2 - 15
  | _ => fun _ => 0

theorem mk_He (ξ : ℝ) : ∀ k ≤ 6, I ^ k * Mk k ξ = (He k ξ : ℂ) * Mk 0 ξ := by
  have h1 : I ^ 1 * Mk 1 ξ = (He 1 ξ : ℂ) * Mk 0 ξ := by
    rw [Mk_one]; simp [He]; ring_nf; rw [I_sq]; ring
  have h0 : I ^ 0 * Mk 0 ξ = (He 0 ξ : ℂ) * Mk 0 ξ := by simp [He]
  have h2 : I ^ 2 * Mk 2 ξ = (He 2 ξ : ℂ) * Mk 0 ξ := by
    rw [mk_rec 0, h1, h0]; simp [He]; ring
  have h3 : I ^ 3 * Mk 3 ξ = (He 3 ξ : ℂ) * Mk 0 ξ := by
    rw [mk_rec 1, h2, h1]; simp [He]; ring
  have h4 : I ^ 4 * Mk 4 ξ = (He 4 ξ : ℂ) * Mk 0 ξ := by
    rw [mk_rec 2, h3, h2]; simp [He]; ring
  have h5 : I ^ 5 * Mk 5 ξ = (He 5 ξ : ℂ) * Mk 0 ξ := by
    rw [mk_rec 3, h4, h3]; simp [He]; ring
  have h6 : I ^ 6 * Mk 6 ξ = (He 6 ξ : ℂ) * Mk 0 ξ := by
    rw [mk_rec 4, h5, h4]; simp [He]; ring
  intro k hk
  interval_cases k <;> assumption

/-- `M₀(ξ) = √(2π) e^{−ξ²/2}`. -/
theorem Mk_zero (ξ : ℝ) : Mk 0 ξ = ((Real.sqrt (2 * π) * Real.exp (-ξ ^ 2 / 2) : ℝ) : ℂ) := by
  unfold Mk gE
  have h := integral_cexp_quadratic (b := -1 / 2) (by norm_num) (-I * ξ) 0
  have e : ∀ v : ℝ, (v : ℂ) ^ 0 * Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v) =
      Complex.exp (-1 / 2 * (v : ℂ) ^ 2 + -I * ξ * v + 0) := by intro v; rw [pow_zero, one_mul]; ring_nf
  simp_rw [e, h]
  have hpi : (π : ℂ) / -(-1 / 2) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [hpi, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 1; congr 1
  push_cast
  linear_combination ((ξ : ℂ) ^ 2 / 2) * I_sq

/-- The standard normal density `φ(z) = e^{−z²/2}/√(2π)`. -/
noncomputable def phiN (z : ℝ) : ℝ := Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * π)

/-- **The Gaussian integrals** (Proposition C): for `s > 0`, `κ₁, T ∈ ℝ`, `k ≤ 6` and `z = (T − κ₁)/s`,
`(2π)^{−1} ∫ (iσ)^k e^{iκ₁σ − s²σ²/2 − iTσ} dσ = He_k(z) φ(z)/s^{k+1}`. -/
theorem gauss_He {s : ℝ} (hs : 0 < s) (κ₁ T : ℝ) {k : ℕ} (hk : k ≤ 6) :
    (1 / (2 * π) : ℂ) * ∫ σ : ℝ, (I * σ) ^ k * Complex.exp (I * κ₁ * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) =
      ((He k ((T - κ₁) / s) * phiN ((T - κ₁) / s) / s ^ (k + 1) : ℝ) : ℂ) := by
  set z := (T - κ₁) / s with hz
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hF : ∀ σ : ℝ, (I * σ) ^ k * Complex.exp (I * κ₁ * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) =
      (I ^ k / (s : ℂ) ^ k) * ((((s * σ : ℝ)) : ℂ) ^ k * gE z (s * σ)) := by
    intro σ
    have hE : Complex.exp (I * κ₁ * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) = gE z (s * σ) := by
      unfold gE; congr 1; rw [hz]; push_cast; field_simp; ring
    rw [hE, mul_pow]; push_cast; field_simp; ring
  simp_rw [hF]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v : ℝ => (v : ℂ) ^ k * gE z v) s]
  have hM : ∫ v : ℝ, (v : ℂ) ^ k * gE z v = Mk k z := rfl
  rw [hM, abs_of_pos (inv_pos.mpr hs), Complex.real_smul]
  have hk' : I ^ k * Mk k z = (He k z : ℂ) * Mk 0 z := mk_He z k hk
  have hsq : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hsq0 : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  calc (1 / (2 * π) : ℂ) * (I ^ k / (s : ℂ) ^ k * (((s⁻¹ : ℝ) : ℂ) * Mk k z))
      = (1 / (2 * π) : ℂ) / (s : ℂ) ^ k * ((s⁻¹ : ℝ) : ℂ) * (I ^ k * Mk k z) := by ring
    _ = _ := by
        rw [hk', Mk_zero, phiN]; push_cast
        have hq : ((Real.sqrt (2 * π) : ℝ) : ℂ) ^ 2 = 2 * π := by exact_mod_cast hsq
        have hq0 : ((Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
        field_simp
        rw [← hq]; ring

/-- `A_k = ∫ |v|^k e^{−v²/2} dv`. -/
noncomputable def Am (k : ℕ) : ℝ := ∫ v : ℝ, |v| ^ k * Real.exp (-v ^ 2 / 2)

theorem integrable_absmom (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Integrable fun σ : ℝ => |σ| ^ k * Real.exp (-(s ^ 2 * σ ^ 2) / 2) := by
  have := integrable_pow_gauss k (b := s ^ 2 / 2) (by positivity)
  refine this.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only; congr 2; ring

/-- `∫ |σ|^k e^{−s²σ²/2} dσ = A_k / s^{k+1}`. -/
theorem absmom_scale (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ σ : ℝ, |σ| ^ k * Real.exp (-(s ^ 2 * σ ^ 2) / 2) = Am k / s ^ (k + 1) := by
  have hF : ∀ σ : ℝ, |σ| ^ k * Real.exp (-(s ^ 2 * σ ^ 2) / 2) =
      (1 / s ^ k) * (|s * σ| ^ k * Real.exp (-(s * σ) ^ 2 / 2)) := by
    intro σ; rw [abs_mul, abs_of_pos hs, mul_pow]; field_simp
  simp_rw [hF]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v : ℝ => |v| ^ k * Real.exp (-v ^ 2 / 2)) s,
    abs_of_pos (inv_pos.mpr hs), smul_eq_mul]
  unfold Am; rw [pow_succ]; field_simp

theorem Am_nonneg (k : ℕ) : 0 ≤ Am k := integral_nonneg fun v => by positivity

end ArcsAlgo.Edge
