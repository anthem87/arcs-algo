module

public import ArcsAlgo.EdgeGauss
set_option autoImplicit false

/-!
# Theorem E(2), the vanishing factor: Gaussian integrals with complex centre (paper §3.5)

The cumulant `κ₁` of `G̃ = G·e^{iwt/2} sinc(wt/2)` at `t*` is not real, so `z = (T − κ₁)/s` is complex.

* `MkC`, `mkC_He`, `MkC_zero`: `i^k M_k(ξ) = He_k(ξ)√(2π)e^{−ξ²/2}` for complex `ξ`, `k ≤ 7`.
* `gaussC_He`: `(2π)^{−1}∫(iσ)^k e^{iκ₁σ − s²σ²/2 − iTσ} dσ = He_k(z)φ(z)/s^{k+1}`, `κ₁ ∈ ℂ`.
* `mainEC`, `edge_mainC`: the Edgeworth arc term with complex `κ₁`.
* `dmainEC`, `edge_dmainC`, `hasDerivAt_mainEC`, `deriv_mainEC`: its `T`-derivative,
  `(2π)^{−1}∫(−iσ)edgeIC e^{−iTσ} = d/dT mainEC` (`He_k′ − zHe_k = −He_{k+1}`).

No hypothesis.
-/

open Complex MeasureTheory Real

@[expose] public section

namespace ArcsAlgo.Edge

/-- `g_ξ(v) = e^{−v²/2 − iξv}`, complex `ξ`. -/
noncomputable def gEC (ξ : ℂ) (v : ℝ) : ℂ := Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v)

/-- `M_k(ξ) = ∫ v^k e^{−v²/2 − iξv} dv`, complex `ξ`. -/
noncomputable def MkC (k : ℕ) (ξ : ℂ) : ℂ := ∫ v : ℝ, (v : ℂ) ^ k * gEC ξ v

theorem norm_gEC_le (ξ : ℂ) (v : ℝ) :
    ‖gEC ξ v‖ ≤ Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 4) * v ^ 2) := by
  unfold gEC; rw [Complex.norm_exp, ← Real.exp_add]; apply Real.exp_le_exp.mpr
  have : (-(v : ℂ) ^ 2 / 2 - I * ξ * v).re = -v ^ 2 / 2 + ξ.im * v := by
    simp [Complex.sub_re, Complex.mul_re, sq, Complex.div_re]
  rw [this]; nlinarith [sq_nonneg (v / 2 - ξ.im)]

theorem integrable_momC (k : ℕ) (ξ : ℂ) : Integrable fun v : ℝ => (v : ℂ) ^ k * gEC ξ v := by
  refine Integrable.mono' ((integrable_pow_gauss k (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (Real.exp (ξ.im ^ 2))) ?_ ?_
  · unfold gEC; fun_prop
  · refine Filter.Eventually.of_forall fun v => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have := norm_gEC_le ξ v
    calc |v| ^ k * ‖gEC ξ v‖ ≤ |v| ^ k * (Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 4) * v ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

theorem hasDerivAt_gEC (ξ : ℂ) (v : ℝ) : HasDerivAt (gEC ξ) ((-(v : ℂ) - I * ξ) * gEC ξ v) v := by
  have hv := hasDerivAt_ofReal v
  have hq : HasDerivAt (fun x : ℝ => -(x : ℂ) ^ 2 / 2 - I * ξ * x) (-(v : ℂ) - I * ξ) v := by
    have := ((hv.pow 2).neg.div_const 2).sub (hv.const_mul (I * ξ))
    convert this using 1; simp; ring
  have := hq.cexp
  unfold gEC; convert this using 1; ring

theorem MkC_one (ξ : ℂ) : MkC 1 ξ = -I * ξ * MkC 0 ξ := by
  have hd := fun v => hasDerivAt_gEC ξ v
  have e : (fun v : ℝ => (-(v : ℂ) - I * ξ) * gEC ξ v) =
      fun v : ℝ => -((v : ℂ) ^ 1 * gEC ξ v) + (-I * ξ) * ((v : ℂ) ^ 0 * gEC ξ v) := by ext v; ring
  have hI : Integrable (fun v : ℝ => (-(v : ℂ) - I * ξ) * gEC ξ v) := by
    rw [e]; exact (integrable_momC 1 ξ).neg.add ((integrable_momC 0 ξ).const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hI (by simpa using integrable_momC 0 ξ)
  have hA : Integrable (fun v : ℝ => -((v : ℂ) ^ 1 * gEC ξ v)) := (integrable_momC 1 ξ).neg
  have hB : Integrable (fun v : ℝ => (-I * ξ) * ((v : ℂ) ^ 0 * gEC ξ v)) := (integrable_momC 0 ξ).const_mul _
  rw [e, integral_add hA hB, integral_neg, integral_const_mul] at h0
  unfold MkC; linear_combination -h0

theorem MkC_succ_succ (n : ℕ) (ξ : ℂ) : MkC (n + 2) ξ = -I * ξ * MkC (n + 1) ξ + (n + 1) * MkC n ξ := by
  have hd : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) ^ (n + 1) * gEC ξ v)
      ((n + 1) * ((v : ℂ) ^ n * gEC ξ v) - (v : ℂ) ^ (n + 2) * gEC ξ v + (-I * ξ) * ((v : ℂ) ^ (n + 1) * gEC ξ v)) v := by
    intro v
    have h1 := ((hasDerivAt_ofReal v).pow (n + 1)).mul (hasDerivAt_gEC ξ v)
    convert h1 using 1
    simp; ring
  have hI : Integrable fun v : ℝ =>
      (n + 1) * ((v : ℂ) ^ n * gEC ξ v) - (v : ℂ) ^ (n + 2) * gEC ξ v + (-I * ξ) * ((v : ℂ) ^ (n + 1) * gEC ξ v) :=
    (((integrable_momC n ξ).const_mul _).sub (integrable_momC (n + 2) ξ)).add ((integrable_momC (n + 1) ξ).const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hI (integrable_momC (n + 1) ξ)
  have hA : Integrable (fun v : ℝ => (n + 1) * ((v : ℂ) ^ n * gEC ξ v) - (v : ℂ) ^ (n + 2) * gEC ξ v) :=
    ((integrable_momC n ξ).const_mul _).sub (integrable_momC (n + 2) ξ)
  have hB : Integrable (fun v : ℝ => (-I * ξ) * ((v : ℂ) ^ (n + 1) * gEC ξ v)) :=
    (integrable_momC (n + 1) ξ).const_mul _
  have hA1 : Integrable (fun v : ℝ => (n + 1) * ((v : ℂ) ^ n * gEC ξ v)) := (integrable_momC n ξ).const_mul _
  rw [integral_add hA hB, integral_sub hA1 (integrable_momC (n + 2) ξ),
    integral_const_mul, integral_const_mul] at h0
  unfold MkC; linear_combination -h0

theorem mkC_rec (n : ℕ) (ξ : ℂ) :
    I ^ (n + 2) * MkC (n + 2) ξ = ξ * (I ^ (n + 1) * MkC (n + 1) ξ) - (n + 1) * (I ^ n * MkC n ξ) := by
  rw [MkC_succ_succ]
  have e1 : I ^ (n + 2) = -I ^ n := by rw [pow_add, I_sq]; ring
  have e2 : I ^ (n + 2) * (-I) = I ^ (n + 1) := by
    rw [show n + 2 = n + 1 + 1 from rfl, pow_succ]; linear_combination (-(I ^ (n + 1))) * I_mul_I
  linear_combination ξ * MkC (n + 1) ξ * e2 + (n + 1) * MkC n ξ * e1

/-- The Hermite polynomials `He₀, …, He₇` over `ℂ`. -/
noncomputable def HeC : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | 1 => fun z => z
  | 2 => fun z => z ^ 2 - 1
  | 3 => fun z => z ^ 3 - 3 * z
  | 4 => fun z => z ^ 4 - 6 * z ^ 2 + 3
  | 5 => fun z => z ^ 5 - 10 * z ^ 3 + 15 * z
  | 6 => fun z => z ^ 6 - 15 * z ^ 4 + 45 * z ^ 2 - 15
  | 7 => fun z => z ^ 7 - 21 * z ^ 5 + 105 * z ^ 3 - 105 * z
  | _ => fun _ => 0

set_option maxHeartbeats 4000000 in
theorem mkC_He (ξ : ℂ) : ∀ k ≤ 7, I ^ k * MkC k ξ = HeC k ξ * MkC 0 ξ := by
  have h1 : I ^ 1 * MkC 1 ξ = HeC 1 ξ * MkC 0 ξ := by
    rw [MkC_one]; simp [HeC]; ring_nf; rw [I_sq]; ring
  have h0 : I ^ 0 * MkC 0 ξ = HeC 0 ξ * MkC 0 ξ := by simp [HeC]
  have h2 : I ^ 2 * MkC 2 ξ = HeC 2 ξ * MkC 0 ξ := by rw [mkC_rec 0, h1, h0]; simp [HeC]; ring
  have h3 : I ^ 3 * MkC 3 ξ = HeC 3 ξ * MkC 0 ξ := by rw [mkC_rec 1, h2, h1]; simp [HeC]; ring
  have h4 : I ^ 4 * MkC 4 ξ = HeC 4 ξ * MkC 0 ξ := by rw [mkC_rec 2, h3, h2]; simp [HeC]; ring
  have h5 : I ^ 5 * MkC 5 ξ = HeC 5 ξ * MkC 0 ξ := by rw [mkC_rec 3, h4, h3]; simp [HeC]; ring
  have h6 : I ^ 6 * MkC 6 ξ = HeC 6 ξ * MkC 0 ξ := by rw [mkC_rec 4, h5, h4]; simp [HeC]; ring
  have h7 : I ^ 7 * MkC 7 ξ = HeC 7 ξ * MkC 0 ξ := by rw [mkC_rec 5, h6, h5]; simp [HeC]; ring
  intro k hk
  interval_cases k <;> assumption

/-- `M₀(ξ) = √(2π) e^{−ξ²/2}`, complex `ξ`. -/
theorem MkC_zero (ξ : ℂ) : MkC 0 ξ = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-ξ ^ 2 / 2) := by
  unfold MkC gEC
  have h := integral_cexp_quadratic (b := -1 / 2) (by norm_num) (-I * ξ) 0
  have e : ∀ v : ℝ, (v : ℂ) ^ 0 * Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v) =
      Complex.exp (-1 / 2 * (v : ℂ) ^ 2 + -I * ξ * v + 0) := by intro v; rw [pow_zero, one_mul]; ring_nf
  simp_rw [e, h]
  have hpi : (π : ℂ) / -(-1 / 2) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [hpi, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow]
  congr 2
  linear_combination (ξ ^ 2 / 2) * I_sq

/-- The normal density `φ(z) = e^{−z²/2}/√(2π)` at complex `z`. -/
noncomputable def phiC (z : ℂ) : ℂ := Complex.exp (-z ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ)

/-- `(iσ)^k e^{iκ₁σ − s²σ²/2 − iTσ}`, complex `κ₁`. -/
noncomputable def EkC (k : ℕ) (k1 : ℂ) (s T σ : ℝ) : ℂ :=
  (I * σ) ^ k * Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ)

theorem EkC_eq {s : ℝ} (hs : 0 < s) (k : ℕ) (k1 : ℂ) (T σ : ℝ) :
    EkC k k1 s T σ = (I ^ k / (s : ℂ) ^ k) * ((((s * σ : ℝ)) : ℂ) ^ k * gEC ((T - k1) / s) (s * σ)) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold EkC
  have hE : Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) = gEC ((T - k1) / s) (s * σ) := by
    unfold gEC; congr 1; push_cast; field_simp; ring
  rw [hE, mul_pow]; push_cast; field_simp; ring

theorem integrable_EkC (k : ℕ) (k1 : ℂ) (T : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable fun σ => EkC k k1 s T σ := by
  simp_rw [EkC_eq hs]
  exact ((integrable_momC k ((T - k1) / s)).comp_mul_left' hs.ne').const_mul _

/-- **The Gaussian integrals, complex centre**: for `s > 0`, `κ₁ ∈ ℂ`, `T ∈ ℝ`, `k ≤ 7` and
`z = (T − κ₁)/s`: `(2π)^{−1} ∫ (iσ)^k e^{iκ₁σ − s²σ²/2 − iTσ} dσ = He_k(z) φ(z)/s^{k+1}`. -/
theorem gaussC_He {s : ℝ} (hs : 0 < s) (κ₁ : ℂ) (T : ℝ) {k : ℕ} (hk : k ≤ 7) :
    (1 / (2 * π) : ℂ) * ∫ σ : ℝ, EkC k κ₁ s T σ = HeC k ((T - κ₁) / s) * phiC ((T - κ₁) / s) / (s : ℂ) ^ (k + 1) := by
  set z := (T - κ₁) / s with hz
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp_rw [EkC_eq hs]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v : ℝ => (v : ℂ) ^ k * gEC z v) s]
  have hM : ∫ v : ℝ, (v : ℂ) ^ k * gEC z v = MkC k z := rfl
  rw [hM, abs_of_pos (inv_pos.mpr hs), Complex.real_smul]
  have hk' : I ^ k * MkC k z = HeC k z * MkC 0 z := mkC_He z k hk
  have hsq : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hsq0 : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  calc (1 / (2 * π) : ℂ) * (I ^ k / (s : ℂ) ^ k * (((s⁻¹ : ℝ) : ℂ) * MkC k z))
      = (1 / (2 * π) : ℂ) / (s : ℂ) ^ k * ((s⁻¹ : ℝ) : ℂ) * (I ^ k * MkC k z) := by ring
    _ = _ := by
        rw [hk', MkC_zero, phiC]; push_cast
        have hq : ((Real.sqrt (2 * π) : ℝ) : ℂ) ^ 2 = 2 * π := by exact_mod_cast hsq
        have hq0 : ((Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
        field_simp
        rw [← hq]; ring

/-- The Edgeworth integrand `e^{iκ₁σ − s²σ²/2}(1 + κ₃(iσ)³/6 + κ₄(iσ)⁴/24 + κ₃²(iσ)⁶/72)`, complex `κ₁`. -/
noncomputable def edgeIC (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (σ : ℝ) : ℂ :=
  Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) *
    (1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72)

/-- The Edgeworth arc term `φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`,
`z = (T − κ₁)/s`, complex `κ₁`. -/
noncomputable def mainEC (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) : ℂ :=
  phiC ((T - k1) / s) / s * (1 + κ₃ * HeC 3 ((T - k1) / s) / (6 * (s : ℂ) ^ 3) +
    κ₄ * HeC 4 ((T - k1) / s) / (24 * (s : ℂ) ^ 4) + κ₃ ^ 2 * HeC 6 ((T - k1) / s) / (72 * (s : ℂ) ^ 6))

/-- Its derivative in `T`: `−φ(z)/s²·(He₁(z) + κ₃He₄(z)/(6s³) + κ₄He₅(z)/(24s⁴) + κ₃²He₇(z)/(72s⁶))`. -/
noncomputable def dmainEC (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) : ℂ :=
  -(phiC ((T - k1) / s) / (s : ℂ) ^ 2) * (HeC 1 ((T - k1) / s) + κ₃ * HeC 4 ((T - k1) / s) / (6 * (s : ℂ) ^ 3) +
    κ₄ * HeC 5 ((T - k1) / s) / (24 * (s : ℂ) ^ 4) + κ₃ ^ 2 * HeC 7 ((T - k1) / s) / (72 * (s : ℂ) ^ 6))

theorem edgeIC_mul (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (T σ : ℝ) :
    edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) =
      EkC 0 k1 s T σ + κ₃ / 6 * EkC 3 k1 s T σ + κ₄ / 24 * EkC 4 k1 s T σ + κ₃ ^ 2 / 72 * EkC 6 k1 s T σ := by
  unfold edgeIC EkC
  have : Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) =
      Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) * Complex.exp (-(I * T * σ)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

theorem edgeIC_dmul (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (T σ : ℝ) :
    (-(I * σ)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) =
      -(EkC 1 k1 s T σ + κ₃ / 6 * EkC 4 k1 s T σ + κ₄ / 24 * EkC 5 k1 s T σ + κ₃ ^ 2 / 72 * EkC 7 k1 s T σ) := by
  rw [edgeIC_mul]; unfold EkC; ring

theorem integrable_edgeIC {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    Integrable fun σ => edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) := by
  simp_rw [edgeIC_mul]
  exact (((integrable_EkC 0 k1 T hs).add ((integrable_EkC 3 k1 T hs).const_mul _)).add
    ((integrable_EkC 4 k1 T hs).const_mul _)).add ((integrable_EkC 6 k1 T hs).const_mul _)

theorem integrable_edgeIC_d {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    Integrable fun σ => (-(I * σ)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) := by
  simp_rw [edgeIC_dmul]
  exact ((((integrable_EkC 1 k1 T hs).add ((integrable_EkC 4 k1 T hs).const_mul _)).add
    ((integrable_EkC 5 k1 T hs).const_mul _)).add ((integrable_EkC 7 k1 T hs).const_mul _)).neg

theorem edge_mainC {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ σ : ℝ, edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) = mainEC k1 s κ₃ κ₄ T := by
  simp_rw [edgeIC_mul]
  have i0 : Integrable (fun σ => EkC 0 k1 s T σ) := integrable_EkC 0 k1 T hs
  have i3 : Integrable (fun σ => κ₃ / 6 * EkC 3 k1 s T σ) := (integrable_EkC 3 k1 T hs).const_mul (κ₃ / 6)
  have i4 : Integrable (fun σ => κ₄ / 24 * EkC 4 k1 s T σ) := (integrable_EkC 4 k1 T hs).const_mul (κ₄ / 24)
  have i6 : Integrable (fun σ => κ₃ ^ 2 / 72 * EkC 6 k1 s T σ) := (integrable_EkC 6 k1 T hs).const_mul (κ₃ ^ 2 / 72)
  have i03 : Integrable (fun σ => EkC 0 k1 s T σ + κ₃ / 6 * EkC 3 k1 s T σ) := i0.add i3
  have i034 : Integrable (fun σ => EkC 0 k1 s T σ + κ₃ / 6 * EkC 3 k1 s T σ + κ₄ / 24 * EkC 4 k1 s T σ) :=
    i03.add i4
  rw [integral_add i034 i6, integral_add i03 i4, integral_add i0 i3,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have g0 := gaussC_He hs k1 T (k := 0) (by norm_num)
  have g3 := gaussC_He hs k1 T (k := 3) (by norm_num)
  have g4 := gaussC_He hs k1 T (k := 4) (by norm_num)
  have g6 := gaussC_He hs k1 T (k := 6) (by norm_num)
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold mainEC
  set J0 := ∫ σ : ℝ, EkC 0 k1 s T σ
  set J3 := ∫ σ : ℝ, EkC 3 k1 s T σ
  set J4 := ∫ σ : ℝ, EkC 4 k1 s T σ
  set J6 := ∫ σ : ℝ, EkC 6 k1 s T σ
  have e : (1 / (2 * π) : ℂ) * (J0 + κ₃ / 6 * J3 + κ₄ / 24 * J4 + κ₃ ^ 2 / 72 * J6) =
      (1 / (2 * π) : ℂ) * J0 + κ₃ / 6 * ((1 / (2 * π) : ℂ) * J3) + κ₄ / 24 * ((1 / (2 * π) : ℂ) * J4) +
      κ₃ ^ 2 / 72 * ((1 / (2 * π) : ℂ) * J6) := by ring
  rw [e, g0, g3, g4, g6]
  simp only [HeC]
  field_simp
  ring

theorem edge_dmainC {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ σ : ℝ, (-(I * σ)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) =
      dmainEC k1 s κ₃ κ₄ T := by
  simp_rw [edgeIC_dmul]
  have i1 : Integrable (fun σ => EkC 1 k1 s T σ) := integrable_EkC 1 k1 T hs
  have i4 : Integrable (fun σ => κ₃ / 6 * EkC 4 k1 s T σ) := (integrable_EkC 4 k1 T hs).const_mul (κ₃ / 6)
  have i5 : Integrable (fun σ => κ₄ / 24 * EkC 5 k1 s T σ) := (integrable_EkC 5 k1 T hs).const_mul (κ₄ / 24)
  have i7 : Integrable (fun σ => κ₃ ^ 2 / 72 * EkC 7 k1 s T σ) := (integrable_EkC 7 k1 T hs).const_mul (κ₃ ^ 2 / 72)
  have i14 : Integrable (fun σ => EkC 1 k1 s T σ + κ₃ / 6 * EkC 4 k1 s T σ) := i1.add i4
  have i145 : Integrable (fun σ => EkC 1 k1 s T σ + κ₃ / 6 * EkC 4 k1 s T σ + κ₄ / 24 * EkC 5 k1 s T σ) :=
    i14.add i5
  rw [integral_neg, integral_add i145 i7, integral_add i14 i5, integral_add i1 i4,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have g1 := gaussC_He hs k1 T (k := 1) (by norm_num)
  have g4 := gaussC_He hs k1 T (k := 4) (by norm_num)
  have g5 := gaussC_He hs k1 T (k := 5) (by norm_num)
  have g7 := gaussC_He hs k1 T (k := 7) (by norm_num)
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold dmainEC
  set J1 := ∫ σ : ℝ, EkC 1 k1 s T σ
  set J4 := ∫ σ : ℝ, EkC 4 k1 s T σ
  set J5 := ∫ σ : ℝ, EkC 5 k1 s T σ
  set J7 := ∫ σ : ℝ, EkC 7 k1 s T σ
  have e : (1 / (2 * π) : ℂ) * -(J1 + κ₃ / 6 * J4 + κ₄ / 24 * J5 + κ₃ ^ 2 / 72 * J7) =
      -((1 / (2 * π) : ℂ) * J1 + κ₃ / 6 * ((1 / (2 * π) : ℂ) * J4) + κ₄ / 24 * ((1 / (2 * π) : ℂ) * J5) +
      κ₃ ^ 2 / 72 * ((1 / (2 * π) : ℂ) * J7)) := by ring
  rw [e, g1, g4, g5, g7]
  simp only [HeC]
  field_simp
  ring

/-- `d/dz [e^{−z²/2}(1 + aHe₃ + bHe₄ + cHe₆)] = −e^{−z²/2}(He₁ + aHe₄ + bHe₅ + cHe₇)`. -/
theorem hasDerivAt_gaussPoly (a b c z : ℂ) :
    HasDerivAt (fun z => Complex.exp (-z ^ 2 / 2) * (1 + a * HeC 3 z + b * HeC 4 z + c * HeC 6 z))
      (-(Complex.exp (-z ^ 2 / 2) * (HeC 1 z + a * HeC 4 z + b * HeC 5 z + c * HeC 7 z))) z := by
  have he : HasDerivAt (fun z : ℂ => Complex.exp (-z ^ 2 / 2)) (Complex.exp (-z ^ 2 / 2) * (-z)) z := by
    have h := (((hasDerivAt_pow 2 z).neg).div_const 2).cexp
    convert h using 1; simp; ring
  have p3 := (hasDerivAt_pow 3 z).sub ((hasDerivAt_id z).const_mul 3)
  have p4 := ((hasDerivAt_pow 4 z).sub ((hasDerivAt_pow 2 z).const_mul 6)).add_const 3
  have p6 := (((hasDerivAt_pow 6 z).sub ((hasDerivAt_pow 4 z).const_mul 15)).add
    ((hasDerivAt_pow 2 z).const_mul 45)).sub_const 15
  have hp := (((p3.const_mul a).const_add 1).add (p4.const_mul b)).add (p6.const_mul c)
  have := he.mul hp
  convert this using 1
  · funext w; simp only [HeC, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp only [HeC, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; push_cast; ring

/-- `T ↦ mainEC(T)` has derivative `dmainEC(T)` (`He_k′ − zHe_k = −He_{k+1}`). -/
theorem hasDerivAt_mainEC {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    HasDerivAt (fun T : ℝ => mainEC k1 s κ₃ κ₄ T) (dmainEC k1 s κ₃ κ₄ T) T := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set c : ℂ := ((Real.sqrt (2 * π) : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    simp only [c]; exact_mod_cast this.ne'
  set a := κ₃ / (6 * (s : ℂ) ^ 3)
  set b := κ₄ / (24 * (s : ℂ) ^ 4)
  set d := κ₃ ^ 2 / (72 * (s : ℂ) ^ 6)
  have hz : HasDerivAt (fun u : ℂ => (u - k1) / s) (1 / s) (T : ℂ) :=
    ((hasDerivAt_id (T : ℂ)).sub_const k1).div_const _
  have hG := (hasDerivAt_gaussPoly a b d ((T - k1) / s)).comp (T : ℂ) hz
  have hF := (hG.const_mul (1 / (c * s))).comp_ofReal
  convert hF using 1
  · funext T'
    simp only [mainEC, phiC, Function.comp, a, b, d, c]
    field_simp
  · simp only [dmainEC, phiC, a, b, d, c]
    field_simp

theorem deriv_mainEC {s : ℝ} (hs : 0 < s) (k1 : ℂ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    deriv (fun T : ℝ => mainEC k1 s κ₃ κ₄ T) T = dmainEC k1 s κ₃ κ₄ T :=
  (hasDerivAt_mainEC hs k1 κ₃ κ₄ T).deriv

end ArcsAlgo.Edge
