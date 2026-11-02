module

public import ArcsAlgo.LocalLimit.Fourier
public import ArcsAlgo.LocalLimit.LamSix
set_option autoImplicit false

/-!
# The characteristic function of a centred uniform weight (paper §6.2, proof of Lemma B0′)

`f(θ) = M⁻¹ Σ_{j=1}^M cos((j − μ)θ)` with `μ = (M + 1)/2` is the characteristic function of
`w − μ`; `phiW_eq` gives `φ(θ) = e^{iμθ} f(θ)`, and `lawS_eq_integral_fC` the inversion formula
`Pr(S_k = v) = (2π)⁻¹ ∫_{−π}^{π} f(θ)^k e^{−i(v − kμ)θ} dθ`.

* `fC_eq`: `f(θ) = sin(Mθ/2) / (M sin(θ/2))` (telescoping).
* `fC_main`: on `0 < |θ| ≤ π/M`, `f > 0` and
  `log f = −σ²θ²/2 + κ₄θ⁴/24 + Λ₆(M|θ|/2) − Λ₆(|θ|/2)`, with `σ² = (M² − 1)/12` and
  `κ₄ = −(M⁴ − 1)/120`: this is `log f = −σ²θ²/2 + Λ(y) − Λ(x)` of the paper.
* `abs_fC_le`: on `π/M ≤ |θ| ≤ π`, `|f| ≤ q_M = 1/(M sin(π/(2M)))`, and `qM_le`: `q_M ≤ 1/√2`.
* `integral_fC_sq`: `∫_{−π}^{π} f² = 2π/M`.
-/

open Real Complex Finset MeasureTheory intervalIntegral

@[expose] public section

namespace ArcsAlgo.LLT

/-- The mean `μ = (M + 1)/2` of a uniform weight. -/
noncomputable def muW (M : ℕ) : ℝ := ((M : ℝ) + 1) / 2

/-- The characteristic function of `w − μ`, `f(θ) = M⁻¹ Σ_{j=1}^M cos((j − μ)θ)`; it is real
because the law of `w − μ` is symmetric. -/
noncomputable def fC (M : ℕ) (θ : ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ j : Fin M, Real.cos (θ * (((j : ℕ) : ℝ) + 1 - muW M))

lemma fC_neg (M : ℕ) (θ : ℝ) : fC M (-θ) = fC M θ := by
  simp only [fC, neg_mul, Real.cos_neg]

lemma fC_zero {M : ℕ} (hM : 0 < M) : fC M 0 = 1 := by
  simp [fC]; field_simp

lemma sum_sin_centered (M : ℕ) (θ : ℝ) :
    ∑ j : Fin M, Real.sin (θ * (((j : ℕ) : ℝ) + 1 - muW M)) = 0 := by
  have h : ∑ j : Fin M, Real.sin (θ * (((j : ℕ) : ℝ) + 1 - muW M)) =
      ∑ j : Fin M, Real.sin (θ * (((Fin.rev j : ℕ) : ℝ) + 1 - muW M)) :=
    (Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)).symm
  have h2 : ∀ j : Fin M, Real.sin (θ * (((Fin.rev j : ℕ) : ℝ) + 1 - muW M)) =
      -Real.sin (θ * (((j : ℕ) : ℝ) + 1 - muW M)) := by
    intro j
    rw [Fin.val_rev, Nat.cast_sub (by omega), ← Real.sin_neg]
    congr 1; simp only [muW]; push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_neg_distrib] at h
  linarith

/-- `φ(θ) = e^{iμθ} f(θ)`. -/
lemma phiW_eq {M : ℕ} (θ : ℝ) : phiW M θ = cexp (I * muW M * θ) * (fC M θ : ℂ) := by
  have e : ∀ j : Fin M, cexp (I * (((j : ℕ) : ℂ) + 1) * θ) = cexp (I * muW M * θ) *
      ((Real.cos (θ * (((j : ℕ) : ℝ) + 1 - muW M)) : ℂ)
        + (Real.sin (θ * (((j : ℕ) : ℝ) + 1 - muW M)) : ℂ) * I) := by
    intro j
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [phiW, fC, Finset.sum_congr rfl (fun j _ => e j), ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  simp only [← Complex.ofReal_sum]
  rw [sum_sin_centered]
  push_cast; ring

/-- `f(θ) = sin(Mθ/2) / (M sin(θ/2))` where `sin(θ/2) ≠ 0`. -/
lemma fC_eq {M : ℕ} (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) :
    fC M θ = Real.sin (M * θ / 2) / (M * Real.sin (θ / 2)) := by
  have key : 2 * Real.sin (θ / 2) * ∑ j : Fin M, Real.cos (θ * (((j : ℕ) : ℝ) + 1 - muW M)) =
      2 * Real.sin (M * θ / 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (θ * ((j : ℝ) + 1 - muW M))), Finset.mul_sum]
    have ht : ∀ j ∈ range M, 2 * Real.sin (θ / 2) * Real.cos (θ * ((j : ℝ) + 1 - muW M)) =
        Real.sin (θ * (((j + 1 : ℕ) : ℝ) + 1 / 2 - muW M)) -
          Real.sin (θ * ((j : ℝ) + 1 / 2 - muW M)) := by
      intro j _
      have e1 : θ * (((j + 1 : ℕ) : ℝ) + 1 / 2 - muW M) = θ * ((j : ℝ) + 1 - muW M) + θ / 2 := by
        push_cast; ring
      have e2 : θ * ((j : ℝ) + 1 / 2 - muW M) = θ * ((j : ℝ) + 1 - muW M) - θ / 2 := by ring
      rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
    rw [Finset.sum_congr rfl ht, Finset.sum_range_sub (fun j => Real.sin (θ * ((j : ℝ) + 1 / 2 - muW M)))]
    have e3 : θ * ((M : ℝ) + 1 / 2 - muW M) = M * θ / 2 := by simp only [muW]; ring
    have e4 : θ * (((0 : ℕ) : ℝ) + 1 / 2 - muW M) = -(M * θ / 2) := by simp only [muW]; push_cast; ring
    rw [e3, e4, Real.sin_neg]; ring
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [fC]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [fC, eq_div_iff (mul_ne_zero hM' hs)]
  generalize ∑ j : Fin M, Real.cos (θ * (((j : ℕ) : ℝ) + 1 - muW M)) = S at key ⊢
  field_simp
  linear_combination key / 2

/-- Fourier inversion in centred form: `Pr(S_k = v) = (2π)⁻¹ ∫_{−π}^{π} f(θ)^k e^{−itθ} dθ`
with `t = v − kμ`. -/
lemma lawS_eq_integral_fC {M : ℕ} (hM : 0 < M) (k : ℕ) (v : ℤ) :
    ((lawS M k v : ℝ) : ℂ) = (1 / (2 * π)) * ∫ θ in (-π)..π,
      ((fC M θ ^ k : ℝ) : ℂ) * cexp (-(I * ((v : ℝ) - k * muW M) * θ)) := by
  rw [lawS_eq_integral hM]
  refine congrArg _ (intervalIntegral.integral_congr (fun θ _ => ?_))
  show phiW M θ ^ k * cexp (-(I * v * θ)) = _
  rw [phiW_eq, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow]
  rw [show cexp (k * (I * muW M * θ)) * (fC M θ : ℂ) ^ k * cexp (-(I * v * θ)) =
    (fC M θ : ℂ) ^ k * (cexp (k * (I * muW M * θ)) * cexp (-(I * v * θ))) by ring,
    ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `σ² = (M² − 1)/12`, the variance of a uniform weight. -/
noncomputable def sig2 (M : ℕ) : ℝ := ((M : ℝ) ^ 2 - 1) / 12

/-- `κ₄ = −(M⁴ − 1)/120`, its fourth cumulant. -/
noncomputable def kap4 (M : ℕ) : ℝ := -(((M : ℝ) ^ 4 - 1) / 120)

/-- On `0 < |θ| ≤ π/M`: `f(θ) > 0` and
`log f(θ) = −σ²θ²/2 + κ₄θ⁴/24 + Λ₆(M|θ|/2) − Λ₆(|θ|/2)`. -/
lemma fC_main {M : ℕ} (hM : 2 ≤ M) {θ : ℝ} (h0 : θ ≠ 0) (h1 : |θ| ≤ π / M) :
    0 < fC M θ ∧ Real.log (fC M θ) = -(sig2 M * θ ^ 2 / 2) + kap4 M * θ ^ 4 / 24 +
      (lam6 (M * |θ| / 2) - lam6 (|θ| / 2)) := by
  have hπ := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hfa : fC M θ = fC M |θ| := by
    rcases abs_choice θ with h | h <;> rw [h]; rw [fC_neg]
  set s := |θ| with hs
  have hs0 : 0 < s := abs_pos.mpr h0
  have hy : M * s / 2 ≤ π / 2 := by
    have := (le_div_iff₀ hM0).mp h1; nlinarith
  have hx : s / 2 ≤ π / 4 := by nlinarith
  have hsx : 0 < Real.sin (s / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hsy : 0 < Real.sin (M * s / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hf : fC M s = (Real.sin (M * s / 2) / (M * s / 2)) / (Real.sin (s / 2) / (s / 2)) := by
    rw [fC_eq s hsx.ne']; field_simp
  have hA : 0 < Real.sin (M * s / 2) / (M * s / 2) := by positivity
  have hB : 0 < Real.sin (s / 2) / (s / 2) := by positivity
  rw [hfa, hf]
  refine ⟨div_pos hA hB, ?_⟩
  rw [Real.log_div hA.ne' hB.ne']
  have e1 : Real.log (Real.sin (M * s / 2) / (M * s / 2)) =
      lam6 (M * s / 2) - (M * s / 2) ^ 2 / 6 - (M * s / 2) ^ 4 / 180 := by simp only [lam6]; ring
  have e2 : Real.log (Real.sin (s / 2) / (s / 2)) =
      lam6 (s / 2) - (s / 2) ^ 2 / 6 - (s / 2) ^ 4 / 180 := by simp only [lam6]; ring
  have e3 : θ ^ 2 = s ^ 2 := (sq_abs θ).symm
  have e4 : θ ^ 4 = s ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, e3]
  rw [e1, e2, e3, e4, sig2, kap4]; ring

/-- `q_M = 1/(M sin(π/(2M)))`. -/
noncomputable def qM (M : ℕ) : ℝ := 1 / (M * Real.sin (π / (2 * M)))

lemma sqrt_two_le_M_sin {M : ℕ} (hM : 2 ≤ M) : √2 ≤ M * Real.sin (π / (2 * M)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rcases eq_or_lt_of_le hM with h | h
  · subst h; norm_num
    linarith
  · have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast h
    have hx0 : 0 < π / (2 * M) := by positivity
    have h1 := Real.sin_gt_sub_cube hx0
    have hpl := Real.pi_lt_d4
    have hpg := Real.pi_gt_d4
    have hsq : √2 < 1.4143 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have : M * (π / (2 * M) - (π / (2 * M)) ^ 3 / 6) = π / 2 - π ^ 3 / (48 * M ^ 2) := by
      field_simp; ring
    have h3 : π ^ 3 / (48 * M ^ 2) ≤ π ^ 3 / 432 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
    have hp3 : π ^ 3 < 3.1416 ^ 3 := by
      exact pow_lt_pow_left₀ hpl Real.pi_pos.le (by norm_num)
    have := mul_lt_mul_of_pos_left h1 hM0
    nlinarith

lemma qM_pos {M : ℕ} (hM : 2 ≤ M) : 0 < qM M := by
  have := sqrt_two_le_M_sin hM
  have : (0 : ℝ) < √2 := by positivity
  unfold qM; apply div_pos one_pos; linarith

lemma qM_le {M : ℕ} (hM : 2 ≤ M) : qM M ≤ 1 / √2 := by
  have := sqrt_two_le_M_sin hM
  unfold qM; exact one_div_le_one_div_of_le (by positivity) this

/-- On `π/M ≤ |θ| ≤ π`: `|f(θ)| ≤ q_M`. -/
lemma abs_fC_le {M : ℕ} (hM : 2 ≤ M) {θ : ℝ} (h1 : π / M ≤ |θ|) (h2 : |θ| ≤ π) :
    |fC M θ| ≤ qM M := by
  have hπ := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hfa : fC M θ = fC M |θ| := by
    rcases abs_choice θ with h | h <;> rw [h]; rw [fC_neg]
  set s := |θ|
  have hle : Real.sin (π / (2 * M)) ≤ Real.sin (s / 2) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by
      have : 0 < π / (2 * M) := by positivity
      linarith) (by linarith)
    rw [show π / (2 * M) = (π / M) / 2 by ring]; linarith
  have hq0 : 0 < Real.sin (π / (2 * M)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hM2 hπ.le]
  have hsx : 0 < Real.sin (s / 2) := lt_of_lt_of_le hq0 hle
  rw [hfa, fC_eq s hsx.ne', abs_div, abs_of_pos (by positivity : (0 : ℝ) < M * Real.sin (s / 2)),
    qM, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have := Real.abs_sin_le_one (M * s / 2)
  calc |Real.sin (M * s / 2)| * (M * Real.sin (π / (2 * M))) ≤ 1 * (M * Real.sin (s / 2)) := by
        apply mul_le_mul this (by gcongr) (by positivity) zero_le_one
    _ = M * Real.sin (s / 2) := one_mul _

/-- Parseval: `∫_{−π}^{π} f(θ)² dθ = 2π/M`. -/
lemma integral_fC_sq {M : ℕ} (hM : 0 < M) : ∫ θ in (-π)..π, fC M θ ^ 2 = 2 * π / M := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : ∀ θ : ℝ, ((fC M θ ^ 2 : ℝ) : ℂ) = ∑ j : Fin M, ∑ l : Fin M,
      (1 / (M : ℂ)) ^ 2 * cexp (I * ((((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) : ℤ) : ℂ) * θ) := by
    intro θ
    have h1 := phiW_eq (M := M) θ
    have h2 := phiW_eq (M := M) (-θ)
    rw [fC_neg] at h2
    have h3 : phiW M θ * phiW M (-θ) = ((fC M θ ^ 2 : ℝ) : ℂ) := by
      have : cexp (I * muW M * θ) * cexp (I * muW M * (-θ : ℝ)) = 1 := by
        rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
      rw [h1, h2, Complex.ofReal_pow]
      linear_combination (fC M θ : ℂ) ^ 2 * this
    rw [← h3, phiW, phiW, mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    apply sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply sum_congr rfl; intro l _
    rw [← Complex.exp_add, ← sq]
    congr 2; push_cast; ring
  have hint : ∀ j l : Fin M, IntervalIntegrable (fun θ : ℝ => (1 / (M : ℂ)) ^ 2 *
      cexp (I * ((((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) : ℤ) : ℂ) * θ)) volume (-π) π :=
    fun j l => by apply Continuous.intervalIntegrable; fun_prop
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum (fun j _ => ?_)]
  · simp_rw [intervalIntegral.integral_finsetSum (fun l _ => hint _ l),
      intervalIntegral.integral_const_mul, integral_exp_int, sub_eq_zero, Nat.cast_inj,
      Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp
  · apply Continuous.intervalIntegrable; fun_prop

end ArcsAlgo.LLT
