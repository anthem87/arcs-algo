module

public import ArcsAlgo.LocalLimit.Numeric
public import ArcsAlgo.LocalLimit.Tails
set_option autoImplicit false

/-!
# The three ranges of the Fourier integral (paper §6.2, proof of Lemma B0′)

`PhiB = f(θ)^k e^{−itθ}` is the lattice integrand and `PsiB = e^{−aθ²}(1 + Bθ⁴) e^{−itθ}` its
Gaussian approximation with the first Edgeworth term; `∫ PsiB = G 0 + B·G 4` (`integral_PsiB`).

* `norm_main_le`: on `|θ| ≤ π/M`, `‖∫ (Φ − Ψ)‖ ≤ (B²/2) m₈(a) + 65ckσ⁶ m₆(β)` (from
  `main_pointwise`).
* `norm_mid_le`: on `π/M ≤ |θ| ≤ π`, `|f|^k ≤ q_M^{k−2} f²`, and `∫ f² = 2π/M`.
* `norm_tails_le`: the Gaussian side beyond `±π/M`, by `Tails`.
-/

open Real Complex MeasureTheory Set

@[expose] public section

namespace ArcsAlgo.LLT

/-- The oscillating factor `e^{−itθ}`. -/
noncomputable def eph (t θ : ℝ) : ℂ := cexp (-(I * t * θ))

lemma norm_eph (t θ : ℝ) : ‖eph t θ‖ = 1 := by
  rw [eph, Complex.norm_exp]; simp

lemma gk_eq (a t θ : ℝ) : gk a t θ = ((Real.exp (-a * θ ^ 2) : ℝ) : ℂ) * eph t θ := by
  rw [gk, eph, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The lattice side: `f(θ)^k e^{−itθ}`. -/
noncomputable def PhiB (M k : ℕ) (t θ : ℝ) : ℂ := ((fC M θ ^ k : ℝ) : ℂ) * eph t θ

/-- The Gaussian side with the first Edgeworth term: `e^{−aθ²}(1 + Bθ⁴) e^{−itθ}`. -/
noncomputable def PsiB (a B t θ : ℝ) : ℂ := gk a t θ + (B : ℂ) * ((θ : ℂ) ^ 4 * gk a t θ)

lemma PsiB_eq (a B t θ : ℝ) :
    PsiB a B t θ = ((Real.exp (-a * θ ^ 2) * (1 + B * θ ^ 4) : ℝ) : ℂ) * eph t θ := by
  rw [PsiB, gk_eq]; push_cast; ring

lemma norm_PsiB_le (a B t θ : ℝ) :
    ‖PsiB a B t θ‖ ≤ Real.exp (-a * θ ^ 2) + |B| * (θ ^ 4 * Real.exp (-a * θ ^ 2)) := by
  rw [PsiB_eq, norm_mul, norm_eph, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have : |1 + B * θ ^ 4| ≤ 1 + |B| * θ ^ 4 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ θ ^ 4)]
  nlinarith [Real.exp_pos (-a * θ ^ 2)]

lemma integrable_PsiB {a : ℝ} (ha : 0 < a) (B t : ℝ) : Integrable (PsiB a B t) := by
  have h0 : Integrable (gk a t) := by simpa using integrable_pow_mul_gk ha t 0
  exact h0.add ((integrable_pow_mul_gk ha t 4).const_mul _)

lemma integral_PsiB {a : ℝ} (ha : 0 < a) (B t : ℝ) :
    ∫ θ, PsiB a B t θ = G a t 0 + B * G a t 4 := by
  have h0 : Integrable (gk a t) := by simpa using integrable_pow_mul_gk ha t 0
  unfold PsiB
  rw [integral_add h0 ((integrable_pow_mul_gk ha t 4).const_mul _), integral_const_mul]
  simp [G]

lemma continuous_fC (M : ℕ) : Continuous (fC M) := by unfold fC; fun_prop

lemma continuous_PhiB (M k : ℕ) (t : ℝ) : Continuous (PhiB M k t) := by
  have := continuous_fC M
  unfold PhiB eph; fun_prop

/-- The tails: `‖∫_{θ₀}^∞ Ψ‖` and `‖∫_{−∞}^{−θ₀} Ψ‖` are both `≤ T`. -/
lemma norm_tails_le {a θ0 : ℝ} (ha : 0 < a) (h0 : 0 < θ0) (B t : ℝ) :
    ‖∫ θ in Ioi θ0, PsiB a B t θ‖ ≤ Real.exp (-a * θ0 ^ 2) / (2 * a * θ0) + |B| *
        (Real.exp (-a * θ0 ^ 2) * (θ0 ^ 3 / (2 * a) + 3 * θ0 / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ0))) ∧
    ‖∫ θ in Iic (-θ0), PsiB a B t θ‖ ≤ Real.exp (-a * θ0 ^ 2) / (2 * a * θ0) + |B| *
        (Real.exp (-a * θ0 ^ 2) * (θ0 ^ 3 / (2 * a) + 3 * θ0 / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ0))) := by
  have hA : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2)) (Ioi θ0) := by
    simpa using integrableOn_pow_mul_exp ha 0 (Ioi θ0)
  have hB : IntegrableOn (fun θ : ℝ => θ ^ 4 * Real.exp (-a * θ ^ 2)) (Ioi θ0) :=
    integrableOn_pow_mul_exp ha 4 (Ioi θ0)
  have hg : IntegrableOn (fun θ : ℝ => Real.exp (-a * θ ^ 2) + |B| * (θ ^ 4 * Real.exp (-a * θ ^ 2)))
      (Ioi θ0) := hA.add (hB.const_mul _)
  have hint : ∫ θ in Ioi θ0, (Real.exp (-a * θ ^ 2) + |B| * (θ ^ 4 * Real.exp (-a * θ ^ 2))) ≤
      Real.exp (-a * θ0 ^ 2) / (2 * a * θ0) + |B| *
        (Real.exp (-a * θ0 ^ 2) * (θ0 ^ 3 / (2 * a) + 3 * θ0 / (4 * a ^ 2) + 3 / (8 * a ^ 3 * θ0))) := by
    rw [integral_add hA (hB.const_mul _), integral_const_mul]
    exact add_le_add (integral_Ioi_exp_le ha h0)
      (mul_le_mul_of_nonneg_left (integral_Ioi_pow_four_exp_le ha h0) (abs_nonneg _))
  constructor
  · refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun θ => ?_)).trans hint
    exact norm_PsiB_le a B t θ
  · rw [← integral_comp_neg_Ioi]
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun θ => ?_)).trans hint
    exact le_of_le_of_eq (norm_PsiB_le a B t (-θ)) (by ring_nf)

/-- The middle range: `‖∫_{−π}^{−θ₀} Φ‖ + ‖∫_{θ₀}^{π} Φ‖ ≤ q_M^{k−2} (2π/M)`. -/
lemma norm_mid_le {M : ℕ} (hM : 2 ≤ M) {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    ‖∫ θ in (-π)..(-(π / M)), PhiB M k t θ‖ + ‖∫ θ in (π / M)..π, PhiB M k t θ‖ ≤
      qM M ^ (k - 2) * (2 * π / M) := by
  have hπ := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hθ0 : 0 < π / M := by positivity
  have hθπ : π / M ≤ π := div_le_self hπ.le (by linarith)
  have hq := (qM_pos hM).le
  have hpt : ∀ θ : ℝ, π / M ≤ |θ| → |θ| ≤ π → ‖PhiB M k t θ‖ ≤ qM M ^ (k - 2) * fC M θ ^ 2 := by
    intro θ h1 h2
    rw [PhiB, norm_mul, norm_eph, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_pow,
      show k = (k - 2) + 2 by omega, pow_add, Nat.add_sub_cancel, sq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (abs_fC_le hM h1 h2) _)
      (sq_nonneg _)
  have hcont : Continuous fun θ => qM M ^ (k - 2) * fC M θ ^ 2 := by
    have := continuous_fC M; fun_prop
  have hR : ‖∫ θ in (π / M)..π, PhiB M k t θ‖ ≤ ∫ θ in (π / M)..π, qM M ^ (k - 2) * fC M θ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hθπ
    · refine Filter.Eventually.of_forall fun θ hθ => hpt θ ?_ ?_
      · rw [abs_of_pos (lt_trans hθ0 hθ.1)]; exact hθ.1.le
      · rw [abs_of_pos (lt_trans hθ0 hθ.1)]; exact hθ.2
    · exact hcont.intervalIntegrable _ _
  have hL : ‖∫ θ in (-π)..(-(π / M)), PhiB M k t θ‖ ≤
      ∫ θ in (-π)..(-(π / M)), qM M ^ (k - 2) * fC M θ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall fun θ hθ => hpt θ ?_ ?_
      · rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.2]
      · rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.1]
    · exact hcont.intervalIntegrable _ _
  have hsplit : ∫ θ in (-π)..π, fC M θ ^ 2 = (∫ θ in (-π)..(-(π / M)), fC M θ ^ 2) +
      (∫ θ in (-(π / M))..(π / M), fC M θ ^ 2) + ∫ θ in (π / M)..π, fC M θ ^ 2 := by
    have hc : Continuous fun θ => fC M θ ^ 2 := by have := continuous_fC M; fun_prop
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hmid : 0 ≤ ∫ θ in (-(π / M))..(π / M), fC M θ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  rw [intervalIntegral.integral_const_mul] at hR hL
  have htot := integral_fC_sq (M := M) (by omega)
  rw [hsplit] at htot
  have := mul_le_mul_of_nonneg_left (show (∫ θ in (-π)..(-(π / M)), fC M θ ^ 2) +
    ∫ θ in (π / M)..π, fC M θ ^ 2 ≤ 2 * π / M by linarith) (pow_nonneg hq (k - 2))
  nlinarith

/-- The main range: `‖∫_{−θ₀}^{θ₀} (Φ − Ψ)‖ ≤ (B²/2) m₈(a) + 65ckσ⁶ m₆(β)`. -/
lemma norm_main_le {M : ℕ} (hM : 2 ≤ M) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    ‖∫ θ in (-(π / M))..(π / M), (PhiB M k t θ - PsiB (k * sig2 M / 2) (k * kap4 M / 24) t θ)‖ ≤
      (k * kap4 M / 24) ^ 2 / 2 * mom 8 (k * sig2 M / 2) +
        65 * cL * k * sig2 M ^ 3 * mom 6 (k * sig2 M * (1 / 2 - deltaL)) := by
  have hπ := Real.pi_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hs := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set a := (k : ℝ) * sig2 M / 2 with hadef
  set β := (k : ℝ) * sig2 M * (1 / 2 - deltaL) with hβdef
  have ha : 0 < a := by positivity
  have hβ : 0 < β := by
    have := deltaL_le; rw [hβdef]; apply mul_pos (by positivity); linarith
  set H : ℝ → ℝ := fun θ => (k * kap4 M / 24) ^ 2 / 2 * (θ ^ 8 * Real.exp (-a * θ ^ 2)) +
    65 * cL * k * sig2 M ^ 3 * (θ ^ 6 * Real.exp (-β * θ ^ 2)) with hHdef
  have hH8 : Integrable fun θ : ℝ => θ ^ 8 * Real.exp (-a * θ ^ 2) := by
    simpa using (integrableOn_pow_mul_exp ha 8 univ)
  have hH6 : Integrable fun θ : ℝ => θ ^ 6 * Real.exp (-β * θ ^ 2) := by
    simpa using (integrableOn_pow_mul_exp hβ 6 univ)
  have hHint : Integrable H := (hH8.const_mul _).add (hH6.const_mul _)
  have hH0 : ∀ θ, 0 ≤ H θ := fun θ => by simp only [hHdef]; unfold cL; positivity
  have hθ0 : 0 < π / M := by positivity
  have h1 : ‖∫ θ in (-(π / M))..(π / M), (PhiB M k t θ - PsiB a (k * kap4 M / 24) t θ)‖ ≤
      ∫ θ in (-(π / M))..(π / M), H θ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall fun θ hθ => ?_
      have habs : |θ| ≤ π / M := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
      rw [PhiB, PsiB_eq, ← sub_mul, norm_mul, norm_eph, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      have := main_pointwise hM (k := k) habs
      refine this.trans (le_of_eq ?_)
      simp only [hHdef, hadef, hβdef]; ring
    · exact hHint.intervalIntegrable
  have h2 : ∫ θ in (-(π / M))..(π / M), H θ ≤ ∫ θ, H θ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hHint (Filter.Eventually.of_forall hH0)
  have h3 : ∫ θ, H θ = (k * kap4 M / 24) ^ 2 / 2 * mom 8 a +
      65 * cL * k * sig2 M ^ 3 * mom 6 β := by
    simp only [hHdef]
    rw [integral_add (hH8.const_mul _) (hH6.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  linarith

end ArcsAlgo.LLT
