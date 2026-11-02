module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false

/-!
# Gaussian Fourier moments (paper §6.2, proof of Lemma B0′)

`G n = ∫ θⁿ e^{−aθ² − itθ} dθ`. Integration by parts (`G_rec`) gives
`2a G(n+2) = (n+1) G(n) − it G(n+1)`, so with `G 0 = √(π/a) e^{−t²/(4a)}` (`G_zero`)
`G 4 = G 0 · (3/(4a²) − 3t²/(4a³) + t⁴/(16a⁴))` (`G_four`): with `V = 2a` and `z = t/√V` this is
`G 0 · He₄(z)/V²`, the Fourier side of the first Edgeworth term.
-/

open Real Complex MeasureTheory

@[expose] public section

namespace ArcsAlgo.LLT

/-- The oscillating Gaussian `e^{−aθ² − itθ}`. -/
noncomputable def gk (a t : ℝ) (θ : ℝ) : ℂ := cexp (-(a : ℂ) * (θ : ℂ) ^ 2 - I * t * θ)

lemma norm_gk (a t θ : ℝ) : ‖gk a t θ‖ = Real.exp (-a * θ ^ 2) := by
  rw [gk, Complex.norm_exp]; congr 1; simp [Complex.sub_re, Complex.mul_re, sq]

lemma integrable_pow_mul_gk {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    Integrable fun θ : ℝ => (θ : ℂ) ^ n * gk a t θ := by
  have h : Integrable fun x : ℝ => x ^ (n : ℝ) * Real.exp (-a * x ^ 2) :=
    integrable_rpow_mul_exp_neg_mul_sq ha (by have := n.cast_nonneg (α := ℝ); linarith)
  simp_rw [Real.rpow_natCast] at h
  refine h.norm.mono' (by unfold gk; fun_prop) (Filter.Eventually.of_forall fun θ => ?_)
  rw [norm_mul, norm_gk, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_pow]

lemma hasDerivAt_gk (a t θ : ℝ) :
    HasDerivAt (gk a t) ((-2 * a * θ - I * t) * gk a t θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * θ) θ := by
    simpa using (hasDerivAt_pow 2 (θ : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id (θ : ℂ)).comp_ofReal
  have h : HasDerivAt (fun x : ℝ => -(a : ℂ) * (x : ℂ) ^ 2 - I * t * x)
      (-(a : ℂ) * (2 * θ) - I * t * 1) θ := (h1.const_mul _).sub (h2.const_mul _)
  change HasDerivAt (fun x : ℝ => cexp (-(a : ℂ) * (x : ℂ) ^ 2 - I * t * x)) _ θ
  convert h.cexp using 1
  simp only [gk]; ring

lemma hasDerivAt_pow_mul_gk (a t θ : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (n + 1) * gk a t x)
      ((n + 1) * ((θ : ℂ) ^ n * gk a t θ) - 2 * a * ((θ : ℂ) ^ (n + 2) * gk a t θ)
        - I * t * ((θ : ℂ) ^ (n + 1) * gk a t θ)) θ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (n + 1)) ((n + 1 : ℕ) * (θ : ℂ) ^ n) θ := by
    simpa using (hasDerivAt_pow (n + 1) (θ : ℂ)).comp_ofReal
  convert h1.mul (hasDerivAt_gk a t θ) using 1
  push_cast; ring

/-- `G n = ∫ θⁿ e^{−aθ² − itθ}`. -/
noncomputable def G (a t : ℝ) (n : ℕ) : ℂ := ∫ θ : ℝ, (θ : ℂ) ^ n * gk a t θ

/-- Integration by parts: `2a G(n+2) = (n+1) G(n) − it G(n+1)`. -/
lemma G_rec {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    2 * (a : ℂ) * G a t (n + 2) = (n + 1) * G a t n - I * t * G a t (n + 1) := by
  have i0 := integrable_pow_mul_gk ha t n
  have i1 := integrable_pow_mul_gk ha t (n + 1)
  have i2 := integrable_pow_mul_gk ha t (n + 2)
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_pow_mul_gk a t · n)
    (((i0.const_mul ((n : ℂ) + 1)).sub (i2.const_mul (2 * (a : ℂ)))).sub (i1.const_mul (I * t))) i1
  have hAB : Integrable (fun x : ℝ => ((n : ℂ) + 1) * ((x : ℂ) ^ n * gk a t x)
      - 2 * (a : ℂ) * ((x : ℂ) ^ (n + 2) * gk a t x)) := (i0.const_mul _).sub (i2.const_mul _)
  rw [integral_sub hAB (i1.const_mul _), integral_sub (i0.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  simp only [G]; linear_combination -hi

lemma G_one {a : ℝ} (ha : 0 < a) (t : ℝ) : 2 * (a : ℂ) * G a t 1 = -I * t * G a t 0 := by
  have i0 := integrable_pow_mul_gk ha t 0
  have i1 := integrable_pow_mul_gk ha t 1
  have hd : ∀ θ : ℝ, HasDerivAt (gk a t)
      (-2 * a * ((θ : ℂ) ^ 1 * gk a t θ) - I * t * ((θ : ℂ) ^ 0 * gk a t θ)) θ := by
    intro θ; convert hasDerivAt_gk a t θ using 1; ring
  have i0' : Integrable (gk a t) := by simpa using i0
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable hd
    ((i1.const_mul (-2 * (a : ℂ))).sub (i0.const_mul (I * t))) i0'
  rw [integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul] at hi
  simp only [G, pow_one, pow_zero, one_mul] at hi ⊢; linear_combination -hi

lemma G_zero {a : ℝ} (ha : 0 < a) (t : ℝ) :
    G a t 0 = ((π / a : ℝ) : ℂ) ^ (1 / 2 : ℂ) * cexp (-(t : ℂ) ^ 2 / (4 * a)) := by
  have h := integral_cexp_quadratic (b := -(a : ℂ)) (c := -I * t) (d := 0)
    (by simp [ha]) 
  simp only [G, pow_zero, one_mul, gk]
  convert h using 2
  · funext θ; congr 1; ring
  · rw [neg_neg, Complex.ofReal_div]
  · congr 1
    ring_nf; rw [Complex.I_sq]; ring

/-- The fourth moment: `G 4 = G 0 · (3/(4a²) − 3t²/(4a³) + t⁴/(16a⁴))`. -/
lemma G_four {a : ℝ} (ha : 0 < a) (t : ℝ) :
    G a t 4 = G a t 0 * (3 / (4 * a ^ 2) - 3 * t ^ 2 / (4 * a ^ 3) + t ^ 4 / (16 * a ^ 4)) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h1 := G_one ha t
  have h2 := G_rec ha t 0
  have h3 := G_rec ha t 1
  have h4 := G_rec ha t 2
  have e1 : G a t 1 = -I * t * G a t 0 / (2 * a) := by field_simp; linear_combination h1
  have e2 : G a t 2 = (G a t 0 - I * t * G a t 1) / (2 * a) := by
    field_simp; push_cast at h2; linear_combination h2
  have e3 : G a t 3 = (2 * G a t 1 - I * t * G a t 2) / (2 * a) := by
    field_simp; push_cast at h3; linear_combination h3
  have e4 : G a t 4 = (3 * G a t 2 - I * t * G a t 3) / (2 * a) := by
    field_simp; push_cast at h4; linear_combination h4
  rw [e4, e3, e2, e1]
  field_simp
  ring_nf
  rw [Complex.I_sq, show I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num]
  ring

end ArcsAlgo.LLT
