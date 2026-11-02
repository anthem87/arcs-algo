module

public import ArcsAlgo.EdgeFactor
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Shift
set_option autoImplicit false

/-!
# Theorem E(2), the vanishing factor: `(e^x − 1)/x` (paper §3.5)

If `𝒱(a/q) = {w}`, then `1 + e(wθ) = −iwt·g(iwt)` with `t = 2π(θ − a/q)` and
`g(x) = (e^x − 1)/x`, `g(iwt) = e^{iwt/2} sinc(wt/2)` (`mul_gS`, `gS_I_mul`).

* `gS`, `psiS = log g`: `|g(x) − 1| ≤ 3|x|/4`, `|ψ(x)| ≤ 9|x|/8` for `|x| ≤ 2/3`.
* `taylor_tail_c`: Taylor's remainder at any centre (Cauchy's estimates).
* `gS_expand`: `g(x₀ + z) = g(x₀) exp(Σ_{1≤n≤5} ψ^{(n)}(x₀)zⁿ/n! + R)`, `|R| ≤ (4|z|)⁶`.
* `psiS_d1` … `psiS_d5`: `ψ^{(n)}(0) = 1/2, 1/12, 0, −1/120, 0` (from the doubling identity
  `g(x) = ((1 + e^{x/2})/2) g(x/2)`, the Bernoulli cumulants `c_n(1/2)` and `coeff_zero_of_bound`).
* `lamS w t* n = wⁿψ^{(n)}(iwt*)`: the exact cumulants of `e^{iwt/2} sinc(wt/2)` at `t*`.
* `lamS_close`: for `w|t*| ≤ 1/12` and `w²|t*| ≤ 1` they are `w/2, w²/12, 0, −w⁴/120` up to
  `10⁵·w²|t*|(1 + w²)` (the corrected parenthetical of Theorem E(2)).
* `psiS_d2_real`: `ψ″(iv)` is real (`ψ(z̄) = conj ψ(z)`, `ψ(−z) = ψ(z) − z`), so `κ₂` of the factor is real.

No hypothesis.
-/

open Finset Complex Nat Metric
open scoped Real ComplexConjugate

@[expose] public section

namespace ArcsAlgo.Edge

/-! ### The vanishing factor `(e^x − 1)/x` -/

/-- `g(x) = (e^x − 1)/x`, `g(0) = 1`; `g(iwt) = e^{iwt/2} sinc(wt/2)`. -/
noncomputable def gS (z : ℂ) : ℂ := dslope (fun z => Complex.exp z - 1) 0 z

theorem mul_gS (z : ℂ) : z * gS z = Complex.exp z - 1 := by
  have := sub_smul_dslope (fun z => Complex.exp z - 1) 0 z
  simpa [gS] using this

theorem gS_zero : gS 0 = 1 := by
  unfold gS; rw [dslope_same]
  have : HasDerivAt (fun z => Complex.exp z - 1) (Complex.exp 0) 0 := (Complex.hasDerivAt_exp 0).sub_const 1
  rw [this.deriv, Complex.exp_zero]

theorem gS_of_ne {z : ℂ} (hz : z ≠ 0) : gS z = (Complex.exp z - 1) / z := by
  rw [← mul_gS z]; field_simp

theorem differentiable_gS : Differentiable ℂ gS := by
  have h := (differentiableOn_dslope (f := fun z => Complex.exp z - 1) (s := Set.univ) (c := 0)
    Filter.univ_mem).mpr (by fun_prop)
  exact fun z => (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem

/-- `g(iwt) = e^{iwt/2} sinc(wt/2)`, `sinc u = sin u / u`. -/
theorem gS_I_mul {x : ℝ} (hx : x ≠ 0) :
    gS (I * x) = Complex.exp (I * x / 2) * (Complex.sin (x / 2) / (x / 2)) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [gS_of_ne (mul_ne_zero I_ne_zero hx'), Complex.sin, show I * (x : ℂ) = 2 * (I * x / 2) by ring,
    show Complex.exp (2 * (I * x / 2)) = Complex.exp (I * x / 2) ^ 2 by rw [← Complex.exp_nat_mul]; norm_num]
  rw [show -((x : ℂ) / 2) * I = -(I * x / 2) by ring, show (x : ℂ) / 2 * I = I * x / 2 by ring, Complex.exp_neg]
  have he : Complex.exp (I * x / 2) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring_nf
  rw [I_sq]; ring

theorem norm_gS_sub_one {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖gS z - 1‖ ≤ 3 / 4 * ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [gS_zero]
  have hb := Complex.exp_bound hz (n := 2) (by norm_num)
  have e : gS z - 1 = (Complex.exp z - ∑ m ∈ range 2, z ^ m / (m ! : ℂ)) / z := by
    rw [gS_of_ne hz0]; simp [sum_range_succ]; field_simp; ring
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [e, norm_div, div_le_iff₀ hn]
  refine hb.trans (le_of_eq ?_)
  simp [Nat.factorial]; ring

theorem gS_re_pos {z : ℂ} (hz : ‖z‖ < 2 / 3) : 0 < (gS z).re := by
  have h := norm_gS_sub_one (z := z) (by linarith)
  have h1 : |(gS z - 1).re| ≤ ‖gS z - 1‖ := Complex.abs_re_le_norm _
  have : (gS z - 1).re = (gS z).re - 1 := by simp
  rw [this] at h1
  have := abs_le.mp h1
  nlinarith

theorem gS_slit {z : ℂ} (hz : ‖z‖ < 2 / 3) : gS z ∈ slitPlane := Or.inl (gS_re_pos hz)

/-- `ψ(x) = log((e^x − 1)/x)`: the cumulant generating function of `Uniform[0, 1]`. -/
noncomputable def psiS (z : ℂ) : ℂ := Complex.log (gS z)

theorem exp_psiS {z : ℂ} (hz : ‖z‖ < 2 / 3) : Complex.exp (psiS z) = gS z :=
  Complex.exp_log (slitPlane_ne_zero (gS_slit hz))

theorem psiS_zero : psiS 0 = 0 := by simp [psiS, gS_zero]

theorem differentiableOn_psiS : DifferentiableOn ℂ psiS (ball 0 (2 / 3)) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  exact ((differentiable_gS z).clog (gS_slit hz)).differentiableWithinAt

theorem norm_psiS_le {z : ℂ} (hz : ‖z‖ ≤ 2 / 3) : ‖psiS z‖ ≤ 9 / 8 * ‖z‖ := by
  have h := norm_gS_sub_one (z := z) (by linarith)
  have h2 : ‖gS z - 1‖ ≤ 1 / 2 := by linarith
  have := Complex.norm_log_one_add_half_le_self h2
  rw [add_sub_cancel] at this
  unfold psiS; linarith

/-- **Taylor's remainder at a centre `c`** (as `taylor_tail`). -/
theorem taylor_tail_c {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c (2 * R))) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (K : ℕ) {z : ℂ}
    (hz : ‖z - c‖ ≤ R / 2) :
    ‖f z - ∑ n ∈ range K, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n‖ ≤
      2 * M * (‖z - c‖ / R) ^ K := by
  have hM0 : 0 ≤ M := by
    have := hM (c + R) (by simp [abs_of_pos hR]); exact le_trans (norm_nonneg _) this
  have hzb : z ∈ ball c (2 * R) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hf hzb
  set g : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n with hg
  have hs' : HasSum g (f z) := by
    convert hs using 1; ext n; simp only [hg, smul_eq_mul]; ring
  have htail := (hasSum_nat_add_iff' K).mpr hs'
  have hdc : DiffContOnCl ℂ f (ball c R) :=
    hf.diffContOnCl_ball (closedBall_subset_ball (by linarith))
  set r := ‖z - c‖ / R with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ hR]; linarith
  have hbound : ∀ n, ‖g (n + K)‖ ≤ M * r ^ K * r ^ n := by
    intro n
    have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n + K) hR hdc hM
    simp only [hg, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hf0 : (0 : ℝ) < ((n + K) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((n + K) ! : ℝ)⁻¹ * ‖iteratedDeriv (n + K) f c‖ * ‖z - c‖ ^ (n + K)
        ≤ ((n + K) ! : ℝ)⁻¹ * (((n + K) ! : ℝ) * M / R ^ (n + K)) * ‖z - c‖ ^ (n + K) := by gcongr
      _ = M * r ^ K * r ^ n := by
          rw [hr, div_pow, div_pow]; field_simp; ring
  have hgeo : HasSum (fun n => M * r ^ K * r ^ n) (M * r ^ K * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have := htail.norm_le_of_bounded hgeo hbound
  calc ‖f z - ∑ n ∈ range K, g n‖ ≤ M * r ^ K * (1 - r)⁻¹ := this
    _ ≤ M * r ^ K * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    _ = 2 * M * r ^ K := by ring

/-- **The vanishing factor, expanded**: for `|x₀| ≤ 1/6`, `|z| ≤ 1/8`,
`g(x₀ + z) = g(x₀) exp(Σ_{1≤n≤5} ψ^{(n)}(x₀) z^n/n! + R)`, `|R| ≤ (4|z|)⁶`. -/
theorem gS_expand {x₀ z : ℂ} (hx₀ : ‖x₀‖ ≤ 1 / 6) (hz : ‖z‖ ≤ 1 / 8) :
    ∃ R : ℂ, ‖R‖ ≤ (4 * ‖z‖) ^ 6 ∧
      gS (x₀ + z) = gS x₀ * Complex.exp (∑ n ∈ range 6, (n ! : ℂ)⁻¹ * iteratedDeriv n psiS x₀ * z ^ n -
        psiS x₀ + R) := by
  have hdiff : DifferentiableOn ℂ psiS (ball x₀ (2 * (1 / 4))) := by
    refine differentiableOn_psiS.mono fun y hy => ?_
    rw [mem_ball, dist_eq_norm] at hy; rw [mem_ball, dist_zero_right]
    have := norm_sub_norm_le y x₀; linarith
  have hM : ∀ y ∈ sphere x₀ (1 / 4), ‖psiS y‖ ≤ 1 / 2 := by
    intro y hy
    rw [mem_sphere, dist_eq_norm] at hy
    have h1 : ‖y‖ ≤ 5 / 12 := by have := norm_le_insert' y x₀; linarith
    have := norm_psiS_le (z := y) (by linarith); linarith
  have ht := taylor_tail_c (by norm_num : (0 : ℝ) < 1 / 4) hdiff hM 6 (z := x₀ + z)
    (by rw [add_sub_cancel_left]; linarith)
  rw [add_sub_cancel_left] at ht
  set S := ∑ n ∈ range 6, (n ! : ℂ)⁻¹ * iteratedDeriv n psiS x₀ * z ^ n
  refine ⟨psiS (x₀ + z) - S, ?_, ?_⟩
  · refine ht.trans (le_of_eq ?_); rw [div_pow]; ring_nf
  · have h1 : ‖x₀ + z‖ < 2 / 3 := by have := norm_add_le x₀ z; linarith
    have h0 : ‖x₀‖ < 2 / 3 := by linarith
    rw [show S - psiS x₀ + (psiS (x₀ + z) - S) = psiS (x₀ + z) + -psiS x₀ by ring, Complex.exp_add,
      exp_psiS h1, Complex.exp_neg, exp_psiS h0]
    have : gS x₀ ≠ 0 := slitPlane_ne_zero (gS_slit h0)
    field_simp


/-! ### `ψ^{(n)}(0)` -/

/-- A finite sum `Σ_{n<K} d_n x^n` that is `O(x^K)` as `x → 0⁺` vanishes identically. -/
theorem coeff_zero_of_bound : ∀ (K : ℕ) (d : ℕ → ℂ) {r C : ℝ}, 0 < r →
    (∀ x : ℝ, 0 < x → x ≤ r → ‖∑ n ∈ range K, d n * (x : ℂ) ^ n‖ ≤ C * x ^ K) → ∀ n < K, d n = 0
  | 0, _, _, _, _, _ => fun n hn => absurd hn (Nat.not_lt_zero n)
  | K + 1, d, r, C, hr, h => by
    set A := ∑ n ∈ range K, ‖d (n + 1)‖
    have hA : 0 ≤ A := sum_nonneg fun _ _ => norm_nonneg _
    have hsplit : ∀ x : ℝ, ∑ n ∈ range (K + 1), d n * (x : ℂ) ^ n =
        d 0 + x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n := by
      intro x; rw [sum_range_succ', mul_sum]; simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm]; congr 1; refine sum_congr rfl fun n _ => by ring
    have hin : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n‖ ≤ A := by
      intro x hx0 hx1
      refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hx0.le hx1)
    -- `d 0 = 0`
    have hd0 : d 0 = 0 := by
      by_contra hne
      have hpos : 0 < ‖d 0‖ := norm_pos_iff.mpr hne
      set x := min (min r 1) (‖d 0‖ / (2 * (A + |C| + 1)))
      have hx0 : 0 < x := lt_min (lt_min hr one_pos) (by positivity)
      have hx1 : x ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
      have hxr : x ≤ r := (min_le_left _ _).trans (min_le_left _ _)
      have hxd : x ≤ ‖d 0‖ / (2 * (A + |C| + 1)) := min_le_right _ _
      have h1 := h x hx0 hxr
      rw [hsplit] at h1
      have h2 : ‖d 0‖ ≤ ‖d 0 + x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n‖ + x * A := by
        have e : d 0 = (d 0 + x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n) -
            x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n := by ring
        have := norm_sub_le (d 0 + x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n)
          (x * ∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n)
        rw [← e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at this
        have := mul_le_mul_of_nonneg_left (hin x hx0 hx1) hx0.le
        linarith
      have h3 : C * x ^ (K + 1) ≤ |C| * x := by
        have : x ^ (K + 1) ≤ x := by
          calc x ^ (K + 1) = x ^ K * x := pow_succ _ _
            _ ≤ 1 * x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0.le hx1) hx0.le
            _ = x := one_mul x
        calc C * x ^ (K + 1) ≤ |C| * x ^ (K + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          _ ≤ |C| * x := mul_le_mul_of_nonneg_left this (abs_nonneg C)
      have h4 : ‖d 0‖ ≤ x * (A + |C|) := by nlinarith
      have h5 : x * (A + |C|) < ‖d 0‖ := by
        have hden : 0 < 2 * (A + |C| + 1) := by positivity
        have := mul_le_mul_of_nonneg_right hxd (by positivity : (0 : ℝ) ≤ A + |C|)
        have e : ‖d 0‖ / (2 * (A + |C| + 1)) * (A + |C|) < ‖d 0‖ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]; nlinarith [abs_nonneg C]
        linarith
      linarith
    -- the rest, divided by `x`
    have hrest := coeff_zero_of_bound K (fun n => d (n + 1)) hr (C := C) (fun x hx0 hxr => by
      have h1 := h x hx0 hxr
      rw [hsplit, hd0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, pow_succ] at h1
      have : x * ‖∑ n ∈ range K, d (n + 1) * (x : ℂ) ^ n‖ ≤ x * (C * x ^ K) := by linarith
      exact le_of_mul_le_mul_left this hx0)
    intro n hn
    rcases n with _ | n
    · exact hd0
    · exact hrest n (by omega)

/-- The doubling identity `(e^x − 1)/x = ((1 + e^{x/2})/2)·(e^{x/2} − 1)/(x/2)`. -/
theorem gS_double (x : ℂ) : gS x = (1 + 1 / 2 * (Complex.exp (x / 2) - 1)) * gS (x / 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [gS_zero]
  have hx2 : x / 2 ≠ 0 := div_ne_zero hx two_ne_zero
  rw [gS_of_ne hx, gS_of_ne hx2]
  have e : Complex.exp x = Complex.exp (x / 2) ^ 2 := by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]; field_simp; ring

theorem abs_arg_lt_of_re_pos {u : ℂ} (hu : 0 < u.re) : |u.arg| < π / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)

/-- `ψ(x) = ψ_{1/2}(x/2) + ψ(x/2)` for `|x| ≤ 1/8` (`ψ_p` the Bernoulli cumulant function). -/
theorem psiS_double {x : ℂ} (hx : ‖x‖ ≤ 1 / 8) : psiS x = psiB (1 / 2) (x / 2) + psiS (x / 2) := by
  have hx2 : ‖x / 2‖ ≤ 1 / 16 := by rw [norm_div, Complex.norm_ofNat]; linarith
  have hb := psiB_expand (p := 1 / 2) (K := 1) le_rfl (by norm_num) (x := x / 2) (by norm_num; linarith)
  unfold psiS
  rw [gS_double x]
  set u := 1 + 1 / 2 * (Complex.exp (x / 2) - 1)
  have hu : 0 < u.re := by
    have h1 : ‖(1 / 2 : ℂ) * (Complex.exp (x / 2) - 1)‖ ≤ 1 / 2 := by
      have := Complex.norm_exp_sub_one_le (x := x / 2) (by linarith)
      rw [norm_mul]; norm_num; linarith
    have h2 := Complex.abs_re_le_norm ((1 / 2 : ℂ) * (Complex.exp (x / 2) - 1))
    simp only [u, Complex.add_re, Complex.one_re]
    have := abs_le.mp (h2.trans h1); linarith
  have hg : 0 < (gS (x / 2)).re := gS_re_pos (by linarith)
  rw [Complex.log_mul (by intro h; rw [h] at hu; simp at hu) (by intro h; rw [h] at hg; simp at hg)]
  · rfl
  · have := abs_arg_lt_of_re_pos hu; have := abs_arg_lt_of_re_pos hg
    constructor <;> [skip; skip] <;> (have := abs_lt.mp ‹|u.arg| < π / 2›; have := abs_lt.mp ‹|(gS (x / 2)).arg| < π / 2›; linarith [Real.pi_pos])


theorem psiS_taylor0 {y : ℂ} (hy : ‖y‖ ≤ 1 / 6) :
    ‖psiS y - ∑ n ∈ range 6, (n ! : ℂ)⁻¹ * iteratedDeriv n psiS 0 * y ^ n‖ ≤ 3 / 4 * (3 * ‖y‖) ^ 6 := by
  have hd : DifferentiableOn ℂ psiS (ball 0 (2 * (1 / 3))) := by
    convert differentiableOn_psiS using 2; norm_num
  have hM : ∀ z ∈ sphere (0 : ℂ) (1 / 3), ‖psiS z‖ ≤ 3 / 8 := by
    intro z hz; rw [mem_sphere, dist_zero_right] at hz
    have := norm_psiS_le (z := z) (by linarith); linarith
  have := taylor_tail (by norm_num : (0 : ℝ) < 1 / 3) hd hM 6 (z := y) (by linarith)
  refine this.trans (le_of_eq ?_); rw [div_pow]; ring_nf

/-- The Taylor coefficients `a_n = ψ^{(n)}(0)/n!` satisfy `a_n(1 − 2^{−n}) = c_n(1/2)/2^n`. -/
theorem psiS_coeffs : ∀ n < 6,
    (n ! : ℂ)⁻¹ * iteratedDeriv n psiS 0 * (1 - 1 / 2 ^ n) - cB (1 / 2) n / 2 ^ n = 0 := by
  refine coeff_zero_of_bound 6 _ (r := 1 / 16)
    (C := 3 / 4 * 3 ^ 6 + 3 / 4 * (3 / 2) ^ 6 + 2 * 4 ^ 6) (by norm_num) fun x hx0 hxr => ?_
  set a : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * iteratedDeriv n psiS 0
  have hxn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hx2n : ‖(x : ℂ) / 2‖ = x / 2 := by rw [norm_div, hxn, Complex.norm_ofNat]
  have h1 := psiS_taylor0 (y := (x : ℂ)) (by rw [hxn]; linarith)
  have h2 := psiS_taylor0 (y := (x : ℂ) / 2) (by rw [hx2n]; linarith)
  have h3 := (psiB_expand (p := 1 / 2) (K := 1) le_rfl (by norm_num) (x := (x : ℂ) / 2)
    (by rw [hx2n]; linarith)).2
  have hd := psiS_double (x := (x : ℂ)) (by rw [hxn]; linarith)
  rw [hxn] at h1; rw [hx2n] at h2 h3
  have e : ∑ n ∈ range 6, (a n * (1 - 1 / 2 ^ n) - cB (1 / 2) n / 2 ^ n) * (x : ℂ) ^ n =
      (psiB (1 / 2) ((x : ℂ) / 2) - ∑ n ∈ range 6, cB (1 / 2) n * ((x : ℂ) / 2) ^ n) +
      (psiS ((x : ℂ) / 2) - ∑ n ∈ range 6, a n * ((x : ℂ) / 2) ^ n) -
      (psiS x - ∑ n ∈ range 6, a n * (x : ℂ) ^ n) := by
    rw [hd]; simp only [sum_range_succ, sum_range_zero]; ring
  rw [e]
  have n1 := norm_sub_le ((psiB (1 / 2) ((x : ℂ) / 2) - ∑ n ∈ range 6, cB (1 / 2) n * ((x : ℂ) / 2) ^ n) +
      (psiS ((x : ℂ) / 2) - ∑ n ∈ range 6, a n * ((x : ℂ) / 2) ^ n))
    (psiS x - ∑ n ∈ range 6, a n * (x : ℂ) ^ n)
  have n2 := norm_add_le (psiB (1 / 2) ((x : ℂ) / 2) - ∑ n ∈ range 6, cB (1 / 2) n * ((x : ℂ) / 2) ^ n)
      (psiS ((x : ℂ) / 2) - ∑ n ∈ range 6, a n * ((x : ℂ) / 2) ^ n)
  have : 2 * (8 * 1 * (x / 2)) ^ 6 + 3 / 4 * (3 * (x / 2)) ^ 6 + 3 / 4 * (3 * x) ^ 6 =
      (3 / 4 * 3 ^ 6 + 3 / 4 * (3 / 2) ^ 6 + 2 * 4 ^ 6) * x ^ 6 := by ring
  linarith

/-- `ψ^{(n)}(0) = 1/2, 1/12, 0, −1/120, 0` for `n = 1, …, 5` (the cumulants of `Uniform[0, 1]`). -/
theorem psiS_d1 : iteratedDeriv 1 psiS 0 = 1 / 2 := by
  have := psiS_coeffs 1 (by norm_num); simp [cB] at this; rw [iteratedDeriv_one]; linear_combination 2 * this
theorem psiS_d2 : iteratedDeriv 2 psiS 0 = 1 / 12 := by
  have := psiS_coeffs 2 (by norm_num); simp [cB, Nat.factorial] at this; linear_combination 8 / 3 * this
theorem psiS_d3 : iteratedDeriv 3 psiS 0 = 0 := by
  have := psiS_coeffs 3 (by norm_num); simp [cB, Nat.factorial] at this
  rcases this with h | h
  · exact h
  · norm_num at h
theorem psiS_d4 : iteratedDeriv 4 psiS 0 = -1 / 120 := by
  have := psiS_coeffs 4 (by norm_num); simp [cB, Nat.factorial] at this; linear_combination 384 / 15 * this
theorem psiS_d5 : iteratedDeriv 5 psiS 0 = 0 := by
  have := psiS_coeffs 5 (by norm_num); simp [cB, Nat.factorial] at this
  rcases this with h | h
  · exact h
  · norm_num at h


/-! ### `ψ^{(n)}` near `0` (Cauchy's estimates) -/

theorem analyticOnNhd_psiS : AnalyticOnNhd ℂ psiS (ball 0 (2 / 3)) :=
  differentiableOn_psiS.analyticOnNhd isOpen_ball

theorem differentiableOn_dpsiS (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n psiS) (ball 0 (2 / 3)) := by
  rw [iteratedDeriv_eq_iterate]; exact (analyticOnNhd_psiS.iterated_deriv n).differentiableOn

/-- `|ψ^{(n)}(y)| ≤ n!(9/16)3^n` for `|y| ≤ 1/6`. -/
theorem norm_dpsiS_le (n : ℕ) {y : ℂ} (hy : ‖y‖ ≤ 1 / 6) :
    ‖iteratedDeriv n psiS y‖ ≤ n ! * (9 / 16) * 3 ^ n := by
  have hdc : DiffContOnCl ℂ psiS (ball y (1 / 3)) := by
    refine (differentiableOn_psiS.mono fun z hz => ?_).diffContOnCl_ball le_rfl
    rw [mem_closedBall, dist_eq_norm] at hz; rw [mem_ball, dist_zero_right]
    have := norm_le_insert' z y; linarith
  have hC : ∀ z ∈ sphere y (1 / 3), ‖psiS z‖ ≤ 9 / 16 := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz
    have := norm_le_insert' z y
    have := norm_psiS_le (z := z) (by linarith); linarith
  have := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num : (0 : ℝ) < 1 / 3) hdc hC
  refine this.trans (le_of_eq ?_)
  have e : (1 / 3 : ℝ) ^ n * 3 ^ n = 1 := by rw [← mul_pow]; norm_num
  field_simp; linarith

/-- First order: `|ψ^{(n)}(x) − ψ^{(n)}(0)| ≤ n!(27/2)3^n|x|` for `|x| ≤ 1/12`. -/
theorem dpsiS_near1 (n : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 1 / 12) :
    ‖iteratedDeriv n psiS x - iteratedDeriv n psiS 0‖ ≤ n ! * (27 / 4) * 3 ^ n * ‖x‖ := by
  have hd : DifferentiableOn ℂ (iteratedDeriv n psiS) (ball 0 (2 * (1 / 6))) :=
    (differentiableOn_dpsiS n).mono (ball_subset_ball (by norm_num))
  have hM : ∀ z ∈ sphere (0 : ℂ) (1 / 6), ‖iteratedDeriv n psiS z‖ ≤ n ! * (9 / 16) * 3 ^ n := by
    intro z hz; rw [mem_sphere, dist_zero_right] at hz; exact norm_dpsiS_le n hz.le
  have := taylor_tail_c (by norm_num : (0 : ℝ) < 1 / 6) hd hM 1 (z := x) (by rw [sub_zero]; linarith)
  simp only [sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero,
    sub_zero, pow_zero, mul_one, pow_one] at this
  refine this.trans (le_of_eq ?_); ring

/-- Second order: `|ψ^{(n)}(x) − ψ^{(n)}(0) − ψ^{(n+1)}(0)x| ≤ n!(81/2)3^n|x|²` for `|x| ≤ 1/12`. -/
theorem dpsiS_near2 (n : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 1 / 12) :
    ‖iteratedDeriv n psiS x - iteratedDeriv n psiS 0 - iteratedDeriv (n + 1) psiS 0 * x‖ ≤
      n ! * (81 / 2) * 3 ^ n * ‖x‖ ^ 2 := by
  have hd : DifferentiableOn ℂ (iteratedDeriv n psiS) (ball 0 (2 * (1 / 6))) :=
    (differentiableOn_dpsiS n).mono (ball_subset_ball (by norm_num))
  have hM : ∀ z ∈ sphere (0 : ℂ) (1 / 6), ‖iteratedDeriv n psiS z‖ ≤ n ! * (9 / 16) * 3 ^ n := by
    intro z hz; rw [mem_sphere, dist_zero_right] at hz; exact norm_dpsiS_le n hz.le
  have := taylor_tail_c (by norm_num : (0 : ℝ) < 1 / 6) hd hM 2 (z := x) (by rw [sub_zero]; linarith)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    one_mul, iteratedDeriv_zero, iteratedDeriv_one, sub_zero, pow_zero, mul_one, pow_one, zero_add] at this
  rw [← iteratedDeriv_succ] at this
  refine (le_of_eq (by ring_nf)).trans (this.trans (le_of_eq ?_)); ring

/-- The cumulants of the vanishing factor `e^{iwt/2} sinc(wt/2) = g(iwt)` at `t*`:
`λ_n = w^n ψ^{(n)}(iwt*)`. -/
noncomputable def lamS (w : ℕ) (ts : ℝ) (n : ℕ) : ℂ := (w : ℂ) ^ n * iteratedDeriv n psiS (I * w * ts)

theorem norm_Iwt (w : ℕ) (ts : ℝ) : ‖I * (w : ℂ) * ts‖ = w * |ts| := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]

/-- **The corrections**: for `w|t*| ≤ 1/12` and `w²|t*| ≤ 1`, the cumulants of the vanishing factor
at `t*` are `w/2, w²/12, 0, −w⁴/120` up to `C w²|t*|(1 + w²)`, `C = 10⁵`. -/
theorem lamS_close {w : ℕ} {ts : ℝ} (h1 : (w : ℝ) * |ts| ≤ 1 / 12) (h2 : (w : ℝ) ^ 2 * |ts| ≤ 1) :
    ‖lamS w ts 1 - w / 2‖ ≤ 10 ^ 5 * (w ^ 2 * |ts| * (1 + w ^ 2)) ∧
    ‖lamS w ts 2 - w ^ 2 / 12‖ ≤ 10 ^ 5 * (w ^ 2 * |ts| * (1 + w ^ 2)) ∧
    ‖lamS w ts 3‖ ≤ 10 ^ 5 * (w ^ 2 * |ts| * (1 + w ^ 2)) ∧
    ‖lamS w ts 4 + w ^ 4 / 120‖ ≤ 10 ^ 5 * (w ^ 2 * |ts| * (1 + w ^ 2)) := by
  set x := I * (w : ℂ) * ts
  have hx : ‖x‖ = w * |ts| := norm_Iwt w ts
  have hx12 : ‖x‖ ≤ 1 / 12 := by rw [hx]; exact h1
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have ht0 : 0 ≤ |ts| := abs_nonneg ts
  set u := (w : ℝ) ^ 2 * |ts| * (1 + w ^ 2)
  have hnw : ∀ k : ℕ, ‖(w : ℂ) ^ k‖ = (w : ℝ) ^ k := fun k => by rw [norm_pow, Complex.norm_natCast]
  -- `w^k‖x‖ ≤ u` for `k = 1, 3`, `w^k‖x‖² ≤ u` for `k = 2, 4`
  have e1 : (w : ℝ) * ‖x‖ ≤ u := by
    rw [hx]; simp only [u]; nlinarith [mul_nonneg (pow_nonneg hw0 2) ht0, pow_nonneg hw0 4]
  have e3 : (w : ℝ) ^ 3 * ‖x‖ ≤ u := by
    rw [hx]; simp only [u]
    have : (w : ℝ) ^ 3 * (w * |ts|) = w ^ 4 * |ts| := by ring
    rw [this]; nlinarith [mul_nonneg (pow_nonneg hw0 2) ht0]
  have e2 : (w : ℝ) ^ 2 * ‖x‖ ^ 2 ≤ u := by
    rw [hx]; simp only [u]
    have : (w : ℝ) ^ 2 * (w * |ts|) ^ 2 = (w ^ 2 * |ts|) * (w ^ 2 * |ts|) := by ring
    rw [this]
    have h0 : 0 ≤ (w : ℝ) ^ 2 * |ts| := by positivity
    nlinarith [pow_nonneg hw0 2]
  have e4 : (w : ℝ) ^ 4 * ‖x‖ ^ 2 ≤ u := by
    rw [hx]; simp only [u]
    have : (w : ℝ) ^ 4 * (w * |ts|) ^ 2 = (w ^ 2 * |ts|) * (w ^ 4 * |ts|) := by ring
    rw [this]
    have h0 : 0 ≤ (w : ℝ) ^ 4 * |ts| := by positivity
    nlinarith [mul_nonneg (pow_nonneg hw0 2) ht0]
  have hu0 : 0 ≤ u := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := dpsiS_near1 1 hx12
    rw [psiS_d1] at h
    have e : lamS w ts 1 - w / 2 = (w : ℂ) ^ 1 * (iteratedDeriv 1 psiS x - 1 / 2) := by
      unfold lamS; ring
    rw [e, norm_mul, hnw]
    calc (w : ℝ) ^ 1 * ‖iteratedDeriv 1 psiS x - 1 / 2‖ ≤ (w : ℝ) ^ 1 * (1 ! * (27 / 4) * 3 ^ 1 * ‖x‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 81 / 4 * (w * ‖x‖) := by simp; ring
      _ ≤ 10 ^ 5 * u := by nlinarith
  · have h := dpsiS_near2 2 hx12
    rw [psiS_d2, psiS_d3, zero_mul, sub_zero] at h
    have e : lamS w ts 2 - w ^ 2 / 12 = (w : ℂ) ^ 2 * (iteratedDeriv 2 psiS x - 1 / 12) := by
      unfold lamS; ring
    rw [e, norm_mul, hnw]
    calc (w : ℝ) ^ 2 * ‖iteratedDeriv 2 psiS x - 1 / 12‖ ≤ (w : ℝ) ^ 2 * (2 ! * (81 / 2) * 3 ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 729 * (w ^ 2 * ‖x‖ ^ 2) := by simp [Nat.factorial]; ring
      _ ≤ 10 ^ 5 * u := by nlinarith
  · have h := dpsiS_near1 3 hx12
    rw [psiS_d3, sub_zero] at h
    unfold lamS
    rw [norm_mul, hnw]
    calc (w : ℝ) ^ 3 * ‖iteratedDeriv 3 psiS x‖ ≤ (w : ℝ) ^ 3 * (3 ! * (27 / 4) * 3 ^ 3 * ‖x‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2187 / 2 * (w ^ 3 * ‖x‖) := by simp [Nat.factorial]; ring
      _ ≤ 10 ^ 5 * u := by nlinarith
  · have h := dpsiS_near2 4 hx12
    rw [psiS_d4, psiS_d5, zero_mul, sub_zero] at h
    have e : lamS w ts 4 + w ^ 4 / 120 = (w : ℂ) ^ 4 * (iteratedDeriv 4 psiS x - -1 / 120) := by
      unfold lamS; ring
    rw [e, norm_mul, hnw]
    calc (w : ℝ) ^ 4 * ‖iteratedDeriv 4 psiS x - -1 / 120‖ ≤ (w : ℝ) ^ 4 * (4 ! * (81 / 2) * 3 ^ 4 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 78732 * (w ^ 4 * ‖x‖ ^ 2) := by simp [Nat.factorial]; ring
      _ ≤ 10 ^ 5 * u := by nlinarith

/-! ### `κ₂` of the vanishing factor is real -/

theorem gS_conj (z : ℂ) : gS (conj z) = conj (gS z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [gS_zero]
  have hz' : conj z ≠ 0 := by simpa using hz
  rw [gS_of_ne hz', gS_of_ne hz, map_div₀, map_sub, map_one, ← Complex.exp_conj]

theorem psiS_conj {z : ℂ} (hz : ‖z‖ < 2 / 3) : psiS (conj z) = conj (psiS z) := by
  unfold psiS; rw [gS_conj]
  refine Complex.log_conj _ fun h => ?_
  have := abs_arg_lt_of_re_pos (gS_re_pos hz)
  rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]

theorem gS_neg (z : ℂ) : gS (-z) = Complex.exp (-z) * gS z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [gS_zero]
  rw [gS_of_ne (neg_ne_zero.mpr hz), gS_of_ne hz, Complex.exp_neg]
  have := Complex.exp_ne_zero z
  field_simp; ring

theorem psiS_neg {z : ℂ} (hz : ‖z‖ < 2 / 3) : psiS (-z) = psiS z - z := by
  show Complex.log (gS (-z)) = psiS z - z
  rw [gS_neg, ← exp_psiS hz, ← Complex.exp_add]
  have hb := norm_psiS_le (z := z) hz.le
  have hi : |(-z + psiS z).im| ≤ 2 / 3 + 3 / 4 := by
    refine (Complex.abs_im_le_norm _).trans ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; nlinarith [norm_nonneg z]
  have hpi := Real.two_le_pi
  rw [Complex.log_exp (by linarith [(abs_le.mp hi).1]) (by linarith [(abs_le.mp hi).2])]
  ring

theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, ← iteratedDeriv_succ]

/-- `ψ″(iv)` is real for real `v`, `|v| ≤ 1/12`: hence `κ₂` of the vanishing factor at `t*` is real. -/
theorem psiS_d2_real {v : ℝ} (hv : |v| ≤ 1 / 12) : (iteratedDeriv 2 psiS (I * v)).im = 0 := by
  set x := I * (v : ℂ)
  have hx : ‖x‖ < 2 / 3 := by
    simp only [x, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; linarith
  have hxc : conj x = -x := by simp [x]
  have hball : ball (0 : ℂ) (2 / 3) ∈ nhds x := isOpen_ball.mem_nhds (by rwa [mem_ball, dist_zero_right])
  -- conjugation
  have hc : (conj ∘ psiS ∘ conj) =ᶠ[nhds x] psiS := by
    filter_upwards [hball] with z hz
    rw [mem_ball, dist_zero_right] at hz
    show conj (psiS (conj z)) = psiS z
    rw [psiS_conj hz, conj_conj]
  have h1 : iteratedDeriv 2 psiS x = conj (iteratedDeriv 2 psiS (-x)) := by
    rw [← hc.iteratedDeriv_eq 2, iteratedDeriv_conj_conj]; simp [hxc]
  -- parity
  have hn : (fun z => psiS (-z)) =ᶠ[nhds x] (psiS - id) := by
    filter_upwards [hball] with z hz
    rw [mem_ball, dist_zero_right] at hz
    simp [psiS_neg hz]
  have hcd : ContDiffAt ℂ 2 psiS x := (analyticOnNhd_psiS x (by rwa [mem_ball, dist_zero_right])).contDiffAt
  have h2 : iteratedDeriv 2 psiS (-x) = iteratedDeriv 2 psiS x := by
    have := hn.iteratedDeriv_eq 2
    rw [iteratedDeriv_comp_neg, iteratedDeriv_sub hcd contDiffAt_id, iteratedDeriv_id] at this
    simpa using this
  rw [h2] at h1
  have := congrArg Complex.im h1
  rw [Complex.conj_im] at this
  linarith

end ArcsAlgo.Edge
