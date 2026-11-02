module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
set_option autoImplicit false

/-!
# Theorem E(2), the core: one factor (paper §3.5)

* `taylor_tail`: Taylor's remainder for a holomorphic function from Cauchy's estimates,
  `|f(z) − Σ_{n<K} f^{(n)}(0)z^n/n!| ≤ 2M(|z|/R)^K` for `|z| ≤ R/2`, `|f| ≤ M` on `|z| = R`.
* `psiB p x = log(1 + p(e^x − 1))` (the cumulant generating function of `Bernoulli(p)`, complex `p`),
  with `ψ^{(n+1)} = Q_n(P)`, `P = pe^x/(1 + p(e^x − 1))`, `Q_{n+1} = Q_n′·X(1 − X)` (`iteratedDeriv_psiB`).
* `cB p n = ψ^{(n)}(0)/n!`: `p`, `p(1−p)/2`, `p(1−p)(1−2p)/6`, `p(1−p)(1−6p+6p²)/24`,
  `p(1−p)(1−2p)(1−12p+12p²)/120` (`taylor_coeff_psiB`): the cumulants of Propositions C, C′.
* `psiB_expand`: for `|p| ≤ K`, `K ≥ 1`, `|x| ≤ 1/(16K)`: `1 + p(e^x − 1) = e^ψ`,
  `|ψ − Σ_{n≤5} c_n x^n| ≤ 2(8K|x|)^6` (this replaces the paper's Cauchy estimate
  `O((qwσ)⁶ log q)`, with `K = q`).
* `norm_cB_le`: `|c_n| ≤ 25K^n`.

No hypothesis.
-/

open Finset Complex Polynomial Nat

@[expose] public section

namespace ArcsAlgo.Edge

/-- **Taylor's remainder for a holomorphic function** (Cauchy's estimates): if `f` is holomorphic
on `|z| < 2R` and `|f| ≤ M` on `|z| = R`, then for `|z| ≤ R/2`,
`|f(z) − Σ_{n<K} f^{(n)}(0) z^n/n!| ≤ 2M(|z|/R)^K`. -/
theorem taylor_tail {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (Metric.ball 0 (2 * R)))
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (K : ℕ) {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖f z - ∑ n ∈ range K, (n ! : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n‖ ≤ 2 * M * (‖z‖ / R) ^ K := by
  have hM0 : 0 ≤ M := by
    have := hM (R : ℂ) (by simp [abs_of_pos hR]); exact le_trans (norm_nonneg _) this
  have hzb : z ∈ Metric.ball (0 : ℂ) (2 * R) := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hf hzb
  set g : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n with hg
  have hs' : HasSum g (f z) := by
    convert hs using 1; ext n; simp only [hg, sub_zero, smul_eq_mul]; ring
  have htail := (hasSum_nat_add_iff' K).mpr hs'
  have hdc : DiffContOnCl ℂ f (Metric.ball 0 R) :=
    hf.diffContOnCl_ball (Metric.closedBall_subset_ball (by linarith))
  set r := ‖z‖ / R with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ hR]; linarith
  have hbound : ∀ n, ‖g (n + K)‖ ≤ M * r ^ K * r ^ n := by
    intro n
    have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n + K) hR hdc hM
    simp only [hg, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hf0 : (0 : ℝ) < ((n + K) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((n + K) ! : ℝ)⁻¹ * ‖iteratedDeriv (n + K) f 0‖ * ‖z‖ ^ (n + K)
        ≤ ((n + K) ! : ℝ)⁻¹ * (((n + K) ! : ℝ) * M / R ^ (n + K)) * ‖z‖ ^ (n + K) := by gcongr
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

/-! ### The factor `1 + p(e^x − 1)` -/

/-- `ψ_p(x) = log(1 + p(e^x − 1))`: the cumulant generating function of `Bernoulli(p)`. -/
noncomputable def psiB (p x : ℂ) : ℂ := Complex.log (1 + p * (Complex.exp x - 1))

/-- `P_p(x) = p e^x / (1 + p(e^x − 1))`. -/
noncomputable def PB (p x : ℂ) : ℂ := p * Complex.exp x / (1 + p * (Complex.exp x - 1))

/-- The region `|p(e^x − 1)| < 1`. -/
def UB (p : ℂ) : Set ℂ := {x | ‖p * (Complex.exp x - 1)‖ < 1}

theorem UB_open (p : ℂ) : IsOpen (UB p) :=
  isOpen_lt (by fun_prop) continuous_const

theorem re_pos {p x : ℂ} (hx : x ∈ UB p) : 0 < (1 + p * (Complex.exp x - 1)).re := by
  have h := Complex.abs_re_le_norm (p * (Complex.exp x - 1))
  have h' : ‖p * (Complex.exp x - 1)‖ < 1 := hx
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le (p * (Complex.exp x - 1)).re]

theorem mem_slit {p x : ℂ} (hx : x ∈ UB p) : 1 + p * (Complex.exp x - 1) ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_pos hx))

theorem D_ne {p x : ℂ} (hx : x ∈ UB p) : 1 + p * (Complex.exp x - 1) ≠ 0 := slitPlane_ne_zero (mem_slit hx)

theorem hasDerivAt_D (p x : ℂ) : HasDerivAt (fun x => 1 + p * (Complex.exp x - 1)) (p * Complex.exp x) x := by
  have := ((Complex.hasDerivAt_exp x).sub_const 1).const_mul p |>.const_add 1
  simpa using this

theorem hasDerivAt_psiB {p x : ℂ} (hx : x ∈ UB p) : HasDerivAt (psiB p) (PB p x) x := by
  have := (hasDerivAt_D p x).clog (mem_slit hx)
  unfold psiB PB; convert this using 1

theorem hasDerivAt_PB {p x : ℂ} (hx : x ∈ UB p) : HasDerivAt (PB p) (PB p x * (1 - PB p x)) x := by
  have hD := D_ne hx
  have h := ((Complex.hasDerivAt_exp x).const_mul p).div (hasDerivAt_D p x) hD
  unfold PB
  convert h using 1
  field_simp

/-- `Q₀ = X`, `Q_{n+1} = Q_n′ · X(1 − X)`: `ψ^{(n+1)} = Q_n(P)`. -/
noncomputable def Qd : ℕ → Polynomial ℂ
  | 0 => X
  | n + 1 => Polynomial.derivative (Qd n) * (X * (1 - X))

theorem iteratedDeriv_psiB (p : ℂ) (n : ℕ) :
    ∀ x ∈ UB p, iteratedDeriv (n + 1) (psiB p) x = (Qd n).eval (PB p x) := by
  induction n with
  | zero =>
    intro x hx
    rw [iteratedDeriv_one, (hasDerivAt_psiB hx).deriv]; simp [Qd]
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv (n + 1) (psiB p) =ᶠ[nhds x] fun y => (Qd n).eval (PB p y) :=
      Filter.eventually_of_mem ((UB_open p).mem_nhds hx) ih
    rw [hev.deriv_eq]
    have h := ((Qd n).hasDerivAt (PB p x)).comp x (hasDerivAt_PB hx)
    rw [show (fun y => (Qd n).eval (PB p y)) = (fun x => (Qd n).eval x) ∘ PB p from rfl, h.deriv]
    simp [Qd, eval_mul]

theorem zero_mem_UB (p : ℂ) : (0 : ℂ) ∈ UB p := by simp [UB]

theorem PB_zero (p : ℂ) : PB p 0 = p := by simp [PB]

theorem psiB_zero (p : ℂ) : psiB p 0 = 0 := by simp [psiB]

/-- The Taylor coefficients `c_n = ψ^{(n)}(0)/n!`: `c₁ = p`, `c₂ = p(1−p)/2`, `c₃ = p(1−p)(1−2p)/6`,
`c₄ = p(1−p)(1−6p+6p²)/24`, `c₅ = p(1−p)(1−2p)(1−12p+12p²)/120` (Propositions C, C′). -/
noncomputable def cB (p : ℂ) : ℕ → ℂ
  | 1 => p
  | 2 => p * (1 - p) / 2
  | 3 => p * (1 - p) * (1 - 2 * p) / 6
  | 4 => p * (1 - p) * (1 - 6 * p + 6 * p ^ 2) / 24
  | 5 => p * (1 - p) * (1 - 2 * p) * (1 - 12 * p + 12 * p ^ 2) / 120
  | _ => 0

theorem taylor_coeff_psiB (p : ℂ) :
    ∀ n ∈ range 6, (n ! : ℂ)⁻¹ * iteratedDeriv n (psiB p) 0 = cB p n := by
  intro n hn
  have hn6 := mem_range.mp hn
  rcases n with _ | n
  · simp [psiB_zero, cB]
  · rw [iteratedDeriv_psiB p n 0 (zero_mem_UB p), PB_zero]
    have : n < 5 := by omega
    interval_cases n <;> simp [Qd, cB, Nat.factorial, eval_mul] <;> ring

/-- **The factor expansion**: for `|p| ≤ K`, `K ≥ 1` and `|x| ≤ 1/(16K)`,
`1 + p(e^x − 1) = e^{ψ}` with `|ψ − Σ_{n=1}^{5} c_n x^n| ≤ 2(8K|x|)^6`. -/
theorem psiB_expand {p : ℂ} {K : ℝ} (hK : 1 ≤ K) (hp : ‖p‖ ≤ K) {x : ℂ} (hx : ‖x‖ ≤ 1 / (16 * K)) :
    1 + p * (Complex.exp x - 1) = Complex.exp (psiB p x) ∧
      ‖psiB p x - ∑ n ∈ range 6, cB p n * x ^ n‖ ≤ 2 * (8 * K * ‖x‖) ^ 6 := by
  have hK0 : 0 < K := by linarith
  set R := 1 / (8 * K) with hR
  have hR0 : 0 < R := by positivity
  have hsmall : ∀ y : ℂ, ‖y‖ ≤ 1 / (4 * K) → ‖p * (Complex.exp y - 1)‖ ≤ 2 * K * ‖y‖ := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := le_trans hy (by rw [div_le_one (by positivity)]; linarith)
    rw [norm_mul]
    calc ‖p‖ * ‖Complex.exp y - 1‖ ≤ K * (2 * ‖y‖) :=
          mul_le_mul hp (Complex.norm_exp_sub_one_le hy1) (norm_nonneg _) hK0.le
      _ = 2 * K * ‖y‖ := by ring
  have hU : ∀ y : ℂ, ‖y‖ < 1 / (4 * K) → y ∈ UB p := by
    intro y hy
    show ‖p * (Complex.exp y - 1)‖ < 1
    have := hsmall y hy.le
    have : 2 * K * ‖y‖ < 2 * K * (1 / (4 * K)) := by gcongr
    have e : 2 * K * (1 / (4 * K)) = 1 / 2 := by field_simp; ring
    linarith
  have hdiff : DifferentiableOn ℂ (psiB p) (Metric.ball 0 (2 * R)) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have e : 2 * R = 1 / (4 * K) := by rw [hR]; field_simp; ring
    rw [e] at hy
    exact (hasDerivAt_psiB (hU y hy)).differentiableAt.differentiableWithinAt
  have hM : ∀ y ∈ Metric.sphere (0 : ℂ) R, ‖psiB p y‖ ≤ 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    have h1 : ‖p * (Complex.exp y - 1)‖ ≤ 1 / 4 := by
      have := hsmall y (by rw [hy, hR]; gcongr; linarith)
      rw [hy, hR] at this
      have e : 2 * K * (1 / (8 * K)) = 1 / 4 := by field_simp; ring
      linarith
    have := Complex.norm_log_one_add_half_le_self (z := p * (Complex.exp y - 1)) (by linarith)
    unfold psiB; linarith
  have hxR : ‖x‖ ≤ R / 2 := by
    rw [hR]; rw [show 1 / (8 * K) / 2 = 1 / (16 * K) by field_simp; ring]; exact hx
  have hT := taylor_tail hR0 hdiff hM 6 hxR
  have hsum : ∑ n ∈ range 6, (n ! : ℂ)⁻¹ * iteratedDeriv n (psiB p) 0 * x ^ n =
      ∑ n ∈ range 6, cB p n * x ^ n :=
    sum_congr rfl fun n hn => by rw [taylor_coeff_psiB p n hn]
  rw [hsum] at hT
  refine ⟨?_, ?_⟩
  · have hx0 : x ∈ UB p := hU x (lt_of_le_of_lt hx (by gcongr; linarith))
    unfold psiB; rw [Complex.exp_log (D_ne hx0)]
  · calc ‖psiB p x - ∑ n ∈ range 6, cB p n * x ^ n‖ ≤ 2 * 1 * (‖x‖ / R) ^ 6 := hT
      _ = 2 * (8 * K * ‖x‖) ^ 6 := by rw [hR]; field_simp

/-- `|c_n(p)| ≤ 25 K^n` for `|p| ≤ K`, `K ≥ 1`, `n ≤ 5`. -/
theorem norm_cB_le {p : ℂ} {K : ℝ} (hK : 1 ≤ K) (hp : ‖p‖ ≤ K) (n : ℕ) : ‖cB p n‖ ≤ 25 * K ^ n := by
  have hK0 : 0 ≤ K := by linarith
  have h1 : ‖1 - p‖ ≤ 2 * K := (norm_sub_le _ _).trans (by simp; linarith)
  have h2 : ‖1 - 2 * p‖ ≤ 3 * K := (norm_sub_le _ _).trans (by rw [norm_mul]; simp; linarith)
  have h3 : ‖1 - 6 * p + 6 * p ^ 2‖ ≤ 13 * K ^ 2 := by
    calc ‖1 - 6 * p + 6 * p ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖6 * p‖ + ‖6 * p ^ 2‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 1 + 6 * K + 6 * K ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow]; simp only [norm_one, Complex.norm_ofNat]; gcongr
      _ ≤ 13 * K ^ 2 := by nlinarith
  have h4 : ‖1 - 12 * p + 12 * p ^ 2‖ ≤ 25 * K ^ 2 := by
    calc ‖1 - 12 * p + 12 * p ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖12 * p‖ + ‖12 * p ^ 2‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 1 + 12 * K + 12 * K ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow]; simp only [norm_one, Complex.norm_ofNat]; gcongr
      _ ≤ 25 * K ^ 2 := by nlinarith
  have hpK : ‖p‖ * ‖1 - p‖ ≤ K * (2 * K) := mul_le_mul hp h1 (norm_nonneg _) hK0
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [cB]
  · simp only [cB, zero_add, pow_one]; nlinarith
  · simp only [cB, norm_div, norm_mul, Complex.norm_ofNat]; nlinarith
  · simp only [cB, norm_div, norm_mul, Complex.norm_ofNat]
    have := mul_le_mul hpK h2 (norm_nonneg _) (by positivity); nlinarith
  · simp only [cB, norm_div, norm_mul, Complex.norm_ofNat]
    have := mul_le_mul hpK h3 (norm_nonneg _) (by positivity); nlinarith
  · simp only [cB, norm_div, norm_mul, Complex.norm_ofNat]
    have h5 := mul_le_mul hpK h2 (norm_nonneg _) (by positivity)
    have := mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
    have e : K * (2 * K) * (3 * K) * (25 * K ^ 2) = 150 * K ^ 5 := by ring
    rw [div_le_iff₀ (by norm_num)]; norm_num; nlinarith [pow_nonneg hK0 5]
  · simp [cB]; positivity

end ArcsAlgo.Edge
