module

public import ArcsAlgo.Clausen
public import ArcsAlgo.LemmaP
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
set_option autoImplicit false

/-!
# Lemma Q: the lobes of every arc (paper §3.3)

`h_q(x) = log|Φ_q(−e(x))|`, `A_q(X) = X⁻¹∫₀^X h_q`, `G(u) = log|2 sin πu|`, `κ = Cl₂(π/3)/π`
(`Clausen`).

* `hq_moebius`, `Aq_moebius`: `h_q(x) = Σ_{d∣q} μ(q/d) G(dx + d/2)` for irrational `x`, hence
  `A_q(X) = Σ_{d∣q} μ(q/d) X⁻¹∫₀^X G(dx + d/2)` (Möbius inversion of `Π_{d∣n} Φ_d = X^n − 1`).
* `neg_int_Gs_le_half`: `−L⁻¹∫_{d/2}^{d/2+L} G ≤ log(e/(2L))` for `0 < L ≤ 1`.
* **Q(1)** `lemmaQ1`: `h_q` is strictly decreasing on `[0, 1/(2q))`, from
  `|Φ_q(−e(x))|² = Π_μ (2 Re μ + 2 cos 2πx)` and `Re μ ≥ −cos(π/q)` (`norm_cyc_sq`, `re_prim_ge`);
  `lemmaQ1_avg`: `A_q(X) < h_q(0) = φ(q)c_q` on `(0, 1/(2q))` and `A_q` is strictly decreasing there,
  so `X_q ≥ 1/(2q)`.
* **Q(2)** `lemmaQ2`: for `X > 0`,
  `A_q(X) ≤ Σ_{μ(q/d)=1} min(log 2, κ/(dX)) + Σ_{μ(q/d)=−1} β(dX)` with
  `β(L) = max(κ, min(κ/L, log(e/(2L))))` for `L ≤ 1` and `κ/L` for `L > 1` (`betaQ`);
  `rhsQ_anti`: the right side is non-increasing in `X`; `lemmaQ2_Rq`: `A_q(X) ≤ φ(q)R_q` for
  `X ≥ 1/(2q)`, so `ℓ_q ≤ R_q`; `Rq_bound`, `Rq_bound_tau`:
  `φ(q)R_q ≤ 2^{ω(q)−1}(1 + log 2 + log rad q) ≤ τ(q) log(2eq)/2`.
* **Q(3)** `lemmaQ3`: for `X ≥ 1`, `A_q(X) ≤ κ·2^{ω(q)}`.

No hypothesis. `κ ≤ 1/2` is proved (`kappa_le_half`); its value `0.32307…` is not used.
-/

open Finset Real Polynomial ArithmeticFunction MeasureTheory
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

@[expose] public section

namespace ArcsAlgo.Core

/-! ### Möbius inversion of `log|z^n − 1|` -/

theorem log_cyc_moebius {z : ℂ} (hz : ∀ n, 0 < n → z ^ n ≠ 1) {q : ℕ} (hq : 0 < q) :
    Real.log ‖(cyclotomic q ℂ).eval z‖ =
      ∑ x ∈ q.divisorsAntidiagonal, (μ x.1 : ℝ) * Real.log ‖z ^ x.2 - 1‖ := by
  have h : ∀ n > 0, ∑ d ∈ n.divisors, Real.log ‖(cyclotomic d ℂ).eval z‖ = Real.log ‖z ^ n - 1‖ := by
    intro n hn
    have hp := prod_cyclotomic_eq_X_pow_sub_one hn ℂ
    have he : ∏ d ∈ n.divisors, (cyclotomic d ℂ).eval z = z ^ n - 1 := by
      rw [← eval_prod, hp]; simp
    have hne : ∀ d ∈ n.divisors, (cyclotomic d ℂ).eval z ≠ 0 := by
      have h0 : z ^ n - 1 ≠ 0 := sub_ne_zero.mpr (hz n hn)
      rw [← he] at h0
      exact fun d hd => (prod_ne_zero_iff.mp h0) d hd
    rw [← he, norm_prod, Real.log_prod (fun d hd => norm_ne_zero_iff.mpr (hne d hd))]
  exact ((sum_eq_iff_sum_mul_moebius_eq (f := fun d => Real.log ‖(cyclotomic d ℂ).eval z‖)
    (g := fun n => Real.log ‖z ^ n - 1‖)).mp h q hq).symm

theorem ee_eq_one {t : ℝ} (h : ee t = 1) : ∃ k : ℤ, t = k := by
  unfold ee at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨k, ?_⟩
  have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (t : ℂ) = k := by
    have := hk; rw [show (k : ℂ) * (2 * π * Complex.I) = 2 * π * Complex.I * k by ring] at this
    exact mul_left_cancel₀ h2 this
  exact_mod_cast this

theorem neg_ee_pow (x : ℝ) (n : ℕ) : (-ee x) ^ n = ee (n * x + n / 2) := by
  have h1 : (-1 : ℂ) = ee (1 / 2) := by
    unfold ee
    rw [show (2 * π * Complex.I * ((1 / 2 : ℝ) : ℂ)) = π * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  rw [neg_eq_neg_one_mul, h1, mul_pow, ee_pow, ee_pow]
  unfold ee
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- For irrational `x`, `−e(x)` is not a root of unity. -/
theorem neg_ee_pow_ne_one {x : ℝ} (hx : Irrational x) (n : ℕ) (hn : 0 < n) : (-ee x) ^ n ≠ 1 := by
  rw [neg_ee_pow]
  intro h
  obtain ⟨k, hk⟩ := ee_eq_one h
  apply hx
  refine ⟨((k : ℚ) - n / 2) / n, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  linarith

theorem norm_ee_sub_one (t : ℝ) : ‖ee t - 1‖ = 2 * |sin (π * t)| := by
  have h : ee t - 1 = Complex.exp (π * t * Complex.I) * (2 * Complex.I * Complex.sin (π * t)) := by
    unfold ee
    rw [Complex.sin, show (2 : ℂ) * Complex.I * ((Complex.exp (-(↑π * ↑t) * Complex.I) -
      Complex.exp (↑π * ↑t * Complex.I)) * Complex.I / 2) =
      Complex.exp (↑π * ↑t * Complex.I) - Complex.exp (-(↑π * ↑t) * Complex.I) by
        ring_nf; rw [Complex.I_sq]; ring]
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    rw [show (↑π * ↑t * Complex.I + ↑π * ↑t * Complex.I) = 2 * ↑π * Complex.I * ↑t by ring,
      show (↑π * ↑t * Complex.I + -(↑π * ↑t) * Complex.I) = 0 by ring, Complex.exp_zero]
  rw [h, norm_mul, show (π * t * Complex.I : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
    show (π : ℂ) * t = ((π * t : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin, Complex.norm_real,
    Real.norm_eq_abs]
  simp

/-- `log|e(t) − 1| = G(t)` off `ℤ`. -/
theorem log_norm_ee_sub_one {t : ℝ} (ht : sin (π * t) ≠ 0) : Real.log ‖ee t - 1‖ = Gs t := by
  rw [norm_ee_sub_one, Real.log_mul (by norm_num) (abs_ne_zero.mpr ht), Real.log_abs]; rfl

/-- **The Möbius form of `h_q`** (paper §3.3, proof of Lemma Q(2)): for irrational `x` and `q ≥ 1`,
`h_q(x) = Σ_{d∣q} μ(q/d) G(dx + d/2)`. -/
theorem hq_moebius {q : ℕ} (hq0 : 0 < q) {x : ℝ} (hx : Irrational x) :
    hq q x = ∑ y ∈ q.divisorsAntidiagonal, (μ y.1 : ℝ) * Gs (y.2 * x + y.2 / 2) := by
  unfold hq
  rw [log_cyc_moebius (neg_ee_pow_ne_one hx) hq0]
  refine sum_congr rfl fun y hy => ?_
  have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  rw [neg_ee_pow, log_norm_ee_sub_one]
  intro hs
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
  apply neg_ee_pow_ne_one hx y.2 hy2
  rw [neg_ee_pow]
  unfold ee
  rw [Complex.exp_eq_one_iff]
  refine ⟨k, ?_⟩
  have : (y.2 * x + y.2 / 2 : ℝ) = k := by
    have := Real.pi_pos
    field_simp at hk ⊢; linarith
  rw [show ((y.2 * x + y.2 / 2 : ℝ) : ℂ) = (k : ℂ) by exact_mod_cast this]; ring

/-! ### Integrals of `G(d· + c)` -/

theorem Gs_aff_int {d : ℝ} (hd : d ≠ 0) (c a b : ℝ) :
    IntervalIntegrable (fun x => Gs (d * x + c)) volume a b := by
  have h1 := (Gs_int (d * a + c) (d * b + c)).comp_add_right c
  have h2 := h1.comp_mul_left (c := d)
  simp only [add_sub_cancel_right, mul_div_cancel_left₀ _ hd] at h2
  exact h2

theorem avg_Gs_eq {d X : ℝ} (hd : 0 < d) (c : ℝ) :
    (∫ x in (0 : ℝ)..X, Gs (d * x + c)) = d⁻¹ * ∫ t in c..c + d * X, Gs t := by
  rw [intervalIntegral.integral_comp_mul_add Gs hd.ne' c, mul_zero, zero_add, smul_eq_mul, add_comm]

/-- **`A_q` as a sum over divisors**: `A_q(X) = Σ_{d∣q} μ(q/d) X⁻¹∫₀^X G(dx + d/2) dx`. -/
theorem Aq_moebius {q : ℕ} (hq0 : 0 < q) (X : ℝ) :
    Aq q X = ∑ y ∈ q.divisorsAntidiagonal,
      (μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X) := by
  unfold Aq
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc 0 X →
      hq q x = ∑ y ∈ q.divisorsAntidiagonal, (μ y.1 : ℝ) * Gs (y.2 * x + y.2 / 2) := by
    have hc : volume (Set.range ((↑) : ℚ → ℝ)) = 0 := (Set.countable_range _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hc] with x hx _
    exact hq_moebius hq0 hx
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_finsetSum, sum_div]
  · refine sum_congr rfl fun y _ => ?_
    rw [intervalIntegral.integral_const_mul, mul_div_assoc]
  · intro y hy
    have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
    exact (Gs_aff_int (by exact_mod_cast hy2.ne') _ 0 X).const_mul _

/-! ### The bounds for one divisor -/

theorem avg_le_log2 {d X : ℝ} (hd : 0 < d) (hX : 0 < X) (c : ℝ) :
    (∫ x in (0 : ℝ)..X, Gs (d * x + c)) / X ≤ Real.log 2 := by
  rw [div_le_iff₀ hX]
  have := intervalIntegral.integral_mono_on hX.le (Gs_aff_int hd.ne' c 0 X) intervalIntegrable_const
    fun x _ => Gs_le (d * x + c)
  simpa [intervalIntegral.integral_const, mul_comm] using this

theorem Gs_ge_log4 {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) : Real.log (4 * t) ≤ Gs t := by
  unfold Gs
  have hpi := Real.pi_pos
  have hs : 2 * t ≤ sin (π * t) := by
    have := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith)
    have e : 2 / π * (π * t) = 2 * t := by field_simp
    linarith
  rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.log_mul (by norm_num) (by positivity)]
  have := Real.log_le_log (by positivity) hs
  linarith

theorem log4_int (a b : ℝ) : IntervalIntegrable (fun t => Real.log (4 * t)) volume a b := by
  have := (intervalIntegral.intervalIntegrable_log' (a := 4 * a) (b := 4 * b)).comp_mul_left (c := 4)
  rwa [mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0),
    mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at this

theorem integral_log4 (L : ℝ) : ∫ t in (0 : ℝ)..L, Real.log (4 * t) = L * Real.log (4 * L) - L := by
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.log t) (by norm_num : (4 : ℝ) ≠ 0),
    integral_log]
  simp only [mul_zero, Real.log_zero, smul_eq_mul]
  ring

theorem integral_Gs_period (c : ℝ) : ∫ t in c..c + 1, Gs t = 0 := by
  rw [Gs_periodic.intervalIntegral_add_eq c 0, zero_add, integral_Gs_zero_one]

/-- `−∫_c^{c+L} G ≤ L(1 − log 2L)` for `c ∈ {0, 1/2}` and `0 < L ≤ 1`. -/
theorem neg_int_Gs_le {c L : ℝ} (hc : c = 0 ∨ c = 1 / 2) (hL0 : 0 < L) (hL1 : L ≤ 1) :
    -∫ t in c..c + L, Gs t ≤ L * (1 - Real.log (2 * L)) := by
  rcases le_or_gt L (1 / 2) with hL | hL
  · have hlow : L * Real.log (4 * L) - L ≤ ∫ t in c..c + L, Gs t := by
      rcases hc with rfl | rfl
      · rw [zero_add, ← integral_log4]
        exact intervalIntegral.integral_mono_on_of_le_Ioo hL0.le (log4_int 0 L) (Gs_int 0 L)
          fun t ht => Gs_ge_log4 ht.1 (by linarith [ht.2])
      · -- reflect `t ↦ 1 − t`, then shift
        have e1 : ∫ t in (1 / 2 : ℝ)..1 / 2 + L, Gs t = ∫ t in (1 / 2 - L)..1 / 2, Gs t := by
          have := intervalIntegral.integral_comp_sub_left (a := 1 / 2) (b := 1 / 2 + L) Gs 1
          rw [show (1 : ℝ) - (1 / 2 + L) = 1 / 2 - L by ring, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
          rw [← this]
          exact intervalIntegral.integral_congr fun t _ => (Gs_one_sub t).symm
        have e2 : ∫ t in (1 / 2 - L)..1 / 2, Real.log (4 * (t - (1 / 2 - L))) =
            ∫ t in (0 : ℝ)..L, Real.log (4 * t) := by
          have := intervalIntegral.integral_comp_sub_right (a := 1 / 2 - L) (b := 1 / 2)
            (fun t => Real.log (4 * t)) (1 / 2 - L)
          simp only [sub_self, show (1 / 2 : ℝ) - (1 / 2 - L) = L by ring] at this
          exact this
        rw [e1, ← integral_log4, ← e2]
        refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) ?_ (Gs_int _ _) fun t ht => ?_
        · have := (log4_int 0 L).comp_sub_right (1 / 2 - L)
          simpa [show (0 : ℝ) - (1 / 2 - L) = -(1 / 2 - L) by ring, sub_neg_eq_add,
            show L + (1 / 2 - L) = (1 / 2 : ℝ) by ring] using this
        · obtain ⟨h1, h2⟩ := ht
          have hpos : 0 < t - (1 / 2 - L) := by linarith
          have := Gs_ge_log4 (t := t) (by linarith) h2.le
          exact le_trans (Real.log_le_log (by positivity) (by linarith)) this
    have : Real.log (2 * L) ≤ Real.log (4 * L) := Real.log_le_log (by positivity) (by linarith)
    nlinarith
  · -- `L > 1/2`: the complement in a period
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (Gs_int c (c + L)) (Gs_int (c + L) (c + 1))
    rw [integral_Gs_period] at hsplit
    have hup : ∫ t in (c + L)..c + 1, Gs t ≤ (1 - L) * Real.log 2 := by
      have := intervalIntegral.integral_mono_on (by linarith : c + L ≤ c + 1) (Gs_int _ _)
        intervalIntegrable_const fun t _ => Gs_le t
      simpa [intervalIntegral.integral_const, show c + 1 - (c + L) = 1 - L by ring] using this
    have hlog : Real.log (2 * L) ≤ 2 * L - 1 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * L); linarith
    have hl2 := Real.log_two_lt_d9
    nlinarith

theorem Gs_add_nat (x : ℝ) (k : ℕ) : Gs (x + k) = Gs x := by
  simpa using Gs_periodic.nat_mul k x

/-- The same after an integer shift: `c = n/2` for `n ∈ ℕ`. -/
theorem neg_int_Gs_le_half (n : ℕ) {L : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1) :
    -∫ t in (n / 2 : ℝ)..n / 2 + L, Gs t ≤ L * (1 - Real.log (2 * L)) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · have h := neg_int_Gs_le (c := 0) (Or.inl rfl) hL0 hL1
    have e := intervalIntegral.integral_comp_add_right (a := 0) (b := L) Gs (k : ℝ)
    have e' : ∫ x in (0 : ℝ)..L, Gs (x + k) = ∫ x in (0 : ℝ)..L, Gs x :=
      intervalIntegral.integral_congr fun x _ => Gs_add_nat x k
    have hn : (n / 2 : ℝ) = 0 + k := by subst hk; push_cast; ring
    have hn' : (n / 2 : ℝ) + L = L + k := by rw [hn]; ring
    rw [hn', hn, ← e, e']
    simpa using h
  · have h := neg_int_Gs_le (c := 1 / 2) (Or.inr rfl) hL0 hL1
    have e := intervalIntegral.integral_comp_add_right (a := 1 / 2) (b := 1 / 2 + L) Gs (k : ℝ)
    have e' : ∫ x in (1 / 2 : ℝ)..1 / 2 + L, Gs (x + k) = ∫ x in (1 / 2 : ℝ)..1 / 2 + L, Gs x :=
      intervalIntegral.integral_congr fun x _ => Gs_add_nat x k
    have hn : (n / 2 : ℝ) = 1 / 2 + k := by subst hk; push_cast; ring
    have hn' : (n / 2 : ℝ) + L = 1 / 2 + L + k := by rw [hn]; ring
    rw [hn', hn, ← e, e']
    exact h

/-! ### Lemma Q(2) -/

theorem kappa_nonneg : 0 ≤ kappa := by unfold kappa; linarith [Cl_sixth_nonpos]

/-- The lobe weight of a divisor with `μ(q/d) = −1`: `β(L) = max(κ, min(κ/L, log(e/(2L))))` for
`L ≤ 1` and `κ/L` for `L > 1` (non-increasing). -/
noncomputable def betaQ (L : ℝ) : ℝ :=
  if L ≤ 1 then max kappa (min (kappa / L) (Real.log (Real.exp 1 / (2 * L)))) else kappa / L

/-- The weight of a divisor `d` with `μ(q/d) = m` at `L = dX`. -/
noncomputable def termQ (m : ℤ) (L : ℝ) : ℝ :=
  if m = 1 then min (Real.log 2) (kappa / L) else if m = -1 then betaQ L else 0

theorem log_e_div {L : ℝ} (hL : 0 < L) : Real.log (Real.exp 1 / (2 * L)) = 1 - Real.log (2 * L) := by
  rw [Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp]

theorem moebius_cases (n : ℕ) : μ n = -1 ∨ μ n = 0 ∨ μ n = 1 := by
  have := abs_moebius_le_one (n := n); rw [abs_le] at this; omega

/-- One divisor: `μ(q/d)·X⁻¹∫₀^X G(dx + d/2) ≤ term(μ(q/d), dX)`. -/
theorem term_le {b : ℕ} (hb : 0 < b) {X : ℝ} (hX : 0 < X) (m : ℤ) (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (m : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (b * x + b / 2)) / X) ≤ termQ m (b * X) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  set a := (∫ x in (0 : ℝ)..X, Gs (b * x + b / 2)) / X
  have habs := abs_avg_Gs_le hb' hX ((b : ℝ) / 2)
  have hlog2 := avg_le_log2 hb' hX ((b : ℝ) / 2)
  have hL : 0 < (b : ℝ) * X := by positivity
  unfold termQ
  rcases hm with rfl | rfl | rfl
  · simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false, if_true, Int.cast_neg, Int.cast_one, neg_one_mul]
    have h1 : -a ≤ kappa / (b * X) := by have := neg_abs_le a; linarith [abs_le.mp habs]
    unfold betaQ
    split_ifs with hL1
    · -- `−a ≤ log(e/(2L))` for `L ≤ 1`
      have h2 : -a ≤ Real.log (Real.exp 1 / (2 * (b * X))) := by
        rw [log_e_div hL]
        have hneg := neg_int_Gs_le_half b hL hL1
        have e : a = (b * X)⁻¹ * ∫ t in ((b : ℝ) / 2)..(b / 2 + b * X), Gs t := by
          simp only [a]; rw [avg_Gs_eq hb']; field_simp
        rw [e]
        have : -((b * X)⁻¹ * ∫ t in ((b : ℝ) / 2)..(b / 2 + b * X), Gs t) =
            (b * X)⁻¹ * -∫ t in ((b : ℝ) / 2)..(b / 2 + b * X), Gs t := by ring
        rw [this, inv_mul_le_iff₀ hL]
        push_cast at hneg; linarith
      exact le_trans (le_min h1 h2) (le_max_right _ _)
    · exact h1
  · simp
  · simp only [if_true, Int.cast_one, one_mul]
    exact le_min hlog2 ((le_abs_self a).trans habs)

/-- **Lemma Q(2)** (paper §3.3): for `q ≥ 1` and `X > 0`,
`A_q(X) ≤ Σ_{μ(q/d)=1} min(log 2, κ/(dX)) + Σ_{μ(q/d)=−1} β(dX)`. -/
theorem lemmaQ2 {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 0 < X) :
    Aq q X ≤ ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X) := by
  rw [Aq_moebius hq0]
  refine sum_le_sum fun y hy => ?_
  have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  exact term_le hy2 hX (μ y.1) (moebius_cases y.1)

theorem betaQ_anti {L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') : betaQ L' ≤ betaQ L := by
  have hk := kappa_nonneg
  have hL' : 0 < L' := lt_of_lt_of_le hL hLL
  have hd : kappa / L' ≤ kappa / L := div_le_div_of_nonneg_left hk hL hLL
  unfold betaQ
  split_ifs with h1 h2 h2
  · refine max_le_max le_rfl (min_le_min hd ?_)
    rw [log_e_div hL, log_e_div hL']
    have := Real.log_le_log (by positivity) (by linarith : 2 * L ≤ 2 * L'); linarith
  · exact absurd (le_trans hLL h1) h2
  · exact le_trans (div_le_self hk (by linarith)) (le_max_left _ _)
  · exact hd

theorem termQ_anti (m : ℤ) {L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') : termQ m L' ≤ termQ m L := by
  unfold termQ
  split_ifs
  · exact min_le_min le_rfl (div_le_div_of_nonneg_left kappa_nonneg hL hLL)
  · exact betaQ_anti hL hLL
  · exact le_rfl

/-- **The right side of Lemma Q(2) is non-increasing in `X`.** -/
theorem rhsQ_anti {q : ℕ} {X X' : ℝ} (hX : 0 < X) (hXX : X ≤ X') :
    ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X') ≤
      ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X) := by
  refine sum_le_sum fun y hy => ?_
  have hy2 : (0 : ℝ) < y.2 := by
    exact_mod_cast Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  exact termQ_anti _ (by positivity) (mul_le_mul_of_nonneg_left hXX hy2.le)

/-- Hence `A_q(X) ≤ φ(q)R_q` for every `X ≥ 1/(2q)`, with `φ(q)R_q` the right side at `X = 1/(2q)`. -/
theorem lemmaQ2_Rq {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 1 / (2 * q) ≤ X) :
    Aq q X ≤ ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q))) := by
  have h0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  exact (lemmaQ2 hq0 (lt_of_lt_of_le h0 hX)).trans (rhsQ_anti h0 hX)

/-! ### The size of `R_q` -/

theorem kappa_le_half : kappa ≤ 1 / 2 := by
  have h : (1 / 6 : ℝ) * Real.log (4 * (1 / 6)) - 1 / 6 ≤ Cl (1 / 6) := by
    rw [← integral_log4]
    exact intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (log4_int 0 (1 / 6)) (Gs_int 0 (1 / 6))
      fun t ht => Gs_ge_log4 ht.1 (by linarith [ht.2])
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 * (1 / 6) by norm_num)
  norm_num at hl h
  unfold kappa; linarith

/-- `rad q = Π_{p ∣ q} p`. -/
def radQ (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

theorem le_radQ {q a : ℕ} (hq : q ≠ 0) (ha : a ∣ q) (hsq : Squarefree a) : a ≤ radQ q := by
  have hr : 0 < radQ q := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  refine Nat.le_of_dvd hr ?_
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono ha hq)

theorem radQ_le {q : ℕ} (hq : q ≠ 0) : radQ q ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

theorem card_sqfree_divisors {q : ℕ} (hq : q ≠ 0) :
    ((q.divisors).filter Squarefree).card = 2 ^ ω q := by
  have := Nat.sum_divisors_filter_squarefree hq (f := fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, card_powerset] at this
  rw [this, cardDistinctFactors_eq_card_primeFactors, Nat.factors_eq]
  rfl

theorem sum_moebius_divisors {q : ℕ} (hq : 1 < q) : ∑ d ∈ q.divisors, (μ d : ℤ) = 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f q) (coe_moebius_mul_coe_zeta (R := ℤ))
  rw [coe_mul_zeta_apply, one_apply_ne (by omega)] at this
  simpa using this

/-- `#{d ∣ q : μ(d) = 1} = #{d ∣ q : μ(d) = −1} = 2^{ω(q)−1}` (as `2·N = 2^ω`), `q ≥ 2`. -/
theorem card_moebius_pm {q : ℕ} (hq : 1 < q) :
    2 * ((q.divisors).filter (fun d => μ d = 1)).card = 2 ^ ω q ∧
      2 * ((q.divisors).filter (fun d => μ d = -1)).card = 2 ^ ω q := by
  set Np := ((q.divisors).filter (fun d => μ d = 1)).card
  set Nm := ((q.divisors).filter (fun d => μ d = -1)).card
  have hsum : Np + Nm = 2 ^ ω q := by
    rw [← card_sqfree_divisors (by omega : q ≠ 0), ← card_union_of_disjoint]
    · congr 1; ext d
      simp only [mem_union, mem_filter, ← moebius_ne_zero_iff_squarefree]
      constructor
      · rintro (⟨h, h1⟩ | ⟨h, h1⟩) <;> exact ⟨h, by omega⟩
      · rintro ⟨h, h1⟩; rcases moebius_cases d with h2 | h2 | h2
        · exact Or.inr ⟨h, h2⟩
        · exact absurd h2 h1
        · exact Or.inl ⟨h, h2⟩
    · exact disjoint_filter.mpr fun d _ h1 h2 => by omega
  have hdiff : (Np : ℤ) - Nm = 0 := by
    rw [← sum_moebius_divisors hq]
    simp only [Np, Nm, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rcases moebius_cases d with h | h | h <;> simp [h]
  omega

set_option maxHeartbeats 1000000 in
/-- **The size of `R_q`** (paper §3.3, Lemma Q(2)): for `q ≥ 2`,
`φ(q)R_q ≤ 2^{ω(q)−1}(1 + log 2 + log rad q) ≤ τ(q) log(2eq)/2`. -/
theorem Rq_bound {q : ℕ} (hq : 1 < q) :
    ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q))) ≤
      (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q)) := by
  have hq0 : q ≠ 0 := by omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hrad1 : (1 : ℝ) ≤ radQ q := by
    have : 0 < radQ q := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    exact_mod_cast this
  rw [Nat.sum_divisorsAntidiagonal (fun a b => termQ (μ a) (b * (1 / (2 * q))))]
  set g : ℕ → ℝ := fun a => (if μ a = 1 then Real.log 2 else 0) +
    (if μ a = -1 then 1 + Real.log (radQ q) else 0)
  have hterm : ∀ a ∈ q.divisors, termQ (μ a) ((q / a : ℕ) * (1 / (2 * q))) ≤ g a := by
    intro a ha
    have hdvd := Nat.dvd_of_mem_divisors ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hL : ((q / a : ℕ) : ℝ) * (1 / (2 * q)) = 1 / (2 * a) := by
      rw [Nat.cast_div hdvd (by exact_mod_cast ha0.ne')]; field_simp
    rw [hL]
    simp only [g]
    unfold termQ
    rcases moebius_cases a with h | h | h
    · rw [h]; simp only [show (-1 : ℤ) ≠ 1 by norm_num, if_false, if_true, zero_add]
      unfold betaQ
      rw [if_pos (by rw [div_le_one (by positivity)]; linarith)]
      have hsq : Squarefree a := moebius_ne_zero_iff_squarefree.mp (by rw [h]; norm_num)
      have hla : Real.log (Real.exp 1 / (2 * (1 / (2 * a)))) = 1 + Real.log a := by
        rw [show 2 * (1 / (2 * (a : ℝ))) = 1 / a by field_simp, div_div_eq_mul_div, div_one,
          Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      have hlog : Real.log a ≤ Real.log (radQ q) :=
        Real.log_le_log (by positivity) (by exact_mod_cast le_radQ hq0 hdvd hsq)
      have hk := kappa_le_half
      have hla0 : 0 ≤ Real.log a := Real.log_nonneg ha'
      refine max_le (by linarith) ((min_le_right _ _).trans ?_)
      rw [hla]; linarith
    · rw [h]; simp
    · rw [h]; simp only [if_true, show (1 : ℤ) ≠ -1 by norm_num, if_false, add_zero]
      exact min_le_left _ _
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  obtain ⟨h1, h2⟩ := card_moebius_pm hq
  simp only [g, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
  have e1 : (((q.divisors).filter (fun d => μ d = 1)).card : ℝ) = (2 : ℝ) ^ ω q / 2 := by
    rw [eq_div_iff (by norm_num), mul_comm]; exact_mod_cast h1
  have e2 : (((q.divisors).filter (fun d => μ d = -1)).card : ℝ) = (2 : ℝ) ^ ω q / 2 := by
    rw [eq_div_iff (by norm_num), mul_comm]; exact_mod_cast h2
  rw [e1, e2]; ring

/-- The last form: `φ(q)R_q ≤ τ(q) log(2eq)/2`. -/
theorem Rq_bound_tau {q : ℕ} (hq : 1 < q) :
    (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q)) ≤
      (q.divisors.card : ℝ) * Real.log (2 * Real.exp 1 * q) / 2 := by
  have hq0 : q ≠ 0 := by omega
  have hrad : (0 : ℝ) < radQ q := by
    have : 0 < radQ q := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    exact_mod_cast this
  have h2w : (2 : ℝ) ^ ω q ≤ q.divisors.card := by
    have h := card_sqfree_divisors hq0
    have : ((2 ^ ω q : ℕ) : ℝ) ≤ q.divisors.card := by rw [← h]; exact_mod_cast card_filter_le _ _
    exact_mod_cast this
  have hlog : 1 + Real.log 2 + Real.log (radQ q) ≤ Real.log (2 * Real.exp 1 * q) := by
    rw [Real.log_mul (by positivity) (by exact_mod_cast hq0), Real.log_mul (by norm_num)
      (Real.exp_pos 1).ne', Real.log_exp]
    have := Real.log_le_log hrad (Nat.cast_le.mpr (radQ_le hq0))
    linarith
  have h0 : 0 ≤ 1 + Real.log 2 + Real.log (radQ q) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ radQ q by
      have : 0 < radQ q := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      exact_mod_cast this)
    have := Real.log_two_gt_d9; linarith
  have : 0 ≤ (2 : ℝ) ^ ω q := by positivity
  calc (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q))
      ≤ (q.divisors.card : ℝ) / 2 * Real.log (2 * Real.exp 1 * q) := by gcongr
    _ = _ := by ring

/-- **Lemma Q(3)** (paper §3.3): for `X ≥ 1`, `A_q(X) ≤ κ·2^{ω(q)} ≤ κτ(q)`. -/
theorem lemmaQ3 {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 1 ≤ X) : Aq q X ≤ kappa * 2 ^ ω q := by
  have hX0 : 0 < X := by linarith
  rw [Aq_moebius hq0]
  have hterm : ∀ y ∈ q.divisorsAntidiagonal, (μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X) ≤
      if μ y.1 ≠ 0 then kappa else 0 := by
    intro y hy
    have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
    have hb : (1 : ℝ) ≤ y.2 := by exact_mod_cast hy2
    have habs := abs_avg_Gs_le (by positivity : (0 : ℝ) < y.2) hX0 ((y.2 : ℝ) / 2)
    have hk : kappa / (y.2 * X) ≤ kappa :=
      div_le_self kappa_nonneg (by nlinarith)
    rcases moebius_cases y.1 with h | h | h
    · rw [h, if_pos (by norm_num)]; push_cast
      linarith [neg_abs_le ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X)]
    · rw [h]; simp
    · rw [h, if_pos (by norm_num)]; push_cast
      linarith [le_abs_self ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X)]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => if μ a ≠ 0 then kappa else 0), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_comm]
  have e : (q.divisors.filter fun a => μ a ≠ 0) = q.divisors.filter Squarefree := by
    ext d; simp [moebius_ne_zero_iff_squarefree]
  rw [e, card_sqfree_divisors hq0.ne']; push_cast; ring

/-! ### Lemma Q(1) -/

theorem norm_cyc_neg_prod (q : ℕ) (h3 : q ≠ 0) (y : ℂ) :
    ‖(cyclotomic q ℂ).eval (-y)‖ = ∏ ν ∈ primitiveRoots q ℂ, ‖y + ν‖ := by
  rw [eval_cyclotomic_prod q h3, norm_prod]
  exact prod_congr rfl fun ν _ => by rw [show -y - ν = -(y + ν) by ring, norm_neg]

theorem norm_pair (x : ℝ) {ν : ℂ} (hν : ‖ν‖ = 1) :
    ‖ee x + ν‖ * ‖ee x + ν⁻¹‖ = |2 * ν.re + 2 * cos (2 * π * x)| := by
  have hy : ee x ≠ 0 := by unfold ee; exact Complex.exp_ne_zero _
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hyinv : ee x + (ee x)⁻¹ = ((2 * cos (2 * π * x) : ℝ) : ℂ) := by
    unfold ee
    rw [← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    push_cast; try ring_nf
  have hνinv : ν + ν⁻¹ = ((2 * ν.re : ℝ) : ℂ) := by
    rw [Complex.inv_eq_conj hν, Complex.add_conj]
    all_goals push_cast
    all_goals try ring
  have e : (ee x + ν) * (ee x + ν⁻¹) = ee x * (((2 * ν.re + 2 * cos (2 * π * x)) : ℝ) : ℂ) := by
    push_cast
    rw [show ((2 : ℂ) * ν.re + 2 * Complex.cos (2 * π * x)) = (ν + ν⁻¹) + (ee x + (ee x)⁻¹) by
      rw [hνinv, hyinv]; push_cast; ring]
    field_simp; ring
  rw [← norm_mul, e, norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- `|Φ_q(−e(x))|² = Π_ν |2 Re ν + 2 cos 2πx|` over the primitive `q`-th roots `ν`. -/
theorem norm_cyc_sq (q : ℕ) (h3 : q ≠ 0) (x : ℝ) :
    ‖(cyclotomic q ℂ).eval (-ee x)‖ ^ 2 =
      ∏ ν ∈ primitiveRoots q ℂ, |2 * ν.re + 2 * cos (2 * π * x)| := by
  have hroot : ∀ ν ∈ primitiveRoots q ℂ, IsPrimitiveRoot ν q := fun ν hν =>
    (mem_primitiveRoots (Nat.pos_of_ne_zero h3)).mp hν
  have hinv : ∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν‖ = ∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν⁻¹‖ := by
    have := prod_eq_prod_of_inj (s := primitiveRoots q ℂ) (t := primitiveRoots q ℂ) (fun z => z⁻¹)
      (fun z hz => (mem_primitiveRoots (Nat.pos_of_ne_zero h3)).mpr (hroot z hz).inv)
      (fun a _ b _ h => inv_injective h) le_rfl (fun ν => ((‖ee x + ν‖ : ℝ) : ℂ))
    rw [← Complex.ofReal_prod, ← Complex.ofReal_prod] at this
    exact_mod_cast this
  rw [norm_cyc_neg_prod q h3, sq]
  nth_rewrite 2 [hinv]
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun ν hν => norm_pair x ((hroot ν hν).norm'_eq_one h3)

/-- For `q ≥ 3` and `ν` a primitive `q`-th root, `Re ν ≥ −cos(π/q)`. -/
theorem re_prim_ge {q : ℕ} (h3 : 3 ≤ q) {ν : ℂ} (hν : IsPrimitiveRoot ν q) : -cos (π / q) ≤ ν.re := by
  obtain ⟨r, hr, hcop, rfl⟩ := (Complex.isPrimitiveRoot_iff ν q (by omega)).mp hν
  have h3' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [show (2 * π * Complex.I * (r / q) : ℂ) = ((2 * π * r / q : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]
  have hr0 : r ≠ 0 := by rintro rfl; simp at hcop; omega
  have h2r : 2 * r ≠ q := by
    rintro h
    have : r ∣ q := ⟨2, by omega⟩
    have h1 := Nat.Coprime.eq_one_of_dvd hcop this
    omega
  have hpi := Real.pi_pos
  rw [← Real.cos_pi_sub]
  rcases lt_or_gt_of_ne h2r with h | h
  · -- `2πr/q ≤ π − π/q`
    have h' : (2 * r + 1 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * r + 1 ≤ q)
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · have : π / q ≥ 0 := by positivity
      linarith
    · rw [div_le_iff₀ h3', sub_mul, div_mul_cancel₀ _ h3'.ne']; nlinarith
  · -- `2πr/q = 2π − 2π(q − r)/q` with `2π(q − r)/q ≤ π − π/q`
    have h' : (q + 1 : ℝ) ≤ 2 * r := by exact_mod_cast (by omega : q + 1 ≤ 2 * r)
    have hrq : (r : ℝ) < q := by exact_mod_cast hr
    rw [show 2 * π * r / q = 2 * π - 2 * π * (q - r) / q by field_simp; ring, Real.cos_two_pi_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · apply div_nonneg _ h3'.le; nlinarith
    · have : π / q ≥ 0 := by positivity
      linarith
    · rw [div_le_iff₀ h3', sub_mul, div_mul_cancel₀ _ h3'.ne']; nlinarith

/-- On `[0, 1/(2q))` every factor `2 Re ν + 2 cos 2πx` is positive and decreasing. -/
theorem factor_pos {q : ℕ} (h3 : 3 ≤ q) {ν : ℂ} (hν : IsPrimitiveRoot ν q) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x < 1 / (2 * q)) : 0 < 2 * ν.re + 2 * cos (2 * π * x) := by
  have h3' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpi := Real.pi_pos
  have hre := re_prim_ge h3 hν
  have h2 : 2 * π * x < π / q := by
    rw [lt_div_iff₀ h3']; rw [lt_div_iff₀ (by positivity)] at hx; nlinarith
  have hc : cos (π / q) < cos (2 * π * x) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by
      rw [div_le_iff₀ h3']; have : (1 : ℝ) ≤ q := by linarith [show (3 : ℝ) ≤ q by exact_mod_cast h3]
      nlinarith) h2
  linarith

/-- `h_q(x) = ½ Σ_ν log(2 Re ν + 2 cos 2πx)` on `[0, 1/(2q))`. -/
theorem hq_eq_sum {q : ℕ} (h3 : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / (2 * q)) :
    hq q x = (1 / 2) * ∑ ν ∈ primitiveRoots q ℂ, Real.log (2 * ν.re + 2 * cos (2 * π * x)) := by
  have hroot : ∀ ν ∈ primitiveRoots q ℂ, IsPrimitiveRoot ν q := fun ν hν =>
    (mem_primitiveRoots (by omega)).mp hν
  have hpos : ∀ ν ∈ primitiveRoots q ℂ, 0 < 2 * ν.re + 2 * cos (2 * π * x) := fun ν hν =>
    factor_pos h3 (hroot ν hν) hx0 hx
  have hsq := norm_cyc_sq q (by omega) x
  rw [prod_congr rfl fun ν hν => abs_of_pos (hpos ν hν)] at hsq
  unfold hq
  rw [← Real.log_prod (fun ν hν => (hpos ν hν).ne'), ← hsq, Real.log_pow]
  push_cast; ring

/-- **Lemma Q(1)** (paper §3.3): for `q ≥ 3`, `h_q` is strictly decreasing on `[0, 1/(2q))`. -/
theorem lemmaQ1 {q : ℕ} (h3 : 3 ≤ q) : StrictAntiOn (hq q) (Set.Ico 0 (1 / (2 * q))) := by
  intro x hx y hy hxy
  rw [hq_eq_sum h3 hx.1 hx.2, hq_eq_sum h3 hy.1 hy.2]
  have hroot : ∀ ν ∈ primitiveRoots q ℂ, IsPrimitiveRoot ν q := fun ν hν =>
    (mem_primitiveRoots (by omega)).mp hν
  have hne : (primitiveRoots q ℂ).Nonempty := by
    rw [← card_pos, Complex.card_primitiveRoots]; exact Nat.totient_pos.mpr (by omega)
  have h3' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpi := Real.pi_pos
  have hcos : cos (2 * π * y) < cos (2 * π * x) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by nlinarith [hx.1])
    · have := hy.2; rw [lt_div_iff₀ (by positivity)] at this
      have : (1 : ℝ) ≤ q := by linarith [show (3 : ℝ) ≤ q by exact_mod_cast h3]
      nlinarith
    · nlinarith
  have := sum_lt_sum_of_nonempty hne fun ν hν =>
    (show Real.log (2 * ν.re + 2 * cos (2 * π * y)) < Real.log (2 * ν.re + 2 * cos (2 * π * x)) from
      Real.log_lt_log (factor_pos h3 (hroot ν hν) hy.1 hy.2) (by linarith [hcos]))
  linarith

theorem hq_cont {q : ℕ} (h3 : 3 ≤ q) : ContinuousOn (hq q) (Set.Ico 0 (1 / (2 * q))) := by
  have hroot : ∀ ν ∈ primitiveRoots q ℂ, IsPrimitiveRoot ν q := fun ν hν =>
    (mem_primitiveRoots (by omega)).mp hν
  refine ContinuousOn.congr (f := fun x => (1 / 2) * ∑ ν ∈ primitiveRoots q ℂ,
    Real.log (2 * ν.re + 2 * cos (2 * π * x))) ?_ fun x hx => hq_eq_sum h3 hx.1 hx.2
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun ν hν => ?_)
  refine ContinuousOn.log (by fun_prop) fun x hx => (factor_pos h3 (hroot ν hν) hx.1 hx.2).ne'

/-- Consequences of Q(1): for `0 < X < 1/(2q)`, `A_q(X) < h_q(0) = log|Φ_q(−1)| = φ(q)c_q`, and
`A_q` is strictly decreasing on `(0, 1/(2q))`, so the first local minimum `X_q` of `A_q` is
`≥ 1/(2q)`. -/
theorem lemmaQ1_avg {q : ℕ} (h3 : 3 ≤ q) :
    (∀ X ∈ Set.Ioo (0 : ℝ) (1 / (2 * q)), Aq q X < hq q 0) ∧
      StrictAntiOn (Aq q) (Set.Ioo 0 (1 / (2 * q))) := by
  have hanti := lemmaQ1 h3
  have hc := hq_cont h3
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < 1 / (2 * q) →
      IntervalIntegrable (hq q) volume a b := fun a b ha hab hb =>
    (hc.mono (Set.Icc_subset_Ico ha hb)).intervalIntegrable_of_Icc hab
  -- strict average bound: `∫_a^b h < (b − a) h(a)`
  have hlt : ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 / (2 * q) →
      ∫ x in a..b, hq q x < (b - a) * hq q a := by
    intro a b ha hab hb
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      (hc.mono (Set.Icc_subset_Ico ha hb)) continuousOn_const
      (fun x hx => (hanti ⟨ha, by linarith [hx.2]⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1).le)
      ⟨b, ⟨hab.le, le_rfl⟩, hanti ⟨ha, by linarith⟩ ⟨by linarith, hb⟩ hab⟩
    simpa [intervalIntegral.integral_const, mul_comm] using this
  have hgt : ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 / (2 * q) →
      (b - a) * hq q b < ∫ x in a..b, hq q x := by
    intro a b ha hab hb
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      continuousOn_const (hc.mono (Set.Icc_subset_Ico ha hb))
      (fun x hx => by
        rcases eq_or_lt_of_le hx.2 with h | h
        · rw [h]
        · exact (hanti ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith, hb⟩ h).le)
      ⟨a, ⟨le_rfl, hab.le⟩, hanti ⟨ha, by linarith⟩ ⟨by linarith, hb⟩ hab⟩
    simpa [intervalIntegral.integral_const, mul_comm] using this
  refine ⟨fun X hX => ?_, fun X hX Y hY hXY => ?_⟩
  · unfold Aq
    rw [div_lt_iff₀ hX.1, mul_comm]
    simpa using hlt 0 X le_rfl hX.1 hX.2
  · unfold Aq
    have e := intervalIntegral.integral_add_adjacent_intervals (hint 0 X le_rfl hX.1.le hX.2)
      (hint X Y hX.1.le hXY.le hY.2)
    have h1 := hlt X Y hX.1.le hXY hY.2
    have h2 := hgt 0 X le_rfl hX.1 hX.2
    rw [div_lt_div_iff₀ hY.1 hX.1, ← e]
    have hX0 := hX.1
    -- `∫₀^X h > X h(X)` and `∫_X^Y h < (Y − X) h(X)` give `X ∫₀^Y h < Y ∫₀^X h`
    nlinarith

end ArcsAlgo.Core
