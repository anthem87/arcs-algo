module

public import ArcsAlgo.EdgeFactor
public import ArcsAlgo.EdgeGauss
set_option autoImplicit false

/-!
# Theorem E(2), the core: the Edgeworth expansion of a finite product (paper §3.5)

For weights `w ∈ W` with `w ≤ N` and complex `p_w`, `|p_w| ≤ K`:
* `kap W p j = Σ_w w^j j! c_j(p_w)`: the cumulants of Proposition C.
* `prod_expand`: for `|σ| ≤ τ`, `16KNτ ≤ 1`:
  `Π_w(1 + p_w(e^{iwσ} − 1)) = exp(Σ_{n≤5} κ_n(iσ)^n/n! + R)`, `|R| ≤ 2·8⁶K⁶σ⁶Σw⁶`.
* `core_pt`: with `κ₁ = k₁`, `κ₂ = s²` real, the product differs from
  `edgeI = e^{ik₁σ − s²σ²/2}(1 + κ₃(iσ)³/6 + κ₄(iσ)⁴/24 + κ₃²(iσ)⁶/72)` by at most `e^{−s²σ²/2}Eb(|σ|)`
  (`e^x = 1 + x + x²/2 + O(|x|³)`, all dropped products of cumulants kept in `Eb`).
* `mainE`, `edge_main`: `(2π)^{−1}∫ edgeI e^{−iTσ} = φ(z)/s·(1 + κ₃He₃/(6s³) + κ₄He₄/(24s⁴) + κ₃²He₆/(72s⁶))`.
* `core_int`: `|(2π)^{−1}∫_{−τ}^{τ} Π e^{−iTσ} dσ − mainE(T)| ≤ (2π)^{−1}(E_I + e^{−s²τ²/4}T_I)`, uniformly in
  `T`, with `E_I = Σ_i c_i A_{m_i}/s^{m_i+1}` and `T_I` explicit.

No hypothesis.
-/

open Finset Complex MeasureTheory Nat
open scoped Real

@[expose] public section

namespace ArcsAlgo.Edge

/-- The cumulants `κ_j = Σ_w w^j j! c_j(p_w)` of `Σ_w w·Bernoulli(p_w)` (Proposition C). -/
noncomputable def kap (W : Finset ℕ) (p : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ w ∈ W, (w : ℂ) ^ j * (j ! : ℂ) * cB (p w) j

/-- **The product of the factors**: for `|p_w| ≤ K`, `w ≤ N` and `|σ| ≤ τ` with `16KNτ ≤ 1`,
`Π_w (1 + p_w(e^{iwσ} − 1)) = exp(Σ_{n≤5} κ_n (iσ)^n/n! + R)`, `|R| ≤ 2·8⁶K⁶σ⁶ Σ_w w⁶`. -/
theorem prod_expand (W : Finset ℕ) (p : ℕ → ℂ) {K N τ : ℝ} (hK : 1 ≤ K) (hp : ∀ w ∈ W, ‖p w‖ ≤ K)
    (hW : ∀ w ∈ W, (w : ℝ) ≤ N) (hτ : 16 * K * N * τ ≤ 1) {σ : ℝ} (hσ : |σ| ≤ τ) :
    ∃ R : ℂ, ‖R‖ ≤ 2 * 8 ^ 6 * K ^ 6 * σ ^ 6 * ∑ w ∈ W, (w : ℝ) ^ 6 ∧
      ∏ w ∈ W, (1 + p w * (Complex.exp (I * w * σ) - 1)) =
        Complex.exp (∑ n ∈ range 6, kap W p n * (I * σ) ^ n / (n ! : ℂ) + R) := by
  have hK0 : 0 < K := by linarith
  have hx : ∀ w ∈ W, ‖I * (w : ℂ) * σ‖ ≤ 1 / (16 * K) := by
    intro w hw
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, le_div_iff₀ (by positivity)]
    have h1 : (w : ℝ) * |σ| ≤ N * τ := mul_le_mul (hW w hw) hσ (abs_nonneg _)
      (le_trans (Nat.cast_nonneg w) (hW w hw))
    nlinarith
  set R := ∑ w ∈ W, (psiB (p w) (I * w * σ) - ∑ n ∈ range 6, cB (p w) n * (I * w * σ) ^ n) with hRdef
  refine ⟨R, ?_, ?_⟩
  · refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun w hw => ?_
    refine ((psiB_expand hK (hp w hw) (hx w hw)).2).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
    have : |σ| ^ 6 = σ ^ 6 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    rw [mul_pow, mul_pow, mul_pow, this]; ring
  · have hprod : ∏ w ∈ W, (1 + p w * (Complex.exp (I * w * σ) - 1)) =
        ∏ w ∈ W, Complex.exp (psiB (p w) (I * w * σ)) :=
      prod_congr rfl fun w hw => (psiB_expand hK (hp w hw) (hx w hw)).1
    rw [hprod, ← Complex.exp_sum]
    congr 1
    have hk : ∑ n ∈ range 6, kap W p n * (I * σ) ^ n / (n ! : ℂ) =
        ∑ w ∈ W, ∑ n ∈ range 6, cB (p w) n * (I * w * σ) ^ n := by
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      unfold kap
      rw [sum_mul, sum_div]
      refine sum_congr rfl fun w _ => ?_
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp; ring
    rw [hk, hRdef, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => by ring

theorem cube_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : (u + v) ^ 3 ≤ 4 * u ^ 3 + 4 * v ^ 3 := by
  nlinarith [mul_nonneg (add_nonneg hu hv) (sq_nonneg (u - v))]

theorem sq_le2 (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (u - v)]

/-- The pointwise error polynomial of the core. -/
noncomputable def Eb (α3 α4 α5 ρ x : ℝ) : ℝ :=
  2 / 9 * (4 * α3 ^ 3 * x ^ 9 + 16 * α4 ^ 3 * x ^ 12 + 64 * α5 ^ 3 * x ^ 15 + 64 * ρ ^ 3 * x ^ 18) +
    α5 * x ^ 5 + ρ * x ^ 6 + α3 * α4 * x ^ 7 + α3 * α5 * x ^ 8 + α3 * ρ * x ^ 9 + α4 ^ 2 * x ^ 8 +
    2 * α5 ^ 2 * x ^ 10 + 2 * ρ ^ 2 * x ^ 12

/-- The Edgeworth integrand `e^{iκ₁σ − s²σ²/2}(1 + κ₃(iσ)³/6 + κ₄(iσ)⁴/24 + κ₃²(iσ)⁶/72)`. -/
noncomputable def edgeI (k1 s : ℝ) (κ₃ κ₄ : ℂ) (σ : ℝ) : ℂ :=
  Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) *
    (1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72)

theorem norm_gaussX (k1 s σ : ℝ) :
    ‖Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)‖ = Real.exp (-(s ^ 2 * σ ^ 2) / 2) := by
  rw [Complex.norm_exp]; congr 1
  simp [Complex.sub_re, Complex.mul_re, sq]; ring

/-- **The core, pointwise**: with `κ₁ = k₁` and `κ₂ = s²` real, `α_j = |κ_j|/j!`, `ρ = 2·8⁶K⁶Σw⁶`, and
`α₃|σ|³ + α₄σ⁴ + α₅|σ|⁵ + ρσ⁶ ≤ 1`:
`|Π_w(1 + p_w(e^{iwσ} − 1)) − edgeI(σ)| ≤ e^{−s²σ²/2} Eb(|σ|)`. -/
theorem core_pt (W : Finset ℕ) (p : ℕ → ℂ) {K N τ : ℝ} (hK : 1 ≤ K) (hp : ∀ w ∈ W, ‖p w‖ ≤ K)
    (hW : ∀ w ∈ W, (w : ℝ) ≤ N) (hτ : 16 * K * N * τ ≤ 1) {k1 s : ℝ} (h1 : kap W p 1 = k1)
    (h2 : kap W p 2 = ((s ^ 2 : ℝ) : ℂ)) {σ : ℝ} (hσ : |σ| ≤ τ)
    (hy : ‖kap W p 3‖ / 6 * |σ| ^ 3 + ‖kap W p 4‖ / 24 * σ ^ 4 + ‖kap W p 5‖ / 120 * |σ| ^ 5 +
      2 * 8 ^ 6 * K ^ 6 * (∑ w ∈ W, (w : ℝ) ^ 6) * σ ^ 6 ≤ 1) :
    ‖∏ w ∈ W, (1 + p w * (Complex.exp (I * w * σ) - 1)) - edgeI k1 s (kap W p 3) (kap W p 4) σ‖ ≤
      Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb (‖kap W p 3‖ / 6) (‖kap W p 4‖ / 24) (‖kap W p 5‖ / 120)
        (2 * 8 ^ 6 * K ^ 6 * ∑ w ∈ W, (w : ℝ) ^ 6) |σ| := by
  obtain ⟨R, hR, hPi⟩ := prod_expand W p hK hp hW hτ hσ
  set κ₃ := kap W p 3
  set κ₄ := kap W p 4
  set κ₅ := kap W p 5
  set ρ := 2 * 8 ^ 6 * K ^ 6 * ∑ w ∈ W, (w : ℝ) ^ 6 with hρ
  set X := Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)
  set a3 := κ₃ * (I * σ) ^ 3 / 6
  set a4 := κ₄ * (I * σ) ^ 4 / 24
  set b := κ₅ * (I * σ) ^ 5 / 120 + R
  set Y := a3 + a4 + b
  have hk0 : kap W p 0 = 0 := by simp [kap, cB]
  have hexp : ∑ n ∈ range 6, kap W p n * (I * σ) ^ n / (n ! : ℂ) + R =
      (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) + Y := by
    simp only [sum_range_succ, sum_range_zero, hk0, h1, h2, Y, a3, a4, b, κ₃, κ₄, κ₅]
    simp only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one]
    push_cast
    linear_combination ((s : ℂ) ^ 2 * (σ : ℂ) ^ 2 / 2) * I_sq
  rw [hPi, hexp, Complex.exp_add]
  have hid : X * Complex.exp Y - edgeI k1 s κ₃ κ₄ σ =
      X * ((Complex.exp Y - ∑ m ∈ range 3, Y ^ m / (m ! : ℂ)) + (b + a3 * (a4 + b) + (a4 + b) ^ 2 / 2)) := by
    unfold edgeI
    simp only [sum_range_succ, sum_range_zero, Nat.factorial, Y]
    push_cast; ring
  rw [hid, norm_mul, norm_gaussX]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set x := |σ| with hx
  have hx0 : 0 ≤ x := abs_nonneg σ
  have hσ4 : σ ^ 4 = x ^ 4 := by rw [hx, pow_abs, abs_of_nonneg (by positivity)]
  have hσ6 : σ ^ 6 = x ^ 6 := by rw [hx, pow_abs, abs_of_nonneg (by positivity)]
  set α3 := ‖κ₃‖ / 6
  set α4 := ‖κ₄‖ / 24
  set α5 := ‖κ₅‖ / 120
  have hα3 : 0 ≤ α3 := by positivity
  have hα4 : 0 ≤ α4 := by positivity
  have hα5 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hIσ : ∀ k : ℕ, ‖(I * (σ : ℂ)) ^ k‖ = x ^ k := by
    intro k; rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have na3 : ‖a3‖ = α3 * x ^ 3 := by
    simp only [a3, α3, norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
  have na4 : ‖a4‖ = α4 * x ^ 4 := by
    simp only [a4, α4, norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
  have nb : ‖b‖ ≤ α5 * x ^ 5 + ρ * x ^ 6 := by
    refine (norm_add_le _ _).trans ?_
    have : ‖κ₅ * (I * σ) ^ 5 / 120‖ = α5 * x ^ 5 := by
      simp only [α5, norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
    rw [this]
    have : ‖R‖ ≤ ρ * x ^ 6 := by rw [← hσ6, hρ]; linarith [hR]
    linarith
  have nY : ‖Y‖ ≤ α3 * x ^ 3 + α4 * x ^ 4 + (α5 * x ^ 5 + ρ * x ^ 6) := by
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le a3 a4
    linarith
  have hy' : α3 * x ^ 3 + α4 * x ^ 4 + (α5 * x ^ 5 + ρ * x ^ 6) ≤ 1 := by
    rw [← hσ4, ← hσ6]; rw [hρ] at *; linarith [hy]
  have hY1 : ‖Y‖ ≤ 1 := nY.trans hy'
  have hE := Complex.exp_bound hY1 (by norm_num : 0 < 3)
  have hE' : ‖Complex.exp Y - ∑ m ∈ range 3, Y ^ m / (m ! : ℂ)‖ ≤ 2 / 9 * ‖Y‖ ^ 3 := by
    refine hE.trans (le_of_eq ?_); simp [Nat.factorial]; ring
  -- the cube
  set u := α3 * x ^ 3
  set v := α4 * x ^ 4
  set bb := α5 * x ^ 5 + ρ * x ^ 6
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have hbb : 0 ≤ bb := by positivity
  have hY3 : ‖Y‖ ^ 3 ≤ 4 * u ^ 3 + 16 * v ^ 3 + 64 * (α5 * x ^ 5) ^ 3 + 64 * (ρ * x ^ 6) ^ 3 := by
    have h1 : ‖Y‖ ^ 3 ≤ (u + (v + bb)) ^ 3 := by
      have := pow_le_pow_left₀ (norm_nonneg _) nY 3; linarith [show u + v + bb = u + (v + bb) by ring]
    have h2 := cube_le hu (add_nonneg hv hbb)
    have h3 := cube_le hv hbb
    have h4 := cube_le (by positivity : 0 ≤ α5 * x ^ 5) (by positivity : 0 ≤ ρ * x ^ 6)
    nlinarith
  -- the second-order remainder
  have hrest : ‖b + a3 * (a4 + b) + (a4 + b) ^ 2 / 2‖ ≤ bb + u * (v + bb) + (v ^ 2 + bb ^ 2) := by
    have n1 : ‖a4 + b‖ ≤ v + bb := (norm_add_le _ _).trans (by rw [na4]; linarith)
    have n2 : ‖a3 * (a4 + b)‖ ≤ u * (v + bb) := by rw [norm_mul, na3]; exact mul_le_mul_of_nonneg_left n1 hu
    have n3 : ‖(a4 + b) ^ 2 / 2‖ ≤ v ^ 2 + bb ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      have := pow_le_pow_left₀ (norm_nonneg _) n1 2
      have := sq_le2 v bb
      linarith
    calc ‖b + a3 * (a4 + b) + (a4 + b) ^ 2 / 2‖ ≤ ‖b‖ + ‖a3 * (a4 + b)‖ + ‖(a4 + b) ^ 2 / 2‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ bb + u * (v + bb) + (v ^ 2 + bb ^ 2) := by linarith
  have hbb2 : bb ^ 2 ≤ 2 * (α5 * x ^ 5) ^ 2 + 2 * (ρ * x ^ 6) ^ 2 := sq_le2 _ _
  calc ‖(Complex.exp Y - ∑ m ∈ range 3, Y ^ m / (m ! : ℂ)) + (b + a3 * (a4 + b) + (a4 + b) ^ 2 / 2)‖
      ≤ 2 / 9 * ‖Y‖ ^ 3 + (bb + u * (v + bb) + (v ^ 2 + bb ^ 2)) := (norm_add_le _ _).trans (by linarith)
    _ ≤ Eb α3 α4 α5 ρ x := by
        unfold Eb
        have : 2 / 9 * ‖Y‖ ^ 3 ≤ 2 / 9 * (4 * u ^ 3 + 16 * v ^ 3 + 64 * (α5 * x ^ 5) ^ 3 + 64 * (ρ * x ^ 6) ^ 3) := by
          linarith
        simp only [u, v, bb] at this hbb2 ⊢
        nlinarith

/-- Coefficients and exponents of `Eb` as a sum of monomials. -/
noncomputable def ebC (α3 α4 α5 ρ : ℝ) : ℕ → ℝ
  | 0 => 8 / 9 * α3 ^ 3 | 1 => 32 / 9 * α4 ^ 3 | 2 => 128 / 9 * α5 ^ 3 | 3 => 128 / 9 * ρ ^ 3
  | 4 => α5 | 5 => ρ | 6 => α3 * α4 | 7 => α3 * α5 | 8 => α3 * ρ | 9 => α4 ^ 2
  | 10 => 2 * α5 ^ 2 | 11 => 2 * ρ ^ 2 | _ => 0

def ebM : ℕ → ℕ
  | 0 => 9 | 1 => 12 | 2 => 15 | 3 => 18 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 8
  | 10 => 10 | 11 => 12 | _ => 0

theorem Eb_eq (α3 α4 α5 ρ x : ℝ) : Eb α3 α4 α5 ρ x = ∑ i ∈ range 12, ebC α3 α4 α5 ρ i * x ^ ebM i := by
  simp [Eb, ebC, ebM, sum_range_succ]; ring

theorem ebC_nonneg {α3 α4 α5 ρ : ℝ} (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (h5 : 0 ≤ α5) (hρ : 0 ≤ ρ) (i : ℕ) :
    0 ≤ ebC α3 α4 α5 ρ i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [ebC] <;> positivity

/-- The integrated core error `Σ_i c_i A_{m_i}/s^{m_i+1}`. -/
noncomputable def EI (α3 α4 α5 ρ s : ℝ) : ℝ := ∑ i ∈ range 12, ebC α3 α4 α5 ρ i * Am (ebM i) / s ^ (ebM i + 1)

theorem integrable_gEb {s : ℝ} (hs : 0 < s) (α3 α4 α5 ρ : ℝ) :
    Integrable fun σ : ℝ => Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ| := by
  simp_rw [Eb_eq, mul_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  have := (integrable_absmom (ebM i) hs).const_mul (ebC α3 α4 α5 ρ i)
  refine this.congr (Filter.Eventually.of_forall fun σ => ?_); simp only; ring

theorem integral_gEb {s : ℝ} (hs : 0 < s) (α3 α4 α5 ρ : ℝ) :
    ∫ σ : ℝ, Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ| = EI α3 α4 α5 ρ s := by
  simp_rw [Eb_eq, mul_sum]
  rw [integral_finsetSum _ fun i _ => by
    have := (integrable_absmom (ebM i) hs).const_mul (ebC α3 α4 α5 ρ i)
    exact this.congr (Filter.Eventually.of_forall fun σ => by simp only; ring)]
  unfold EI
  refine sum_congr rfl fun i _ => ?_
  have e : (fun σ : ℝ => Real.exp (-(s ^ 2 * σ ^ 2) / 2) * (ebC α3 α4 α5 ρ i * |σ| ^ ebM i)) =
      fun σ => ebC α3 α4 α5 ρ i * (|σ| ^ ebM i * Real.exp (-(s ^ 2 * σ ^ 2) / 2)) := by ext σ; ring
  rw [e, integral_const_mul, absmom_scale _ hs]; ring

/-- The Edgeworth arc term `φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`,
`z = (T − κ₁)/s` (Proposition C, Theorem E(2)). -/
noncomputable def mainE (k1 s : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) : ℂ :=
  ((phiN ((T - k1) / s) / s : ℝ) : ℂ) *
    (1 + κ₃ * (He 3 ((T - k1) / s) : ℂ) / (6 * (s : ℂ) ^ 3) + κ₄ * (He 4 ((T - k1) / s) : ℂ) / (24 * (s : ℂ) ^ 4) +
      κ₃ ^ 2 * (He 6 ((T - k1) / s) : ℂ) / (72 * (s : ℂ) ^ 6))

theorem norm_cexp_IT (T σ : ℝ) : ‖Complex.exp (-(I * T * σ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

noncomputable def Ek (k : ℕ) (k1 s T σ : ℝ) : ℂ :=
  (I * σ) ^ k * Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ)

theorem integrable_Ek (k : ℕ) (k1 T : ℝ) {s : ℝ} (hs : 0 < s) : Integrable fun σ => Ek k k1 s T σ := by
  refine Integrable.mono' (integrable_absmom k hs) (by unfold Ek; fun_prop) ?_
  refine Filter.Eventually.of_forall fun σ => ?_
  unfold Ek
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp]
  apply le_of_eq; congr 2
  simp [Complex.sub_re, Complex.mul_re, sq]; ring

theorem edgeI_mul (k1 s : ℝ) (κ₃ κ₄ : ℂ) (T σ : ℝ) :
    edgeI k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) =
      Ek 0 k1 s T σ + κ₃ / 6 * Ek 3 k1 s T σ + κ₄ / 24 * Ek 4 k1 s T σ + κ₃ ^ 2 / 72 * Ek 6 k1 s T σ := by
  unfold edgeI Ek
  have : Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2 - I * T * σ) =
      Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) * Complex.exp (-(I * T * σ)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

theorem edge_main {s : ℝ} (hs : 0 < s) (k1 : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ σ : ℝ, edgeI k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) = mainE k1 s κ₃ κ₄ T := by
  simp_rw [edgeI_mul]
  have i0 : Integrable (fun σ => Ek 0 k1 s T σ) := integrable_Ek 0 k1 T hs
  have i3 : Integrable (fun σ => κ₃ / 6 * Ek 3 k1 s T σ) := (integrable_Ek 3 k1 T hs).const_mul (κ₃ / 6)
  have i4 : Integrable (fun σ => κ₄ / 24 * Ek 4 k1 s T σ) := (integrable_Ek 4 k1 T hs).const_mul (κ₄ / 24)
  have i6 : Integrable (fun σ => κ₃ ^ 2 / 72 * Ek 6 k1 s T σ) := (integrable_Ek 6 k1 T hs).const_mul (κ₃ ^ 2 / 72)
  have i03 : Integrable (fun σ => Ek 0 k1 s T σ + κ₃ / 6 * Ek 3 k1 s T σ) := i0.add i3
  have i034 : Integrable (fun σ => Ek 0 k1 s T σ + κ₃ / 6 * Ek 3 k1 s T σ + κ₄ / 24 * Ek 4 k1 s T σ) := i03.add i4
  rw [integral_add i034 i6, integral_add i03 i4, integral_add i0 i3,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have g : ∀ k, k ≤ 6 → (1 / (2 * π) : ℂ) * ∫ σ : ℝ, Ek k k1 s T σ =
      ((He k ((T - k1) / s) * phiN ((T - k1) / s) / s ^ (k + 1) : ℝ) : ℂ) := fun k hk => gauss_He hs k1 T hk
  have g0 := g 0 (by norm_num)
  have g3 := g 3 (by norm_num)
  have g4 := g 4 (by norm_num)
  have g6 := g 6 (by norm_num)
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold mainE
  set J0 := ∫ σ : ℝ, Ek 0 k1 s T σ
  set J3 := ∫ σ : ℝ, Ek 3 k1 s T σ
  set J4 := ∫ σ : ℝ, Ek 4 k1 s T σ
  set J6 := ∫ σ : ℝ, Ek 6 k1 s T σ
  have e : (1 / (2 * π) : ℂ) * (J0 + κ₃ / 6 * J3 + κ₄ / 24 * J4 + κ₃ ^ 2 / 72 * J6) =
      (1 / (2 * π) : ℂ) * J0 + κ₃ / 6 * ((1 / (2 * π) : ℂ) * J3) + κ₄ / 24 * ((1 / (2 * π) : ℂ) * J4) +
      κ₃ ^ 2 / 72 * ((1 / (2 * π) : ℂ) * J6) := by ring
  rw [e, g0, g3, g4, g6]
  simp only [He]; push_cast
  field_simp

/-- The tail constant `T_I = A₀/s′ + α₃A₃/s′⁴ + α₄A₄/s′⁵ + (α₃²/2)A₆/s′⁷`, `s′ = s/√2`. -/
noncomputable def TI (α3 α4 s : ℝ) : ℝ :=
  Am 0 / (s / √2) + α3 * Am 3 / (s / √2) ^ 4 + α4 * Am 4 / (s / √2) ^ 5 + α3 ^ 2 / 2 * Am 6 / (s / √2) ^ 7

set_option maxHeartbeats 4000000 in
/-- **The core, integrated**: under the hypotheses of `core_pt` on `|σ| ≤ τ` (with `τ > 0` and the
bound at `σ = τ`), for every `T`,
`|(2π)^{−1}∫_{−τ}^{τ} Π_w(1 + p_w(e^{iwσ} − 1)) e^{−iTσ} dσ − mainE(T)| ≤ (2π)^{−1}(E_I + e^{−s²τ²/4} T_I)`. -/
theorem core_int (W : Finset ℕ) (p : ℕ → ℂ) {K N τ : ℝ} (hK : 1 ≤ K) (hp : ∀ w ∈ W, ‖p w‖ ≤ K)
    (hW : ∀ w ∈ W, (w : ℝ) ≤ N) (hτ : 16 * K * N * τ ≤ 1) (hτ0 : 0 < τ) {k1 s : ℝ} (hs : 0 < s)
    (h1 : kap W p 1 = k1) (h2 : kap W p 2 = ((s ^ 2 : ℝ) : ℂ))
    (hy : ‖kap W p 3‖ / 6 * τ ^ 3 + ‖kap W p 4‖ / 24 * τ ^ 4 + ‖kap W p 5‖ / 120 * τ ^ 5 +
      2 * 8 ^ 6 * K ^ 6 * (∑ w ∈ W, (w : ℝ) ^ 6) * τ ^ 6 ≤ 1) (T : ℝ) :
    ‖(1 / (2 * π) : ℂ) * (∫ σ in (-τ)..τ, (∏ w ∈ W, (1 + p w * (Complex.exp (I * w * σ) - 1))) *
        Complex.exp (-(I * T * σ))) - mainE k1 s (kap W p 3) (kap W p 4) T‖ ≤
      1 / (2 * π) * (EI (‖kap W p 3‖ / 6) (‖kap W p 4‖ / 24) (‖kap W p 5‖ / 120)
          (2 * 8 ^ 6 * K ^ 6 * ∑ w ∈ W, (w : ℝ) ^ 6) s +
        Real.exp (-(s ^ 2 * τ ^ 2) / 4) * TI (‖kap W p 3‖ / 6) (‖kap W p 4‖ / 24) s) := by
  set κ₃ := kap W p 3
  set κ₄ := kap W p 4
  set α3 := ‖κ₃‖ / 6
  set α4 := ‖κ₄‖ / 24
  set α5 := ‖kap W p 5‖ / 120
  set ρ := 2 * 8 ^ 6 * K ^ 6 * ∑ w ∈ W, (w : ℝ) ^ 6 with hρ
  have hα3 : 0 ≤ α3 := by positivity
  have hα4 : 0 ≤ α4 := by positivity
  have hα5 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set F : ℝ → ℂ := fun σ => (∏ w ∈ W, (1 + p w * (Complex.exp (I * w * σ) - 1))) * Complex.exp (-(I * T * σ))
    with hF
  set f : ℝ → ℂ := fun σ => edgeI k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)) with hf
  have hf_int : Integrable f := by
    have : f = fun σ => Ek 0 k1 s T σ + κ₃ / 6 * Ek 3 k1 s T σ + κ₄ / 24 * Ek 4 k1 s T σ + κ₃ ^ 2 / 72 * Ek 6 k1 s T σ := by
      ext σ; exact edgeI_mul k1 s κ₃ κ₄ T σ
    rw [this]
    exact (((integrable_Ek 0 k1 T hs).add ((integrable_Ek 3 k1 T hs).const_mul _)).add
      ((integrable_Ek 4 k1 T hs).const_mul _)).add ((integrable_Ek 6 k1 T hs).const_mul _)
  have hF_cont : Continuous F := by rw [hF]; fun_prop
  set S := Set.Ioc (-τ) τ
  have hS : MeasurableSet S := measurableSet_Ioc
  have hFS : IntegrableOn F S := (hF_cont.integrableOn_Icc (a := -τ) (b := τ)).mono_set Set.Ioc_subset_Icc_self
  have hmain := edge_main hs k1 κ₃ κ₄ T
  rw [← hmain, intervalIntegral.integral_of_le (by linarith), ← integral_add_compl hS hf_int]
  have hsplit : (1 / (2 * π) : ℂ) * (∫ σ in S, F σ) - (1 / (2 * π) : ℂ) * ((∫ σ in S, f σ) + ∫ σ in Sᶜ, f σ) =
      (1 / (2 * π) : ℂ) * ((∫ σ in S, (F σ - f σ)) - ∫ σ in Sᶜ, f σ) := by
    rw [integral_sub hFS hf_int.integrableOn]; ring
  change ‖(1 / (2 * π) : ℂ) * (∫ σ in S, F σ) - (1 / (2 * π) : ℂ) * ((∫ σ in S, f σ) + ∫ σ in Sᶜ, f σ)‖ ≤ _
  rw [hsplit, norm_mul]
  have h2pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [h2pi]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
  · -- the core
    set g : ℝ → ℝ := fun σ => Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|
    have hg := integrable_gEb hs α3 α4 α5 ρ
    have hpt : ∀ᵐ σ ∂(volume.restrict S), ‖F σ - f σ‖ ≤ g σ := by
      filter_upwards [ae_restrict_mem hS] with σ hσ
      have hσ' : |σ| ≤ τ := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
      have hyσ : α3 * |σ| ^ 3 + α4 * σ ^ 4 + α5 * |σ| ^ 5 + ρ * σ ^ 6 ≤ 1 := by
        have e4 : σ ^ 4 = |σ| ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
        have e6 : σ ^ 6 = |σ| ^ 6 := by rw [pow_abs, abs_of_nonneg (by positivity)]
        rw [e4, e6]
        have p3 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 3
        have p4 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 4
        have p5 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 5
        have p6 := pow_le_pow_left₀ (abs_nonneg σ) hσ' 6
        have : α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α5 * |σ| ^ 5 + ρ * |σ| ^ 6 ≤
            α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 := by gcongr
        have e : α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 =
            ‖kap W p 3‖ / 6 * τ ^ 3 + ‖kap W p 4‖ / 24 * τ ^ 4 + ‖kap W p 5‖ / 120 * τ ^ 5 +
              2 * 8 ^ 6 * K ^ 6 * (∑ w ∈ W, (w : ℝ) ^ 6) * τ ^ 6 := by rw [hρ]; try ring
        linarith
      have hc := core_pt W p hK hp hW hτ h1 h2 hσ' (by
        have e : ‖kap W p 3‖ / 6 * |σ| ^ 3 + ‖kap W p 4‖ / 24 * σ ^ 4 + ‖kap W p 5‖ / 120 * |σ| ^ 5 +
            2 * 8 ^ 6 * K ^ 6 * (∑ w ∈ W, (w : ℝ) ^ 6) * σ ^ 6 = α3 * |σ| ^ 3 + α4 * σ ^ 4 + α5 * |σ| ^ 5 + ρ * σ ^ 6 := by
          rw [hρ]; try ring
        rw [e]; exact hyσ)
      simp only [hF, hf]
      rw [← sub_mul, norm_mul, norm_cexp_IT, mul_one]
      exact hc
    calc ‖∫ σ in S, (F σ - f σ)‖ ≤ ∫ σ in S, g σ := norm_integral_le_of_norm_le hg.integrableOn hpt
      _ ≤ ∫ σ, g σ := setIntegral_le_integral hg (Filter.Eventually.of_forall fun σ => by
          simp only [g]; exact mul_nonneg (Real.exp_pos _).le (by
            rw [Eb_eq]; exact sum_nonneg fun i _ => mul_nonneg (ebC_nonneg hα3 hα4 hα5 hρ0 i) (by positivity)))
      _ = EI α3 α4 α5 ρ s := integral_gEb hs α3 α4 α5 ρ
  · -- the tail of the main term
    set s' := s / √2 with hs'
    have hs'0 : 0 < s' := by positivity
    have hs'2 : s' ^ 2 = s ^ 2 / 2 := by rw [hs', div_pow, Real.sq_sqrt (by norm_num)]
    set h2 : ℝ → ℝ := fun σ => Real.exp (-(s' ^ 2 * σ ^ 2) / 2) * (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)
    have hh2 : Integrable h2 := by
      have e : h2 = fun σ => |σ| ^ 0 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
          α3 * (|σ| ^ 3 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) + α4 * (|σ| ^ 4 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) +
          α3 ^ 2 / 2 * (|σ| ^ 6 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) := by ext σ; simp only [h2]; ring
      rw [e]
      exact (((integrable_absmom 0 hs'0).add ((integrable_absmom 3 hs'0).const_mul _)).add
        ((integrable_absmom 4 hs'0).const_mul _)).add ((integrable_absmom 6 hs'0).const_mul _)
    have hint2 : ∫ σ, h2 σ = TI α3 α4 s := by
      have e : h2 = fun σ => |σ| ^ 0 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
          α3 * (|σ| ^ 3 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) + α4 * (|σ| ^ 4 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) +
          α3 ^ 2 / 2 * (|σ| ^ 6 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) := by ext σ; simp only [h2]; ring
      have j0 : Integrable (fun σ : ℝ => |σ| ^ 0 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) := integrable_absmom 0 hs'0
      have j3 : Integrable (fun σ : ℝ => α3 * (|σ| ^ 3 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
        (integrable_absmom 3 hs'0).const_mul _
      have j4 : Integrable (fun σ : ℝ => α4 * (|σ| ^ 4 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
        (integrable_absmom 4 hs'0).const_mul _
      have j6 : Integrable (fun σ : ℝ => α3 ^ 2 / 2 * (|σ| ^ 6 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
        (integrable_absmom 6 hs'0).const_mul _
      have j03 : Integrable (fun σ : ℝ => |σ| ^ 0 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
          α3 * (|σ| ^ 3 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) := j0.add j3
      have j034 : Integrable (fun σ : ℝ => |σ| ^ 0 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
          α3 * (|σ| ^ 3 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) + α4 * (|σ| ^ 4 * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
        j03.add j4
      rw [e]; beta_reduce
      rw [integral_add j034 j6, integral_add j03 j4, integral_add j0 j3,
        integral_const_mul, integral_const_mul, integral_const_mul, absmom_scale _ hs'0, absmom_scale _ hs'0,
        absmom_scale _ hs'0, absmom_scale _ hs'0]
      unfold TI; rw [← hs']; ring
    have hpt : ∀ᵐ σ ∂(volume.restrict Sᶜ), ‖f σ‖ ≤ Real.exp (-(s ^ 2 * τ ^ 2) / 4) * h2 σ := by
      filter_upwards [ae_restrict_mem hS.compl] with σ hσ
      have hστ : τ ≤ |σ| := by
        simp only [S, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hσ
        rcases hσ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp only [hf]
      rw [norm_mul, norm_cexp_IT, mul_one]
      unfold edgeI
      rw [norm_mul, norm_gaussX]
      have hIσ : ∀ k : ℕ, ‖(I * (σ : ℂ)) ^ k‖ = |σ| ^ k := by
        intro k; rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hpoly : ‖1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ ≤
          1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6 := by
        have n3 : ‖κ₃ * (I * σ) ^ 3 / 6‖ = α3 * |σ| ^ 3 := by
          rw [norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
        have n4 : ‖κ₄ * (I * σ) ^ 4 / 24‖ = α4 * |σ| ^ 4 := by
          rw [norm_div, norm_mul, hIσ, Complex.norm_ofNat]; ring
        have n6 : ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ = α3 ^ 2 / 2 * |σ| ^ 6 := by
          rw [norm_div, norm_mul, norm_pow, hIσ, Complex.norm_ofNat]; ring
        calc _ ≤ ‖(1 : ℂ) + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24‖ + ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ :=
              norm_add_le _ _
          _ ≤ ‖(1 : ℂ)‖ + ‖κ₃ * (I * σ) ^ 3 / 6‖ + ‖κ₄ * (I * σ) ^ 4 / 24‖ + ‖κ₃ ^ 2 * (I * σ) ^ 6 / 72‖ := by
              gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
          _ = _ := by rw [norm_one, n3, n4, n6]
      have hexp : Real.exp (-(s ^ 2 * σ ^ 2) / 2) ≤
          Real.exp (-(s ^ 2 * τ ^ 2) / 4) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) := by
        rw [← Real.exp_add, hs'2]
        apply Real.exp_le_exp.mpr
        have : τ ^ 2 ≤ σ ^ 2 := by
          rw [← sq_abs σ]; exact pow_le_pow_left₀ hτ0.le hστ 2
        nlinarith [sq_nonneg s]
      calc Real.exp (-(s ^ 2 * σ ^ 2) / 2) *
            ‖1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72‖
          ≤ (Real.exp (-(s ^ 2 * τ ^ 2) / 4) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) *
              (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6) :=
            mul_le_mul hexp hpoly (norm_nonneg _) (by positivity)
        _ = Real.exp (-(s ^ 2 * τ ^ 2) / 4) * h2 σ := by simp only [h2]; ring
    calc ‖∫ σ in Sᶜ, f σ‖ ≤ ∫ σ in Sᶜ, Real.exp (-(s ^ 2 * τ ^ 2) / 4) * h2 σ :=
          norm_integral_le_of_norm_le (hh2.const_mul _).integrableOn hpt
      _ ≤ ∫ σ, Real.exp (-(s ^ 2 * τ ^ 2) / 4) * h2 σ :=
          setIntegral_le_integral (hh2.const_mul _) (Filter.Eventually.of_forall fun σ => by
            simp only [h2]; positivity)
      _ = Real.exp (-(s ^ 2 * τ ^ 2) / 4) * TI α3 α4 s := by rw [integral_const_mul, hint2]

end ArcsAlgo.Edge
