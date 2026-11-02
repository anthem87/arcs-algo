module

public import ArcsAlgo.EdgeBound
public import ArcsAlgo.EdgeGaussC
public import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false

/-!
# Theorem E(2), the vanishing factor: the core with the weight `−iw(t* + σ)` (paper §3.5)

* `core_ptC`: if `f(σ) = exp(Σ_{n≤5} κ_n(iσ)^n/n! + R)` with `κ₁ ∈ ℂ`, `κ₂ = s²` real and `|R| ≤ ρσ⁶`, then
  `|f(σ) − edgeIC(σ)| ≤ |e^{iκ₁σ − s²σ²/2}| Eb(|σ|)` (as `core_pt`, complex `κ₁`).
* `core_intV`: the core integral with the weight `−iw(t* + σ)` (the factor `−iwt` of the vanishing
  factor, which becomes `w·d/dT` after inversion) differs from `w(−it*·mainEC + d/dT mainEC)` by
  `(2π)^{−1}w(3(|t*|E_I + E_I′) + e^{−s²τ²/8}(|t*|T_I′ + T_I″))`, uniformly in `T`, when
  `|Im κ₁|τ ≤ 1` and `|Im κ₁| ≤ s²τ/4`.
* `EI1_le`, `TIs_le`: sizes of `E_I′`, `T_I′`, `T_I″`.

No hypothesis.
-/

open Finset Complex MeasureTheory Nat
open scoped Real

@[expose] public section

namespace ArcsAlgo.Edge

theorem norm_gaussXC (k1 : ℂ) (s σ : ℝ) :
    ‖Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)‖ = Real.exp (-(k1.im * σ) - s ^ 2 * σ ^ 2 / 2) := by
  rw [Complex.norm_exp]; congr 1
  simp [Complex.sub_re, Complex.mul_re, sq]

/-- **The core, pointwise, complex `κ₁`**: if `f(σ) = exp(Σ_{n≤5} κ_n(iσ)^n/n! + R)` with `κ₀ = 0`, `κ₁ = k₁`,
`κ₂ = s²` real, `|R| ≤ ρσ⁶` and `α₃|σ|³ + α₄σ⁴ + α₅|σ|⁵ + ρσ⁶ ≤ 1`, then
`|f(σ) − edgeIC(σ)| ≤ |e^{ik₁σ − s²σ²/2}| Eb(|σ|)`. -/
theorem core_ptC {κ : ℕ → ℂ} {k1 : ℂ} {s ρ σ : ℝ} {R : ℂ} (hρ0 : 0 ≤ ρ) (hk0 : κ 0 = 0) (h1 : κ 1 = k1)
    (h2 : κ 2 = ((s ^ 2 : ℝ) : ℂ)) (hR : ‖R‖ ≤ ρ * σ ^ 6)
    (hy : ‖κ 3‖ / 6 * |σ| ^ 3 + ‖κ 4‖ / 24 * σ ^ 4 + ‖κ 5‖ / 120 * |σ| ^ 5 + ρ * σ ^ 6 ≤ 1) :
    ‖Complex.exp (∑ n ∈ range 6, κ n * (I * σ) ^ n / (n ! : ℂ) + R) - edgeIC k1 s (κ 3) (κ 4) σ‖ ≤
      ‖Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)‖ *
        Eb (‖κ 3‖ / 6) (‖κ 4‖ / 24) (‖κ 5‖ / 120) ρ |σ| := by
  set κ₃ := κ 3
  set κ₄ := κ 4
  set κ₅ := κ 5
  set X := Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)
  set a3 := κ₃ * (I * σ) ^ 3 / 6
  set a4 := κ₄ * (I * σ) ^ 4 / 24
  set b := κ₅ * (I * σ) ^ 5 / 120 + R
  set Y := a3 + a4 + b
  have hexp : ∑ n ∈ range 6, κ n * (I * σ) ^ n / (n ! : ℂ) + R =
      (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) + Y := by
    simp only [sum_range_succ, sum_range_zero, hk0, h1, h2, Y, a3, a4, b, κ₃, κ₄, κ₅]
    simp only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one]
    push_cast
    linear_combination ((s : ℂ) ^ 2 * (σ : ℂ) ^ 2 / 2) * I_sq
  rw [hexp, Complex.exp_add]
  have hid : X * Complex.exp Y - edgeIC k1 s κ₃ κ₄ σ =
      X * ((Complex.exp Y - ∑ m ∈ range 3, Y ^ m / (m ! : ℂ)) + (b + a3 * (a4 + b) + (a4 + b) ^ 2 / 2)) := by
    unfold edgeIC
    simp only [sum_range_succ, sum_range_zero, Nat.factorial, Y]
    push_cast; ring
  rw [hid, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
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
    have : ‖R‖ ≤ ρ * x ^ 6 := by rw [← hσ6]; exact hR
    linarith
  have nY : ‖Y‖ ≤ α3 * x ^ 3 + α4 * x ^ 4 + (α5 * x ^ 5 + ρ * x ^ 6) := by
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le a3 a4
    linarith
  have hy' : α3 * x ^ 3 + α4 * x ^ 4 + (α5 * x ^ 5 + ρ * x ^ 6) ≤ 1 := by
    rw [← hσ4, ← hσ6]; linarith [hy]
  have hY1 : ‖Y‖ ≤ 1 := nY.trans hy'
  have hE := Complex.exp_bound hY1 (by norm_num : 0 < 3)
  have hE' : ‖Complex.exp Y - ∑ m ∈ range 3, Y ^ m / (m ! : ℂ)‖ ≤ 2 / 9 * ‖Y‖ ^ 3 := by
    refine hE.trans (le_of_eq ?_); simp [Nat.factorial]; ring
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

/-- The integrated core error with one more factor `|σ|`: `Σ_i c_i A_{m_i+1}/s^{m_i+2}`. -/
noncomputable def EI1 (α3 α4 α5 ρ s : ℝ) : ℝ :=
  ∑ i ∈ range 12, ebC α3 α4 α5 ρ i * Am (ebM i + 1) / s ^ (ebM i + 2)

theorem integrable_gEb1 {s : ℝ} (hs : 0 < s) (α3 α4 α5 ρ : ℝ) :
    Integrable fun σ : ℝ => |σ| * (Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|) := by
  simp_rw [Eb_eq, mul_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  have := (integrable_absmom (ebM i + 1) hs).const_mul (ebC α3 α4 α5 ρ i)
  refine this.congr (Filter.Eventually.of_forall fun σ => ?_); simp only; ring

theorem integral_gEb1 {s : ℝ} (hs : 0 < s) (α3 α4 α5 ρ : ℝ) :
    ∫ σ : ℝ, |σ| * (Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|) = EI1 α3 α4 α5 ρ s := by
  simp_rw [Eb_eq, mul_sum]
  rw [integral_finsetSum _ fun i _ => by
    have := (integrable_absmom (ebM i + 1) hs).const_mul (ebC α3 α4 α5 ρ i)
    exact this.congr (Filter.Eventually.of_forall fun σ => by simp only; ring)]
  unfold EI1
  refine sum_congr rfl fun i _ => ?_
  have e : (fun σ : ℝ => |σ| * (Real.exp (-(s ^ 2 * σ ^ 2) / 2) * (ebC α3 α4 α5 ρ i * |σ| ^ ebM i))) =
      fun σ => ebC α3 α4 α5 ρ i * (|σ| ^ (ebM i + 1) * Real.exp (-(s ^ 2 * σ ^ 2) / 2)) := by ext σ; ring
  rw [e, integral_const_mul, absmom_scale _ hs]; ring

/-- The tail constants with `s′ = s/2`: `∫ e^{−s′²σ²/2}(1 + α₃|σ|³ + α₄σ⁴ + α₃²σ⁶/2)` and the same with `|σ|`. -/
noncomputable def TIs (α3 α4 s : ℝ) : ℝ :=
  Am 0 / (s / 2) + α3 * Am 3 / (s / 2) ^ 4 + α4 * Am 4 / (s / 2) ^ 5 + α3 ^ 2 / 2 * Am 6 / (s / 2) ^ 7

noncomputable def TIs1 (α3 α4 s : ℝ) : ℝ :=
  Am 1 / (s / 2) ^ 2 + α3 * Am 4 / (s / 2) ^ 5 + α4 * Am 5 / (s / 2) ^ 6 + α3 ^ 2 / 2 * Am 7 / (s / 2) ^ 8

/-- `∫ |σ|^j e^{−s′²σ²/2}(1 + α₃|σ|³ + α₄|σ|⁴ + α₃²|σ|⁶/2)` for `j = 0, 1`. -/
theorem integral_tailpoly {s' : ℝ} (hs' : 0 < s') (α3 α4 : ℝ) (j : ℕ) :
    Integrable (fun σ : ℝ => |σ| ^ j * (Real.exp (-(s' ^ 2 * σ ^ 2) / 2) *
      (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6))) ∧
    ∫ σ : ℝ, |σ| ^ j * (Real.exp (-(s' ^ 2 * σ ^ 2) / 2) * (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)) =
      Am j / s' ^ (j + 1) + α3 * Am (j + 3) / s' ^ (j + 4) + α4 * Am (j + 4) / s' ^ (j + 5) +
        α3 ^ 2 / 2 * Am (j + 6) / s' ^ (j + 7) := by
  have e : (fun σ : ℝ => |σ| ^ j * (Real.exp (-(s' ^ 2 * σ ^ 2) / 2) *
      (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6))) = fun σ =>
      |σ| ^ j * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) + α3 * (|σ| ^ (j + 3) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) +
        α4 * (|σ| ^ (j + 4) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) +
        α3 ^ 2 / 2 * (|σ| ^ (j + 6) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) := by
    ext σ; simp only [pow_add]; ring
  have j0 : Integrable (fun σ : ℝ => |σ| ^ j * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) := integrable_absmom j hs'
  have j3 : Integrable (fun σ : ℝ => α3 * (|σ| ^ (j + 3) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
    (integrable_absmom (j + 3) hs').const_mul _
  have j4 : Integrable (fun σ : ℝ => α4 * (|σ| ^ (j + 4) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
    (integrable_absmom (j + 4) hs').const_mul _
  have j6 : Integrable (fun σ : ℝ => α3 ^ 2 / 2 * (|σ| ^ (j + 6) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) :=
    (integrable_absmom (j + 6) hs').const_mul _
  have j03 : Integrable (fun σ : ℝ => |σ| ^ j * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
      α3 * (|σ| ^ (j + 3) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) := j0.add j3
  have j034 : Integrable (fun σ : ℝ => |σ| ^ j * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) +
      α3 * (|σ| ^ (j + 3) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) +
      α4 * (|σ| ^ (j + 4) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2))) := j03.add j4
  rw [e]
  refine ⟨j034.add j6, ?_⟩
  rw [integral_add j034 j6, integral_add j03 j4, integral_add j0 j3,
    integral_const_mul, integral_const_mul, integral_const_mul, absmom_scale _ hs', absmom_scale _ hs',
    absmom_scale _ hs', absmom_scale _ hs']
  ring_nf

set_option maxHeartbeats 8000000 in
/-- **The core with the vanishing factor, integrated**: let `f(σ) = exp(Σ_{n≤5} κ_n(iσ)^n/n! + R(σ))` on
`|σ| ≤ τ` with `|R| ≤ ρσ⁶`, `κ₀ = 0`, `κ₁ = k₁ ∈ ℂ`, `κ₂ = s²` real. With the weight `−iw(t* + σ)`
(the factor `−iwt` of the vanishing factor), uniformly in `T`,
`|(2π)^{−1}∫_{−τ}^{τ} −iw(t* + σ) f(σ) e^{−iTσ} − w(−it*·mainEC(T) + mainEC′(T))|
  ≤ (2π)^{−1}w(3(|t*|E_I + E_I′) + e^{−s²τ²/8}(|t*|T_I′ + T_I″))`. -/
theorem core_intV (f : ℝ → ℂ) (hf : Continuous f) (κ : ℕ → ℂ) {k1 : ℂ} {s ρ τ w ts : ℝ} (hs : 0 < s)
    (hτ0 : 0 < τ) (hρ0 : 0 ≤ ρ) (hw : 0 ≤ w) (hk0 : κ 0 = 0) (h1 : κ 1 = k1) (h2 : κ 2 = ((s ^ 2 : ℝ) : ℂ))
    (hexp : ∀ σ : ℝ, |σ| ≤ τ → ∃ R : ℂ, ‖R‖ ≤ ρ * σ ^ 6 ∧
      f σ = Complex.exp (∑ n ∈ range 6, κ n * (I * σ) ^ n / (n ! : ℂ) + R))
    (hy : ‖κ 3‖ / 6 * τ ^ 3 + ‖κ 4‖ / 24 * τ ^ 4 + ‖κ 5‖ / 120 * τ ^ 5 + ρ * τ ^ 6 ≤ 1)
    (hyτ : |k1.im| * τ ≤ 1) (hyt : |k1.im| ≤ s ^ 2 * τ / 4) (T : ℝ) :
    ‖(1 / (2 * π) : ℂ) * (∫ σ in (-τ)..τ, (-(I * w * (ts + σ))) * f σ * Complex.exp (-(I * T * σ))) -
        w * (-(I * ts) * mainEC k1 s (κ 3) (κ 4) T + dmainEC k1 s (κ 3) (κ 4) T)‖ ≤
      1 / (2 * π) * (w * (3 * (|ts| * EI (‖κ 3‖ / 6) (‖κ 4‖ / 24) (‖κ 5‖ / 120) ρ s +
          EI1 (‖κ 3‖ / 6) (‖κ 4‖ / 24) (‖κ 5‖ / 120) ρ s) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs (‖κ 3‖ / 6) (‖κ 4‖ / 24) s +
          TIs1 (‖κ 3‖ / 6) (‖κ 4‖ / 24) s))) := by
  set κ₃ := κ 3
  set κ₄ := κ 4
  set α3 := ‖κ₃‖ / 6
  set α4 := ‖κ₄‖ / 24
  set α5 := ‖κ 5‖ / 120
  have hα3 : 0 ≤ α3 := by positivity
  have hα4 : 0 ≤ α4 := by positivity
  have hα5 : 0 ≤ α5 := by positivity
  set y := k1.im
  set m : ℝ → ℂ := fun σ => -(I * w * (ts + σ)) with hm
  have hnm : ∀ σ : ℝ, ‖m σ‖ ≤ w * (|ts| + |σ|) := by
    intro σ
    simp only [hm, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw]
    have : ‖((ts : ℂ) + σ)‖ = |ts + σ| := by rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    rw [this]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
  set F : ℝ → ℂ := fun σ => m σ * f σ * Complex.exp (-(I * T * σ)) with hF
  set g : ℝ → ℂ := fun σ => m σ * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) with hg
  have hg_eq : g = fun σ => (w * -(I * ts)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) +
      (w : ℂ) * ((-(I * σ)) * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ)))) := by
    ext σ; simp only [hg, hm]; ring
  have hgi1 := (integrable_edgeIC hs k1 κ₃ κ₄ T).const_mul ((w : ℂ) * -(I * ts))
  have hgi2 := (integrable_edgeIC_d hs k1 κ₃ κ₄ T).const_mul (w : ℂ)
  have hg_int : Integrable g := by rw [hg_eq]; exact hgi1.add hgi2
  have hmain : (1 / (2 * π) : ℂ) * ∫ σ, g σ = w * (-(I * ts) * mainEC k1 s κ₃ κ₄ T + dmainEC k1 s κ₃ κ₄ T) := by
    rw [hg_eq, integral_add hgi1 hgi2, integral_const_mul, integral_const_mul]
    have e1 := edge_mainC hs k1 κ₃ κ₄ T
    have e2 := edge_dmainC hs k1 κ₃ κ₄ T
    linear_combination (w * -(I * ts)) * e1 + (w : ℂ) * e2
  have hF_cont : Continuous F := by rw [hF]; simp only [hm]; fun_prop
  set S := Set.Ioc (-τ) τ
  have hS : MeasurableSet S := measurableSet_Ioc
  have hFS : IntegrableOn F S := (hF_cont.integrableOn_Icc (a := -τ) (b := τ)).mono_set Set.Ioc_subset_Icc_self
  have hint : ∫ σ in (-τ)..τ, (-(I * w * (ts + σ))) * f σ * Complex.exp (-(I * T * σ)) = ∫ σ in S, F σ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
  rw [hint, ← hmain, ← integral_add_compl hS hg_int]
  have hsplit : (1 / (2 * π) : ℂ) * (∫ σ in S, F σ) - (1 / (2 * π) : ℂ) * ((∫ σ in S, g σ) + ∫ σ in Sᶜ, g σ) =
      (1 / (2 * π) : ℂ) * ((∫ σ in S, (F σ - g σ)) - ∫ σ in Sᶜ, g σ) := by
    rw [integral_sub hFS hg_int.integrableOn]; ring
  rw [hsplit, norm_mul]
  have h2pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [h2pi]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
  rw [mul_add]
  refine add_le_add ?_ ?_
  · -- the core
    set G0 : ℝ → ℝ := fun σ => Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|
    set gC : ℝ → ℝ := fun σ => w * (3 * (|ts| * G0 σ + |σ| * G0 σ))
    have hG0 := integrable_gEb hs α3 α4 α5 ρ
    have hG1 := integrable_gEb1 hs α3 α4 α5 ρ
    have hgC : Integrable gC := ((hG0.const_mul |ts|).add hG1).const_mul 3 |>.const_mul w
    have hG0nn : ∀ σ, 0 ≤ G0 σ := fun σ => mul_nonneg (Real.exp_pos _).le (by
      rw [Eb_eq]; exact sum_nonneg fun i _ => mul_nonneg (ebC_nonneg hα3 hα4 hα5 hρ0 i) (by positivity))
    have hpt : ∀ᵐ σ ∂(volume.restrict S), ‖F σ - g σ‖ ≤ gC σ := by
      filter_upwards [ae_restrict_mem hS] with σ hσ
      have hσ' : |σ| ≤ τ := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
      obtain ⟨R, hR, hfσ⟩ := hexp σ hσ'
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
        linarith
      have hc := core_ptC hρ0 hk0 h1 h2 hR hyσ
      rw [← hfσ] at hc
      have hX : ‖Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2)‖ ≤ 3 * Real.exp (-(s ^ 2 * σ ^ 2) / 2) := by
        rw [norm_gaussXC]
        have h1 : -(y * σ) ≤ 1 := by
          have := neg_abs_le (y * σ); rw [abs_mul] at this
          have := mul_le_mul_of_nonneg_left hσ' (abs_nonneg y); linarith
        calc Real.exp (-(y * σ) - s ^ 2 * σ ^ 2 / 2) = Real.exp (-(y * σ)) * Real.exp (-(s ^ 2 * σ ^ 2) / 2) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp 1 * Real.exp (-(s ^ 2 * σ ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le
          _ ≤ 3 * Real.exp (-(s ^ 2 * σ ^ 2) / 2) :=
              mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
      simp only [hF, hg]
      have e : m σ * f σ * Complex.exp (-(I * T * σ)) - m σ * (edgeIC k1 s κ₃ κ₄ σ * Complex.exp (-(I * T * σ))) =
          m σ * (f σ - edgeIC k1 s κ₃ κ₄ σ) * Complex.exp (-(I * T * σ)) := by ring
      rw [e, norm_mul, norm_mul, norm_cexp_IT, mul_one]
      have hEb0 : 0 ≤ Eb α3 α4 α5 ρ |σ| := by
        rw [Eb_eq]; exact sum_nonneg fun i _ => mul_nonneg (ebC_nonneg hα3 hα4 hα5 hρ0 i) (by positivity)
      calc ‖m σ‖ * ‖f σ - edgeIC k1 s κ₃ κ₄ σ‖
          ≤ (w * (|ts| + |σ|)) * (3 * Real.exp (-(s ^ 2 * σ ^ 2) / 2) * Eb α3 α4 α5 ρ |σ|) :=
            mul_le_mul (hnm σ) (hc.trans (mul_le_mul_of_nonneg_right hX hEb0)) (norm_nonneg _) (by positivity)
        _ = gC σ := by simp only [gC, G0]; ring
    calc ‖∫ σ in S, (F σ - g σ)‖ ≤ ∫ σ in S, gC σ := norm_integral_le_of_norm_le hgC.integrableOn hpt
      _ ≤ ∫ σ, gC σ := setIntegral_le_integral hgC (Filter.Eventually.of_forall fun σ => by
          simp only [gC]; have := hG0nn σ; positivity)
      _ = w * (3 * (|ts| * EI α3 α4 α5 ρ s + EI1 α3 α4 α5 ρ s)) := by
          simp only [gC]
          rw [integral_const_mul, integral_const_mul, integral_add (hG0.const_mul _) hG1, integral_const_mul,
            integral_gEb hs, ← integral_gEb1 hs α3 α4 α5 ρ]
  · -- the tail of the main term
    set s' := s / 2 with hs'
    have hs'0 : 0 < s' := by positivity
    have hs'2 : s' ^ 2 = s ^ 2 / 4 := by rw [hs']; ring
    obtain ⟨hi0, hv0⟩ := integral_tailpoly hs'0 α3 α4 0
    obtain ⟨hi1, hv1⟩ := integral_tailpoly hs'0 α3 α4 1
    set P : ℝ → ℝ := fun σ => Real.exp (-(s' ^ 2 * σ ^ 2) / 2) * (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)
    set h2 : ℝ → ℝ := fun σ => w * (|ts| * (|σ| ^ 0 * P σ) + |σ| ^ 1 * P σ)
    have hh2 : Integrable h2 := ((hi0.const_mul |ts|).add hi1).const_mul w
    have hpt : ∀ᵐ σ ∂(volume.restrict Sᶜ), ‖g σ‖ ≤ Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ := by
      filter_upwards [ae_restrict_mem hS.compl] with σ hσ
      have hστ : τ ≤ |σ| := by
        simp only [S, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hσ
        rcases hσ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp only [hg]
      rw [norm_mul, norm_mul, norm_cexp_IT, mul_one]
      unfold edgeIC
      rw [norm_mul, norm_gaussXC]
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
      have hexp : Real.exp (-(y * σ) - s ^ 2 * σ ^ 2 / 2) ≤
          Real.exp (-(s ^ 2 * τ ^ 2) / 8) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2) := by
        rw [← Real.exp_add, hs'2]
        apply Real.exp_le_exp.mpr
        have hyσ : -(y * σ) ≤ s ^ 2 * τ / 4 * |σ| := by
          have := neg_abs_le (y * σ); rw [abs_mul] at this
          have := mul_le_mul_of_nonneg_right hyt (abs_nonneg σ); linarith
        have h1 : τ * |σ| ≤ σ ^ 2 := by
          rw [← sq_abs σ, sq]; exact mul_le_mul_of_nonneg_right hστ (abs_nonneg σ)
        have h2 : τ ^ 2 ≤ σ ^ 2 := by rw [← sq_abs σ]; exact pow_le_pow_left₀ hτ0.le hστ 2
        have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
        nlinarith [mul_le_mul_of_nonneg_left h1 hs2, mul_le_mul_of_nonneg_left h2 hs2]
      calc ‖m σ‖ * (Real.exp (-(y * σ) - s ^ 2 * σ ^ 2 / 2) *
            ‖1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72‖)
          ≤ (w * (|ts| + |σ|)) * ((Real.exp (-(s ^ 2 * τ ^ 2) / 8) * Real.exp (-(s' ^ 2 * σ ^ 2) / 2)) *
              (1 + α3 * |σ| ^ 3 + α4 * |σ| ^ 4 + α3 ^ 2 / 2 * |σ| ^ 6)) :=
            mul_le_mul (hnm σ) (mul_le_mul hexp hpoly (norm_nonneg _) (by positivity)) (by positivity)
              (by positivity)
        _ = Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ := by simp only [h2, P]; ring
    calc ‖∫ σ in Sᶜ, g σ‖ ≤ ∫ σ in Sᶜ, Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ :=
          norm_integral_le_of_norm_le (hh2.const_mul _).integrableOn hpt
      _ ≤ ∫ σ, Real.exp (-(s ^ 2 * τ ^ 2) / 8) * h2 σ :=
          setIntegral_le_integral (hh2.const_mul _) (Filter.Eventually.of_forall fun σ => by
            simp only [h2, P]; positivity)
      _ = w * (Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (|ts| * TIs α3 α4 s + TIs1 α3 α4 s)) := by
          rw [integral_const_mul]
          simp only [h2]
          rw [integral_const_mul, integral_add (hi0.const_mul _) hi1, integral_const_mul, hv0, hv1]
          unfold TIs TIs1; rw [← hs']; ring


/-! ### Sizes -/

theorem EI1_norm (α3 α4 α5 ρ : ℝ) {s : ℝ} (hs : 0 < s) :
    EI1 α3 α4 α5 ρ s = (1 / s ^ 2) * ∑ i ∈ range 12,
      ebC (α3 / s ^ 3) (α4 / s ^ 4) (α5 / s ^ 5) (ρ / s ^ 6) i * Am (ebM i + 1) := by
  simp only [EI1, ebC, ebM, sum_range_succ, sum_range_zero]
  field_simp
  ring

/-- `Λ′ = Σ_i A_{m_i+1}`. -/
noncomputable def LamE1 : ℝ := ∑ i ∈ range 12, Am (ebM i + 1)

theorem EI1_le {α3 α4 α5 ρ s M x : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (h5 : 0 ≤ α5) (hr : 0 ≤ ρ)
    (hM : 1 ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (b3 : α3 / s ^ 3 ≤ M * x) (b4 : α4 / s ^ 4 ≤ M * x ^ 2) (b5 : α5 / s ^ 5 ≤ M * x ^ 3)
    (br : ρ / s ^ 6 ≤ M * x ^ 4) :
    EI1 α3 α4 α5 ρ s ≤ 16 * (M ^ 3 * x ^ 3) * LamE1 / s ^ 2 := by
  rw [EI1_norm _ _ _ _ hs]
  have hb := ebC_bound (by positivity) (by positivity) (by positivity) (by positivity) hM hx0 hx1 b3 b4 b5 br
  have : ∑ i ∈ range 12, ebC (α3 / s ^ 3) (α4 / s ^ 4) (α5 / s ^ 5) (ρ / s ^ 6) i * Am (ebM i + 1) ≤
      ∑ i ∈ range 12, 16 * (M ^ 3 * x ^ 3) * Am (ebM i + 1) :=
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hb i hi) (Am_nonneg _)
  rw [← mul_sum] at this
  unfold LamE1
  rw [one_div_mul_eq_div, div_le_div_iff_of_pos_right (by positivity)]
  exact this

/-- `Λ₃ = 2A₀ + 16A₃ + 32A₄ + 64A₆`, `Λ₄ = 4A₁ + 32A₄ + 64A₅ + 128A₇`. -/
noncomputable def LamT3 : ℝ := 2 * Am 0 + 16 * Am 3 + 32 * Am 4 + 64 * Am 6
noncomputable def LamT4 : ℝ := 4 * Am 1 + 32 * Am 4 + 64 * Am 5 + 128 * Am 7

theorem TIs_le {α3 α4 s M : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (hM : 1 ≤ M)
    (b3 : α3 / s ^ 3 ≤ M) (b4 : α4 / s ^ 4 ≤ M) :
    TIs α3 α4 s ≤ M ^ 2 * LamT3 / s ∧ TIs1 α3 α4 s ≤ M ^ 2 * LamT4 / s ^ 2 := by
  set c3 := α3 / s ^ 3
  set c4 := α4 / s ^ 4
  have hc3 : 0 ≤ c3 := by positivity
  have hc4 : 0 ≤ c4 := by positivity
  have e1 : TIs α3 α4 s = (1 / s) * (2 * Am 0 + 16 * c3 * Am 3 + 32 * c4 * Am 4 + 64 * c3 ^ 2 * Am 6) := by
    simp only [TIs, c3, c4]; field_simp; ring
  have e2 : TIs1 α3 α4 s = (1 / s ^ 2) * (4 * Am 1 + 32 * c3 * Am 4 + 64 * c4 * Am 5 + 128 * c3 ^ 2 * Am 7) := by
    simp only [TIs1, c3, c4]; field_simp; ring
  have a0 := Am_nonneg 0
  have a1 := Am_nonneg 1
  have a3 := Am_nonneg 3
  have a4 := Am_nonneg 4
  have a5 := Am_nonneg 5
  have a6 := Am_nonneg 6
  have a7 := Am_nonneg 7
  have q3 : c3 ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hc3 b3 2
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM1 : 1 ≤ M ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [e1, one_div_mul_eq_div, div_le_div_iff_of_pos_right hs]
    unfold LamT3
    nlinarith [mul_le_mul_of_nonneg_right (b3.trans hM2) a3, mul_le_mul_of_nonneg_right (b4.trans hM2) a4,
      mul_le_mul_of_nonneg_right q3 a6, mul_le_mul_of_nonneg_right hM1 a0]
  · rw [e2, one_div_mul_eq_div, div_le_div_iff_of_pos_right (by positivity)]
    unfold LamT4
    nlinarith [mul_le_mul_of_nonneg_right (b3.trans hM2) a4, mul_le_mul_of_nonneg_right (b4.trans hM2) a5,
      mul_le_mul_of_nonneg_right q3 a7, mul_le_mul_of_nonneg_right hM1 a1]

end ArcsAlgo.Edge
