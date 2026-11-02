module

public import ArcsAlgo.EdgeArc2
public import ArcsAlgo.EdgeCoreS
set_option autoImplicit false

/-!
# The core of an arc at its centre `a/q` (paper §3.5, Remark (the formula of Proposition C))

* `tilt_E`, `EI_scale`: `y²/(2(s² − (s/Λ)²)) ≤ y²/(2s²) + 1` for `y² ≤ Λ²s²`, `Λ ≥ 2`; `E_I` at width `s/Λ`.
* `kS_one_c`: `κ₁(a/q) = Σ_w w/2 + iν_{a/q}` (Proposition C at `a/q`).
* `HhatC`: `F*_N(a/q)·φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`, `z = (T − κ₁)/s` complex,
  the cumulants of Proposition C at `a/q`.
* `centre_size`, `thmC_core`: for `𝒱(a/q) = ∅` and `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`, uniformly in `T`,
  `|∫_{|θ−a/q|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)Ĥ_{a/q}(T)| ≤ |F*_N(a/q)|(e^{ν²/(2s²)}N^{−3/2+6ε}/s + e^{−N^{2ε}/(4096 log N)})`.

Hypotheses: `SiegelWalfisz`; the bound on `ν_{a/q}` is an explicit antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- With `s₁ = s/Λ`, `Λ ≥ 2` and `y² ≤ Λ²s²`: `y²/(2(s² − s₁²)) ≤ y²/(2s²) + 1`. -/
theorem tilt_E {y s Λ : ℝ} (hs : 0 < s) (hΛ : 2 ≤ Λ) (hy : y ^ 2 ≤ Λ ^ 2 * s ^ 2) :
    y ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2)) ≤ y ^ 2 / (2 * s ^ 2) + 1 := by
  have hΛ0 : 0 < Λ := by linarith
  have hd : s ^ 2 - (s / Λ) ^ 2 = s ^ 2 * (Λ ^ 2 - 1) / Λ ^ 2 := by field_simp
  have hΛ2 : 3 ≤ Λ ^ 2 - 1 := by nlinarith
  rw [hd]
  set u := y ^ 2 / s ^ 2 with hu
  have hs2 : 0 < s ^ 2 := by positivity
  have hu0 : 0 ≤ u := by positivity
  have huΛ : u ≤ Λ ^ 2 := by rw [hu, div_le_iff₀ hs2]; linarith
  have e1 : y ^ 2 / (2 * (s ^ 2 * (Λ ^ 2 - 1) / Λ ^ 2)) = u * Λ ^ 2 / (2 * (Λ ^ 2 - 1)) := by
    rw [hu]; field_simp
  have e2 : y ^ 2 / (2 * s ^ 2) = u / 2 := by rw [hu]; field_simp
  rw [e1, e2, div_le_iff₀ (by positivity)]
  nlinarith

/-- `E_I` at the narrower width `s/Λ`: `E_I(s/Λ) ≤ 16M³x³Λ^{10}L_E/s` under the bounds of `EI_le` at `s`,
when `Λ ≥ 1` and `Λ²x ≤ 1`. -/
theorem EI_scale {α3 α4 α5 ρ s M x Λ : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (h5 : 0 ≤ α5) (hr : 0 ≤ ρ)
    (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hx0 : 0 ≤ x) (hx1 : Λ ^ 2 * x ≤ 1)
    (b3 : α3 / s ^ 3 ≤ M * x) (b4 : α4 / s ^ 4 ≤ M * x ^ 2) (b5 : α5 / s ^ 5 ≤ M * x ^ 3)
    (br : ρ / s ^ 6 ≤ M * x ^ 4) :
    EI α3 α4 α5 ρ (s / Λ) ≤ 16 * (M ^ 3 * x ^ 3) * LamE * Λ ^ 10 / s := by
  have hΛ0 : 0 < Λ := by linarith
  have hs1 : 0 < s / Λ := by positivity
  have hsc : ∀ (u : ℝ) (k : ℕ), u / (s / Λ) ^ k = Λ ^ k * (u / s ^ k) := by
    intro u k; rw [div_pow]; field_simp
  have hMΛ : 1 ≤ M * Λ := by nlinarith
  have hΛk : ∀ k : ℕ, 1 ≤ Λ ^ k := fun k => one_le_pow₀ hΛ
  have hxM : 0 ≤ M * x := by positivity
  have c3 : α3 / (s / Λ) ^ 3 ≤ M * Λ * (Λ ^ 2 * x) := by
    rw [hsc]; nlinarith [mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ Λ ^ 3)]
  have c4 : α4 / (s / Λ) ^ 4 ≤ M * Λ * (Λ ^ 2 * x) ^ 2 := by
    rw [hsc]
    have := mul_le_mul_of_nonneg_left b4 (by positivity : (0 : ℝ) ≤ Λ ^ 4)
    have h : Λ ^ 4 * (M * x ^ 2) ≤ M * Λ * (Λ ^ 2 * x) ^ 2 := by
      have : Λ ^ 4 ≤ Λ ^ 5 := pow_le_pow_right₀ hΛ (by norm_num)
      have hm : 0 ≤ M * x ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hm]
    linarith
  have c5 : α5 / (s / Λ) ^ 5 ≤ M * Λ * (Λ ^ 2 * x) ^ 3 := by
    rw [hsc]
    have := mul_le_mul_of_nonneg_left b5 (by positivity : (0 : ℝ) ≤ Λ ^ 5)
    have h : Λ ^ 5 * (M * x ^ 3) ≤ M * Λ * (Λ ^ 2 * x) ^ 3 := by
      have : Λ ^ 5 ≤ Λ ^ 7 := pow_le_pow_right₀ hΛ (by norm_num)
      have hm : 0 ≤ M * x ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hm]
    linarith
  have cr : ρ / (s / Λ) ^ 6 ≤ M * Λ * (Λ ^ 2 * x) ^ 4 := by
    rw [hsc]
    have := mul_le_mul_of_nonneg_left br (by positivity : (0 : ℝ) ≤ Λ ^ 6)
    have h : Λ ^ 6 * (M * x ^ 4) ≤ M * Λ * (Λ ^ 2 * x) ^ 4 := by
      have : Λ ^ 6 ≤ Λ ^ 9 := pow_le_pow_right₀ hΛ (by norm_num)
      have hm : 0 ≤ M * x ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hm]
    linarith
  have h := EI_le hs1 h3 h4 h5 hr hMΛ (by positivity) hx1 c3 c4 c5 cr
  refine h.trans (le_of_eq ?_)
  field_simp

section params
variable {N q a : ℕ}

/-- **`κ₁` at the centre** (Proposition C at `a/q`): `κ₁(a/q) = Σ_w w/2 + iν_{a/q}`. -/
theorem kS_one_c (hq : 3 ≤ q) (hnv : ∀ w ∈ WN N, ¬ vanish q a w) :
    kS N ((a : ℝ) / q + 0 / (2 * π)) 1 =
      ((∑ w ∈ WN N, (w : ℝ) / 2 : ℝ) : ℂ) + I * (nuW (WN N) q a : ℂ) := by
  have hts : (N : ℝ) * |(0 : ℝ)| ≤ 1 / q := by simp
  have hfilt : (WN N).filter (fun w => ¬ vanish q a w) = WN N := filter_true_of_mem hnv
  have him := im_kappa1 (W := WN N) (q := q) (a := a) 0
  rw [Fw'_zero, neg_neg, hfilt] at him
  unfold kS kap
  have hterm : ∀ w ∈ WN N, (w : ℂ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℂ) * cB (pStar ((a : ℝ) / q + 0 / (2 * π)) w) 1 =
      (((w : ℝ) / 2 : ℝ) : ℂ) + I * (((w : ℝ) * (Real.tan (alw q a w + w * 0 / 2) / 2) : ℝ) : ℂ) := by
    intro w hw
    have hp := (p_types (cos_star_ne hq hnv hts hw)).2.2
    simp only [cB, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [pStar_eq]
    set P := Complex.exp (2 * ((alw q a w + w * 0 / 2 : ℝ) : ℂ) * I) /
        (1 + Complex.exp (2 * ((alw q a w + w * 0 / 2 : ℝ) : ℂ) * I))
    push_cast at hp ⊢
    linear_combination (w : ℂ) * hp
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum, him]

end params

end ArcsAlgo.Core

open Finset Complex MeasureTheory
open scoped Real

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- `Ĥ_{a/q}(T) = F*_N(a/q)·φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`, `z = (T − κ₁)/s`,
with the complex cumulants of Proposition C at `a/q`. -/
noncomputable def HhatC (N : ℕ) (θ T : ℝ) : ℂ :=
  FW (WN N) θ * mainEC (kS N θ 1) (sS N θ) (kS N θ 3) (kS N θ 4) T


set_option maxHeartbeats 8000000 in
/-- The size of the error of `core_intS` at the centre: `τ₀ = N^{−3/2+ε}`, `N = e^L`, `|ν| ≤ C_νN^{3/2+ε/2}`. -/
theorem centre_size {q L B ε τ s ν Cν A α3 α4 α5 ρ : ℝ} (hB : 0 < B) (hL0 : 0 < L) (hLone : 1 ≤ L)
    (hε0 : 0 < ε) (hε : ε < 1 / 8) (hq1 : 1 ≤ q) (hqL : q ≤ L ^ B) (hτe : τ = Real.exp ((-(3 / 2) + ε) * L))
    (hA : A = 4 * 8 ^ 6 * q ^ 6)
    (hα3 : α3 ≤ A * Real.exp (4 * L)) (hα4 : α4 ≤ A * Real.exp (5 * L)) (hα5 : α5 ≤ A * Real.exp (6 * L))
    (hρb : ρ ≤ A * Real.exp (7 * L)) (hα30 : 0 ≤ α3) (hα40 : 0 ≤ α4) (hα50 : 0 ≤ α5) (hρ0 : 0 ≤ ρ)
    (hsD : Real.exp (3 / 2 * L) / (16 * √L) ≤ s) (hs1 : 1 ≤ s) (hCν : 0 < Cν)
    (hnu' : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L))
    (hk1 : ((Cν + 2) * 16) ^ 2 * L ^ (1 : ℝ) ≤ Real.exp ((1 / 2 - ε) * √L))
    (hk4 : 48 * (4 * 8 ^ 6 * 16 ^ 6) ^ 3 * LamE * ((Cν + 2) * 16) ^ 10 * L ^ (18 * B + 14) ≤
      Real.exp (ε * √L))
    (hk5 : (4 * 8 ^ 6 * 16 ^ 6) ^ 2 * LamT3 * L ^ (12 * B + 6) ≤ Real.exp (1 * √L))
    (hk6 : 4096 * L ^ (3 / 2 : ℝ) ≤ Real.exp (2 * ε * √L)) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 < s ∧
      1 / (2 * π) * (Real.exp (ν ^ 2 / (2 * (s ^ 2 - s1 ^ 2))) * EI α3 α4 α5 ρ s1 +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs α3 α4 s) ≤
      Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) +
        Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L)) := by
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  have hLamE : 0 ≤ LamE := sum_nonneg fun i _ => Am_nonneg _
  have hLamT3 : 0 ≤ LamT3 := by unfold LamT3; have := Am_nonneg 0; have := Am_nonneg 3
                                have := Am_nonneg 4; have := Am_nonneg 6; positivity
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  set CΛ : ℝ := (Cν + 2) * 16 with hCΛ
  have hs0 : 0 < s := by linarith
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  set D := 16 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ q ^ 6 := one_le_pow₀ hq1; nlinarith
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _

  -- the size of the error
  set M := A * D ^ 6 with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [one_le_pow₀ (n := 6) hD1]
  set x := Real.exp (-(1 / 2) * L) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hxk : ∀ k : ℕ, x ^ k = Real.exp (-(k / 2 : ℝ) * L) := fun k => by
    rw [hx, ← Real.exp_nat_mul]; congr 1; ring
  have b3 : α3 / s ^ 3 ≤ M * x := by
    have := norm_cum (k := 3) (by norm_num) (by linarith) hD1 hα3 hsD
    rw [hx]; convert this using 2; push_cast; ring_nf
  have b4 : α4 / s ^ 4 ≤ M * x ^ 2 := by
    have := norm_cum (k := 4) (by norm_num) (by linarith) hD1 hα4 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have b5 : α5 / s ^ 5 ≤ M * x ^ 3 := by
    have := norm_cum (k := 5) (by norm_num) (by linarith) hD1 hα5 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have br : ρ / s ^ 6 ≤ M * x ^ 4 := by
    have := norm_cum (k := 6) (by norm_num) (by linarith) hD1 hρb hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  -- polylog factors
  have hMle : M ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hM, hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : (q : ℝ) ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hLB6 : 0 ≤ L ^ (6 * B) := by positivity
  have hpow : ∀ k : ℕ, (L ^ (6 * B) * L ^ 3) ^ k = L ^ ((6 * B + 3) * k) := by
    intro k
    have h63 : L ^ (6 * B) * L ^ 3 = L ^ (6 * B + 3) := by
      rw [Real.rpow_add hL0, show L ^ (3 : ℝ) = L ^ 3 by norm_cast]
    rw [h63, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  -- the tilt: `Λ = C_Λ√L e^{εL/2}`, `s₁ = s/Λ`
  have hCΛ2 : 32 ≤ CΛ := by rw [hCΛ]; nlinarith
  set Λ := CΛ * √L * Real.exp (ε / 2 * L) with hΛdef
  have hexpε : 1 ≤ Real.exp (ε / 2 * L) := Real.one_le_exp (by positivity)
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛdef]
    have : 32 ≤ CΛ * √L := by nlinarith
    nlinarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hνs : ν ^ 2 ≤ Λ ^ 2 * s ^ 2 := by
    have hΛs : |ν| ≤ Λ * s := by
      have h1 : CΛ * √L * Real.exp (ε / 2 * L) * (Real.exp (3 / 2 * L) / D) =
          (Cν + 2) * Real.exp ((3 / 2 + ε / 2) * L) := by
        have hsq0 : 0 < √L := by positivity
        rw [hCΛ, hD, show (3 / 2 + ε / 2) * L = ε / 2 * L + 3 / 2 * L by ring, Real.exp_add]
        field_simp <;> ring_nf
      have h2 : Λ * (Real.exp (3 / 2 * L) / D) ≤ Λ * s := mul_le_mul_of_nonneg_left hsD (by linarith)
      have h3 : Cν * Real.exp ((3 / 2 + ε / 2) * L) ≤ (Cν + 2) * Real.exp ((3 / 2 + ε / 2) * L) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      rw [hΛdef] at h2 ⊢; linarith
    have := pow_le_pow_left₀ (abs_nonneg ν) hΛs 2
    rw [sq_abs, mul_pow] at this; exact this
  have hΛx : Λ ^ 2 * x ≤ 1 := by
    have h1 := hk1; rw [Real.rpow_one] at h1
    have h1' : CΛ ^ 2 * L ≤ Real.exp ((1 / 2 - ε) * L) := h1.trans (Real.exp_le_exp.mpr (by nlinarith))
    have e : Λ ^ 2 * x = CΛ ^ 2 * L * Real.exp ((-(1 / 2) + ε) * L) := by
      have hsq : Real.exp (ε / 2 * L) ^ 2 = Real.exp (ε * L) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hΛdef, hx, mul_pow, mul_pow, Real.sq_sqrt hL0.le, hsq, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [e]
    have he : Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    nlinarith [Real.exp_pos ((-(1 / 2) + ε) * L)]
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ : 0 < s / Λ := div_pos hs0 hΛ0
  have hss1 : s / Λ < s := by rw [div_lt_iff₀ hΛ0]; nlinarith
  refine ⟨s / Λ, hsΛ, hss1, ?_⟩
  have hE : Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) ≤ Real.exp 1 * Real.exp (ν ^ 2 / (2 * s ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [tilt_E hs0 hΛ2 hνs])
  have hEIs := EI_scale hs0 hα30 hα40 hα50 hρ0 hM1 hΛ1 hx0 hΛx b3 b4 b5 br
  have hpoly : Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE * Λ ^ 10) ≤ Real.exp ((-(3 / 2) + 6 * ε) * L) := by
    have h := hk4
    have e : L ^ (18 * B + 14) = (L ^ (6 * B) * L ^ 3) ^ 3 * L ^ 5 := by
      rw [hpow, ← Real.rpow_natCast L 5, ← Real.rpow_add hL0]; congr 1; push_cast; ring
    have hm3 : M ^ 3 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 := pow_le_pow_left₀ hM0 (by linarith) 3
    have hΛ10 : Λ ^ 10 = CΛ ^ 10 * L ^ 5 * Real.exp (5 * ε * L) := by
      rw [hΛdef, mul_pow, mul_pow, show √L ^ 10 = (√L ^ 2) ^ 5 by ring, Real.sq_sqrt hL0.le,
        ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have hx3 : x ^ 3 = Real.exp (-(3 / 2) * L) := by rw [hxk]; congr 1 <;> push_cast <;> ring_nf
    have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hC : 3 * 16 * M ^ 3 * LamE * CΛ ^ 10 * L ^ 5 ≤ Real.exp (ε * L) := by
      calc 3 * 16 * M ^ 3 * LamE * CΛ ^ 10 * L ^ 5
          ≤ 3 * 16 * (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 * LamE * CΛ ^ 10 * L ^ 5 := by gcongr
        _ = 48 * K₀ ^ 3 * LamE * CΛ ^ 10 * L ^ (18 * B + 14) := by rw [e]; ring
        _ ≤ Real.exp (ε * √L) := h
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    rw [hΛ10, hx3]
    have hsplit : Real.exp ((-(3 / 2) + 6 * ε) * L) =
        Real.exp (ε * L) * (Real.exp (-(3 / 2) * L) * Real.exp (5 * ε * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [hsplit]
    have hP : 0 ≤ Real.exp (-(3 / 2) * L) * Real.exp (5 * ε * L) := by positivity
    have hQ : 0 ≤ 16 * M ^ 3 * LamE * CΛ ^ 10 * L ^ 5 := by positivity
    calc Real.exp 1 * (16 * (M ^ 3 * Real.exp (-(3 / 2) * L)) * LamE * (CΛ ^ 10 * L ^ 5 * Real.exp (5 * ε * L)))
        = Real.exp 1 * (16 * M ^ 3 * LamE * CΛ ^ 10 * L ^ 5) *
            (Real.exp (-(3 / 2) * L) * Real.exp (5 * ε * L)) := by ring
      _ ≤ 3 * (16 * M ^ 3 * LamE * CΛ ^ 10 * L ^ 5) * (Real.exp (-(3 / 2) * L) * Real.exp (5 * ε * L)) := by
          gcongr
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hP; linarith
  have hpart1 : Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * EI α3 α4 α5 ρ (s / Λ) ≤
      Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) := by
    have hEI0 : 0 ≤ EI α3 α4 α5 ρ (s / Λ) := by
      rw [EI_norm _ _ _ _ hsΛ]
      exact mul_nonneg (one_div_nonneg.mpr hsΛ.le) (sum_nonneg fun i _ => mul_nonneg (ebC_nonneg
        (div_nonneg hα30 (pow_pos hsΛ 3).le) (div_nonneg hα40 (pow_pos hsΛ 4).le)
        (div_nonneg hα50 (pow_pos hsΛ 5).le) (div_nonneg hρ0 (pow_pos hsΛ 6).le) i) (Am_nonneg _))
    calc Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * EI α3 α4 α5 ρ (s / Λ)
        ≤ (Real.exp 1 * Real.exp (ν ^ 2 / (2 * s ^ 2))) * (16 * (M ^ 3 * x ^ 3) * LamE * Λ ^ 10 / s) :=
          mul_le_mul hE hEIs hEI0 (by positivity)
      _ = Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE * Λ ^ 10) / s) := by ring
      _ ≤ Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) := by
          gcongr
  -- the tail
  have hE2 : Real.exp (2 * ε * L) / (256 * L) ≤ s ^ 2 * τ ^ 2 := by
    have h1' : (Real.exp (3 / 2 * L) / D) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 * τ ^ 2 = Real.exp (2 * ε * L) / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hτe, ← Real.exp_nat_mul,
        div_mul_eq_mul_div, ← Real.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right h1' (by positivity)
  have hpart2 : Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs α3 α4 s ≤
      Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L)) := by
    set E := Real.exp (2 * ε * L)
    have hEpos : 0 < E := Real.exp_pos _
    have h6 := hk6
    have hL32 : L ^ (3 / 2 : ℝ) = L * √L := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL0, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hL32] at h6
    have hsqE : √L ≤ E / (4096 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 4096 * (L * √L) ≤ E := h6.trans (Real.exp_le_exp.mpr (by nlinarith))
      linarith
    have hM2 : M ^ 2 * LamT3 ≤ Real.exp (√L) := by
      have h := hk5
      have e : L ^ (12 * B + 6) = (L ^ (6 * B) * L ^ 3) ^ 2 := by rw [hpow]; congr 1; push_cast; ring
      have hm2 : M ^ 2 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 := pow_le_pow_left₀ hM0 (by linarith) 2
      calc M ^ 2 * LamT3 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 * LamT3 := by gcongr
        _ = K₀ ^ 2 * LamT3 * L ^ (12 * B + 6) := by rw [e]; ring
        _ ≤ Real.exp (1 * √L) := h
        _ = _ := by rw [one_mul]
    have hTs : TIs α3 α4 s ≤ M ^ 2 * LamT3 := by
      have hb3 : α3 / s ^ 3 ≤ M := b3.trans (by nlinarith)
      have hb4 : α4 / s ^ 4 ≤ M := b4.trans (by nlinarith [pow_le_one₀ hx0 hx1 (n := 2)])
      refine (TIs_le hs0 hα30 hα40 hM1 hb3 hb4).1.trans ?_
      rw [div_le_iff₀ hs0]
      have : 0 ≤ M ^ 2 * LamT3 := by positivity
      nlinarith
    have hTI0 : 0 ≤ TIs α3 α4 s := by
      unfold TIs; have := Am_nonneg 0; have := Am_nonneg 3; have := Am_nonneg 4; have := Am_nonneg 6
      positivity
    calc Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs α3 α4 s
        ≤ Real.exp (-(E / (256 * L)) / 8) * (M ^ 2 * LamT3) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hTs hTI0 (Real.exp_pos _).le
      _ ≤ Real.exp (-(E / (256 * L)) / 8) * Real.exp (E / (4096 * L)) := by
          gcongr; exact hM2.trans (Real.exp_le_exp.mpr hsqE)
      _ = Real.exp (-E / (4096 * L)) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
  have h2pi : 1 / (2 * π) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hb1 : 0 ≤ Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) := by positivity
  have hb2 : 0 ≤ Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L)) := (Real.exp_pos _).le
  calc 1 / (2 * π) * (Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * EI α3 α4 α5 ρ (s / Λ) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs α3 α4 s)
      ≤ 1 / (2 * π) * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) +
          Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L))) := by gcongr
    _ ≤ 1 * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) +
          Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L))) := by gcongr
    _ = _ := one_mul _


set_option maxHeartbeats 16000000 in
/-- **The core at the centre `a/q`** (Remark (the formula of Proposition C), case `𝒱(a/q) = ∅`): fix `B > 0`,
`0 < ε < 1/8`, `C_ν > 0`, `τ₀ = N^{−3/2+ε}`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, `𝒱(a/q) = ∅` and
`|ν_{a/q}| ≤ C_ν N^{3/2+ε/2}`, uniformly in `T`:
`|∫_{|θ−a/q|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)Ĥ_{a/q}(T)|
  ≤ |F*_N(a/q)|(e^{ν²/(2s²)}N^{−3/2+6ε}/s + e^{−N^{2ε}/(4096 log N)})`, `s = √κ₂(a/q)`. -/
theorem thmC_core (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
      ∀ T : ℝ,
        ‖Rcore N ((a : ℝ) / q) ((N : ℝ) ^ (-(3 / 2 : ℝ) + ε)) T -
            ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ ≤
          ‖FW (WN N) ((a : ℝ) / q)‖ *
            (Real.exp (nuW (WN N) q a ^ 2 / (2 * sS N ((a : ℝ) / q) ^ 2)) *
                ((N : ℝ) ^ (-(3 / 2 : ℝ) + 6 * ε) / sS N ((a : ℝ) / q)) +
              Real.exp (-((N : ℝ) ^ (2 * ε)) / (4096 * Real.log N))) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  have hLamE : 0 ≤ LamE := sum_nonneg fun i _ => Am_nonneg _
  have hLamT3 : 0 ≤ LamT3 := by unfold LamT3; have := Am_nonneg 0; have := Am_nonneg 3
                                have := Am_nonneg 4; have := Am_nonneg 6; positivity
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  set CΛ : ℝ := (Cν + 2) * 16 with hCΛ
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp 1 hε1 (CΛ ^ 2)
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (6 * B) hε3 (16 * 8 ^ 6)
  obtain ⟨K₄, hK₄, hk4⟩ := ev_poly_exp (18 * B + 14) hε0 (48 * K₀ ^ 3 * LamE * CΛ ^ 10)
  obtain ⟨K₅, hK₅, hk5⟩ := ev_poly_exp (12 * B + 6) one_pos (K₀ ^ 2 * LamT3)
  obtain ⟨K₆, hK₆, hk6⟩ := ev_poly_exp (3 / 2) (by positivity : 0 < 2 * ε) 4096
  obtain ⟨K₇, hK₇, hk7⟩ := ev_poly_exp 1 one_pos 16
  obtain ⟨K₈, hK₈, hk8⟩ := ev_poly_exp 1 (by positivity : 0 < ε / 2) (1024 * Cν)
  set Kmax := max (max (max K₁ K₂) (max K₃ K₄)) (max (max K₅ K₆) (max K₇ K₈))
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha hnv hnu T => ?_⟩
  obtain ⟨-, hS2pos, -, -, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL4 : K₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL5 : K₅ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL6 : K₆ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL7 : K₇ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hL8 : K₈ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hnp : ∀ k : ℕ, Nr ^ k = Real.exp (k * L) := fun k => by rw [← hexpL, ← Real.exp_nat_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  -- the centre, written as `a/q + 0/(2π)`
  have hθ0 : (a : ℝ) / q = (a : ℝ) / q + 0 / (2 * π) := by simp
  rw [hθ0]
  set ts : ℝ := 0 with hts0
  have hts' : Nr * |ts| ≤ 1 / q := by rw [hts0]; simp
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  have hpar := fun w (hw : w ∈ WN N) => pStar_le hq hnv hts' hw
  have hne : ∀ w ∈ WN N, 1 + ee (w * θs) ≠ 0 := fun w hw => (hpar w hw).1
  have hpq : ∀ w ∈ WN N, ‖pStar θs w‖ ≤ q := fun w hw => (hpar w hw).2
  -- the cumulants
  set ν := nuW (WN N) q a with hν
  set k1 : ℂ := ((∑ w ∈ WN N, (w : ℝ) / 2 : ℝ) : ℂ) + I * (ν : ℂ) with hk1d
  have h1 : kap (WN N) (pStar θs) 1 = k1 := kS_one_c hq hnv
  have hk1im : k1.im = ν := by rw [hk1d]; simp
  set X : ℝ := ∑ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) with hX
  have h2X : kap (WN N) (pStar θs) 2 = (X : ℂ) := kS_two hq hnv hts'
  have hfilt : (WN N).filter (fun w => ¬ vanish q a w) = WN N := filter_true_of_mem hnv
  have htsw : |ts| < π / (q * Nr) := by rw [hts0, abs_zero]; positivity
  have hXge : S2W (WN N) q a / 4 ≤ X := by
    have := kappa2_ge (W := WN N) (q := q) (a := a) (by omega) (by omega)
      (fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)) htsw
    rwa [hfilt] at this
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXge
  set s := sS N θs with hsdef
  have hsX : s = √X := by rw [hsdef]; unfold sS kS; rw [h2X, Complex.ofReal_re]
  have hs0 : 0 < s := by rw [hsX]; exact Real.sqrt_pos.mpr hX0
  have hs2 : s ^ 2 = X := by rw [hsX, Real.sq_sqrt hX0.le]
  have h2 : kap (WN N) (pStar θs) 2 = ((s ^ 2 : ℝ) : ℂ) := by rw [hs2]; exact h2X
  -- `s ≥ N^{3/2}/D`, `D = 16√L`
  set D := 16 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hsD : Real.exp (3 / 2 * L) / D ≤ s := by
    rw [hsX, Real.le_sqrt (by positivity) hX0.le]
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 = Nr ^ 3 / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hnp 3]
      congr 1; push_cast; ring_nf; ring
    rw [e]
    have := hS2lo
    have e2 : Nr ^ 3 / (256 * L) = Nr ^ 3 / (64 * L) / 4 := by field_simp; ring
    linarith
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ hsD
    rw [le_div_iff₀ (by positivity), one_mul, hD]
    have h7 := hk7 L hL7; rw [Real.rpow_one, one_mul] at h7
    calc 16 * √L ≤ 16 * L := by linarith
      _ ≤ Real.exp (√L) := h7
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  -- the size of the cumulants
  set A : ℝ := 4 * 8 ^ 6 * (q : ℝ) ^ 6 with hA
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ (q : ℝ) ^ 6 := one_le_pow₀ hq1; nlinarith
  have hWN : ∀ w ∈ WN N, (w : ℝ) ≤ Nr := fun w hw => WN_le hw
  have hα : ∀ j : ℕ, 3 ≤ j → j ≤ 5 → ‖kap (WN N) (pStar θs) j‖ / (Nat.factorial j : ℝ) ≤
      A * Real.exp ((j + 1) * L) := by
    intro j hj3 hj5
    have h := kap_le (WN N) (pStar θs) hq1 hpq j
    have hsum := sum_pow_WN (N := N) (by omega) j
    have hf : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
    rw [div_le_iff₀ hf]
    have hqj : (q : ℝ) ^ j ≤ (q : ℝ) ^ 6 := pow_le_pow_right₀ hq1 (by omega)
    have hNj : Nr ^ (j + 1) = Real.exp ((j + 1) * L) := by rw [hnp]; push_cast; ring_nf
    rw [← hNr] at hsum
    calc ‖kap (WN N) (pStar θs) j‖ ≤ (Nat.factorial j : ℝ) * 25 * (q : ℝ) ^ j * (2 * Nr ^ (j + 1)) :=
          h.trans (by gcongr)
      _ ≤ (Nat.factorial j : ℝ) * 25 * (q : ℝ) ^ 6 * (2 * Nr ^ (j + 1)) := by gcongr
      _ ≤ A * Nr ^ (j + 1) * (Nat.factorial j : ℝ) := by
          rw [hA]; have : (0 : ℝ) ≤ (q : ℝ) ^ 6 * Nr ^ (j + 1) * (Nat.factorial j : ℝ) := by positivity
          nlinarith
      _ = A * Real.exp ((j + 1) * L) * (Nat.factorial j : ℝ) := by rw [hNj]
  set α3 := ‖kap (WN N) (pStar θs) 3‖ / 6
  set α4 := ‖kap (WN N) (pStar θs) 4‖ / 24
  set α5 := ‖kap (WN N) (pStar θs) 5‖ / 120
  set ρ := 2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ WN N, (w : ℝ) ^ 6 with hρ
  have hα3 : α3 ≤ A * Real.exp (4 * L) := by
    have := hα 3 le_rfl (by norm_num); norm_num [Nat.factorial] at this; exact this
  have hα4 : α4 ≤ A * Real.exp (5 * L) := by
    have := hα 4 (by norm_num) (by norm_num); norm_num [Nat.factorial] at this; exact this
  have hα5 : α5 ≤ A * Real.exp (6 * L) := by
    have := hα 5 (by norm_num) le_rfl; norm_num [Nat.factorial] at this; exact this
  have hρb : ρ ≤ A * Real.exp (7 * L) := by
    have hsum := sum_pow_WN (N := N) (by omega) 6
    rw [← hNr, show (6 + 1 : ℕ) = 7 from rfl, hnp] at hsum
    rw [hρ, hA]; push_cast at hsum
    have : (0 : ℝ) ≤ 2 * 8 ^ 6 * (q : ℝ) ^ 6 := by positivity
    nlinarith
  have hα30 : 0 ≤ α3 := by positivity
  have hα40 : 0 ≤ α4 := by positivity
  have hα50 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  -- the window conditions
  set τ := Nr ^ (-(3 / 2 : ℝ) + ε) with hτdef
  have hτe : τ = Real.exp ((-(3 / 2) + ε) * L) := hrp _
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
  have hτ : 16 * q * Nr * τ ≤ 1 := by
    have h := hk2 L hL2
    have h' : 16 * (q : ℝ) ≤ Real.exp ((1 / 2 - ε) * L) :=
      (by nlinarith : 16 * (q : ℝ) ≤ 16 * L ^ B).trans (h.trans (Real.exp_le_exp.mpr (by nlinarith)))
    have e : Nr * τ = Real.exp ((-(1 / 2) + ε) * L) := by
      rw [hτe, ← hexpL, ← Real.exp_add]; congr 1; ring
    have he : Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc 16 * q * Nr * τ = 16 * q * (Nr * τ) := by ring
      _ ≤ Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) := by
          rw [e]; exact mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = 1 := he
  have hy : α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 ≤ 1 := by
    have hτk : ∀ k : ℕ, τ ^ k = Real.exp (k * ((-(3 / 2) + ε) * L)) := fun k => by
      rw [hτe, ← Real.exp_nat_mul]
    set E0 := Real.exp ((-(1 / 2) + 3 * ε) * L)
    have hterm : ∀ (u : ℝ) (j : ℕ), 3 ≤ j → u ≤ A * Real.exp ((j + 1) * L) → u * τ ^ j ≤ A * E0 := by
      intro u j hj hu
      rw [hτk]
      calc u * Real.exp (j * ((-(3 / 2) + ε) * L)) ≤ A * Real.exp ((j + 1) * L) * Real.exp (j * ((-(3 / 2) + ε) * L)) :=
            mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
        _ = A * Real.exp ((1 - j * (1 / 2 - ε)) * L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ A * E0 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
            have : (3 : ℝ) ≤ j := by exact_mod_cast hj
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr this) hε1.le) hL0.le]
    have t3 := hterm α3 3 le_rfl (by norm_num; exact hα3)
    have t4 := hterm α4 4 (by norm_num) (by norm_num; exact hα4)
    have t5 := hterm α5 5 (by norm_num) (by norm_num; exact hα5)
    have t6 := hterm ρ 6 (by norm_num) (by norm_num; exact hρb)
    have h4A : 4 * A * E0 ≤ 1 := by
      have h := hk3 L hL3
      have hq6 : (q : ℝ) ^ 6 ≤ L ^ (6 * B) := by
        rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
        exact pow_le_pow_left₀ (by linarith) hqL 6
      have h' : 4 * A ≤ Real.exp ((1 / 2 - 3 * ε) * L) := by
        rw [hA]
        calc 4 * (4 * 8 ^ 6 * (q : ℝ) ^ 6) = 16 * 8 ^ 6 * (q : ℝ) ^ 6 := by ring
          _ ≤ 16 * 8 ^ 6 * L ^ (6 * B) := by gcongr
          _ ≤ Real.exp ((1 / 2 - 3 * ε) * √L) := h
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
      have he : Real.exp ((1 / 2 - 3 * ε) * L) * E0 = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      nlinarith [Real.exp_pos ((-(1 / 2) + 3 * ε) * L)]
    linarith
  have hnu' : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L) := by rw [← hrp]; exact hnu
  have hτ2 : Real.exp ((3 / 2 + ε) * L) / (256 * L) ≤ s ^ 2 * τ := by
    have h1' : (Real.exp (3 / 2 * L) / D) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 * τ = Real.exp ((3 / 2 + ε) * L) / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hτe, div_mul_eq_mul_div,
        ← Real.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right h1' hτ0.le
  have hyt : |k1.im| ≤ s ^ 2 * τ / 4 := by
    rw [hk1im]
    have h8 := hk8 L hL8; rw [Real.rpow_one] at h8
    have h8' : 1024 * Cν * L ≤ Real.exp (ε / 2 * L) := h8.trans (Real.exp_le_exp.mpr (by nlinarith))
    have he : Real.exp ((3 / 2 + ε) * L) = Real.exp (ε / 2 * L) * Real.exp ((3 / 2 + ε / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    have hq : Cν * Real.exp ((3 / 2 + ε / 2) * L) ≤ Real.exp ((3 / 2 + ε) * L) / (256 * L) / 4 := by
      rw [he, div_div, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right h8' (Real.exp_pos ((3 / 2 + ε / 2) * L)).le
      nlinarith [Real.exp_pos ((3 / 2 + ε / 2) * L)]
    linarith
  obtain ⟨s1, hs10, hs1s, hsz⟩ := centre_size (q := (q : ℝ)) hB hL0 hLone hε0 hε hq1 hqL hτe hA hα3 hα4 hα5 hρb
    hα30 hα40 hα50 hρ0 hsD hs1 hCν hnu' (hk1 L hL1) (hk4 L hL4) (hk5 L hL5) (hk6 L hL6)
  -- the core lemma
  have hk0 : kap (WN N) (pStar θs) 0 = 0 := by simp [kap, cB]
  set f : ℝ → ℂ := fun σ => ∏ w ∈ WN N, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1)) with hfdef
  have hf : Continuous f := by rw [hfdef]; fun_prop
  have hexpf : ∀ σ : ℝ, |σ| ≤ τ → ∃ R : ℂ, ‖R‖ ≤ ρ * σ ^ 6 ∧
      f σ = Complex.exp (∑ n ∈ range 6, kap (WN N) (pStar θs) n * (I * σ) ^ n / (n.factorial : ℂ) + R) := by
    intro σ hσ
    obtain ⟨R, hR, he⟩ := prod_expand (WN N) (pStar θs) hq1 hpq hWN hτ hσ
    exact ⟨R, hR.trans (le_of_eq (by rw [hρ]; ring)), he⟩
  have hcore := core_intS f hf (kap (WN N) (pStar θs)) (s1 := s1) (a := 1) (b := 0) 1 0 hs0
    hs10 hs1s hτ0 hρ0 (by simp) (by simp) hk0 h1 h2 hexpf hy hyt T
  -- the identity
  have hid : Rcore N θs τ T - ee (-(T * θs)) * HhatC N θs T =
      FW (WN N) θs * ee (-(T * θs)) * ((1 / (2 * π) : ℂ) *
        (∫ σ in (-τ)..τ, (1 + 0 * (-(I * σ))) * f σ * Complex.exp (-(I * T * σ))) -
        (1 * mainEC k1 s (kap (WN N) (pStar θs) 3) (kap (WN N) (pStar θs) 4) T +
          0 * dmainEC k1 s (kap (WN N) (pStar θs) 3) (kap (WN N) (pStar θs) 4) T)) := by
    rw [Rcore_eq N θs τ T hne]
    unfold HhatC
    have e1 : kS N θs 1 = k1 := h1
    rw [e1]
    simp only [zero_mul, add_zero, one_mul, hfdef]
    unfold kS; ring
  rw [hid, norm_mul, norm_mul, norm_ee, mul_one]
  refine mul_le_mul_of_nonneg_left (hcore.trans ?_) (norm_nonneg _)
  simp only [one_mul, zero_mul, add_zero]
  rw [hk1im, hrp, hrp]
  exact hsz

end ArcsAlgo.Core
