module

public import ArcsAlgo.EdgeVanish
public import ArcsAlgo.EdgeCentre
set_option autoImplicit false

/-!
# The core with the vanishing factor at the centre `a/q` (paper §3.5, Remark (the formula of Proposition C))

* `EI1_scale`: `E_I′` at the narrower width `s/Λ`.
* `kV_one_c`: `Im κ̃₁(a/q) = ν_{a/q}`; at `t = 0` the vanishing factor has the exact cumulants `w₀/2, w₀²/12, 0, −w₀⁴/120`.
* `vanishC_size`, `thmC_vanish`: for `𝒱(a/q) = {w₀}` and `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`, uniformly in `T`,
  `|∫_{|θ−a/q|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)·w₀·Ĥ′(T)| ≤ |G(a/q)|w₀(e^{ν²/(2s̃²)}N^{−3/2+7ε}/s̃² + e^{−N^{2ε}/(16384 log N)})`.

Hypotheses: `SiegelWalfisz`; the bound on `ν_{a/q}` is an explicit antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- `E_I′` at the narrower width `s/Λ`: `E_I′(s/Λ) ≤ 16M³x³Λ^{11}L_E′/s²`. -/
theorem EI1_scale {α3 α4 α5 ρ s M x Λ : ℝ} (hs : 0 < s) (h3 : 0 ≤ α3) (h4 : 0 ≤ α4) (h5 : 0 ≤ α5) (hr : 0 ≤ ρ)
    (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hx0 : 0 ≤ x) (hx1 : Λ ^ 2 * x ≤ 1)
    (b3 : α3 / s ^ 3 ≤ M * x) (b4 : α4 / s ^ 4 ≤ M * x ^ 2) (b5 : α5 / s ^ 5 ≤ M * x ^ 3)
    (br : ρ / s ^ 6 ≤ M * x ^ 4) :
    EI1 α3 α4 α5 ρ (s / Λ) ≤ 16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 11 / s ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hs1 : 0 < s / Λ := by positivity
  have hsc : ∀ (u : ℝ) (k : ℕ), u / (s / Λ) ^ k = Λ ^ k * (u / s ^ k) := by
    intro u k; rw [div_pow]; field_simp
  have hMΛ : 1 ≤ M * Λ := by nlinarith
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
  have h := EI1_le hs1 h3 h4 h5 hr hMΛ (by positivity) hx1 c3 c4 c5 cr
  refine h.trans (le_of_eq ?_)
  field_simp

/-- `κ̃₁` at the centre: `Im κ̃₁(a/q) = ν_{a/q}` (the vanishing factor contributes `w₀/2`, real). -/
theorem kV_one_c {N q a w₀ : ℕ} (hq : 3 ≤ q) : (kV N q a w₀ 0 1).im = nuW (WN N) q a := by
  have hts : (N : ℝ) * |(0 : ℝ)| ≤ 1 / q := by simp
  have him := im_kappa1 (W := WN N) (q := q) (a := a) 0
  rw [Fw'_zero, neg_neg] at him
  have hl : lamS w₀ 0 1 = (w₀ : ℂ) / 2 := by
    have h := (lamS_close (w := w₀) (ts := 0) (by simp) (by simp)).1
    simp only [abs_zero, mul_zero, zero_mul] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  unfold kV; rw [if_neg (by norm_num), hl]
  unfold kap
  have hterm : ∀ w ∈ Wv N q a, (w : ℂ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℂ) * cB (pStar ((a : ℝ) / q + 0 / (2 * π)) w) 1 =
      (((w : ℝ) / 2 : ℝ) : ℂ) + I * (((w : ℝ) * (Real.tan (alw q a w + w * 0 / 2) / 2) : ℝ) : ℂ) := by
    intro w hw
    have hp := (p_types (cos_star_ne_v hq hw hts)).2.2
    simp only [cB, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [pStar_eq]
    push_cast at hp ⊢
    linear_combination (w : ℂ) * hp
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum]
  unfold Wv; rw [him]
  simp

set_option maxHeartbeats 8000000 in
/-- The size of the error of `core_intS` with the vanishing factor at the centre (`A = 0`, `B = w₀`). -/
theorem vanishC_size {q L B ε τ s ν Cν A α3 α4 α5 ρ w : ℝ} (hB : 0 < B) (hL0 : 0 < L) (hLone : 1 ≤ L)
    (hε0 : 0 < ε) (hε : ε < 1 / 8) (hq1 : 1 ≤ q) (hqL : q ≤ L ^ B) (hτe : τ = Real.exp ((-(3 / 2) + ε) * L))
    (hA : A = 8 * 8 ^ 6 * q ^ 6) (hw : 0 ≤ w)
    (hα3 : α3 ≤ A * Real.exp (4 * L)) (hα4 : α4 ≤ A * Real.exp (5 * L)) (hα5 : α5 ≤ A * Real.exp (6 * L))
    (hρb : ρ ≤ A * Real.exp (7 * L)) (hα30 : 0 ≤ α3) (hα40 : 0 ≤ α4) (hα50 : 0 ≤ α5) (hρ0 : 0 ≤ ρ)
    (hsD : Real.exp (3 / 2 * L) / (32 * √L) ≤ s) (hs1 : 1 ≤ s) (hCν : 0 < Cν)
    (hnu' : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L))
    (hk1 : ((Cν + 2) * 32) ^ 2 * L ^ (1 : ℝ) ≤ Real.exp ((1 / 2 - ε) * √L))
    (hk4 : 48 * (8 * 8 ^ 6 * 32 ^ 6) ^ 3 * LamE1 * ((Cν + 2) * 32) ^ 12 * L ^ (18 * B + 15) ≤
      Real.exp (ε * √L))
    (hk5 : (8 * 8 ^ 6 * 32 ^ 6) ^ 2 * LamT4 * L ^ (12 * B + 6) ≤ Real.exp (1 * √L))
    (hk6 : 16384 * L ^ (3 / 2 : ℝ) ≤ Real.exp (2 * ε * √L)) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 < s ∧
      1 / (2 * π) * (Real.exp (ν ^ 2 / (2 * (s ^ 2 - s1 ^ 2))) * (0 * EI α3 α4 α5 ρ s1 + w * EI1 α3 α4 α5 ρ s1) +
        Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (0 * TIs α3 α4 s + w * TIs1 α3 α4 s)) ≤
      w * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 7 * ε) * L) / s ^ 2)) +
        w * Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by
  set K₀ : ℝ := 8 * 8 ^ 6 * 32 ^ 6 with hK₀
  have hLamE1 : 0 ≤ LamE1 := sum_nonneg fun i _ => Am_nonneg _
  have hLamT4 : 0 ≤ LamT4 := by unfold LamT4; have := Am_nonneg 1; have := Am_nonneg 4
                                have := Am_nonneg 5; have := Am_nonneg 7; positivity
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  set CΛ : ℝ := (Cν + 2) * 32 with hCΛ
  have hs0 : 0 < s := by linarith
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  set D := 32 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ q ^ 6 := one_le_pow₀ hq1; nlinarith
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
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
  have hMle : M ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hM, hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : q ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hpow : ∀ k : ℕ, (L ^ (6 * B) * L ^ 3) ^ k = L ^ ((6 * B + 3) * k) := by
    intro k
    have h63 : L ^ (6 * B) * L ^ 3 = L ^ (6 * B + 3) := by
      rw [Real.rpow_add hL0, show L ^ (3 : ℝ) = L ^ 3 by norm_cast]
    rw [h63, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  -- the tilt
  have hCΛ2 : 32 ≤ CΛ := by rw [hCΛ]; nlinarith
  set Λ := CΛ * √L * Real.exp (ε / 2 * L) with hΛdef
  have hexpε : 1 ≤ Real.exp (ε / 2 * L) := Real.one_le_exp (by positivity)
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛdef]
    have : 32 ≤ CΛ * √L := by nlinarith
    nlinarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ0 : 0 < Λ := by linarith
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
  have hsΛ : 0 < s / Λ := div_pos hs0 hΛ0
  have hss1 : s / Λ < s := by rw [div_lt_iff₀ hΛ0]; nlinarith
  refine ⟨s / Λ, hsΛ, hss1, ?_⟩
  have hE : Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) ≤ Real.exp 1 * Real.exp (ν ^ 2 / (2 * s ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [tilt_E hs0 hΛ2 hνs])
  have hEIs := EI1_scale hs0 hα30 hα40 hα50 hρ0 hM1 hΛ1 hx0 hΛx b3 b4 b5 br
  have hpoly : Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 11) ≤ Real.exp ((-(3 / 2) + 7 * ε) * L) := by
    have h := hk4
    have e : L ^ (18 * B + 15) = (L ^ (6 * B) * L ^ 3) ^ 3 * L ^ 6 := by
      rw [hpow, ← Real.rpow_natCast L 6, ← Real.rpow_add hL0]; congr 1; push_cast; ring
    have hm3 : M ^ 3 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 := pow_le_pow_left₀ hM0 (by linarith) 3
    have hΛ11 : Λ ^ 11 ≤ Λ ^ 12 := pow_le_pow_right₀ hΛ1 (by norm_num)
    have hΛ12 : Λ ^ 12 = CΛ ^ 12 * L ^ 6 * Real.exp (6 * ε * L) := by
      rw [hΛdef, mul_pow, mul_pow, show √L ^ 12 = (√L ^ 2) ^ 6 by ring, Real.sq_sqrt hL0.le,
        ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have hx3 : x ^ 3 = Real.exp (-(3 / 2) * L) := by rw [hxk]; congr 1 <;> push_cast <;> ring_nf
    have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hC : 3 * 16 * M ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6 ≤ Real.exp (ε * L) := by
      calc 3 * 16 * M ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6
          ≤ 3 * 16 * (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6 := by gcongr
        _ = 48 * K₀ ^ 3 * LamE1 * CΛ ^ 12 * L ^ (18 * B + 15) := by rw [e]; ring
        _ ≤ Real.exp (ε * √L) := h
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp ((-(3 / 2) + 7 * ε) * L) =
        Real.exp (ε * L) * (Real.exp (-(3 / 2) * L) * Real.exp (6 * ε * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hP : 0 ≤ Real.exp (-(3 / 2) * L) * Real.exp (6 * ε * L) := by positivity
    have hQ : 0 ≤ 16 * M ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6 := by positivity
    have hstep : Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 11) ≤
        Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 12) := by gcongr
    refine hstep.trans ?_
    rw [hΛ12, hx3, hsplit]
    calc Real.exp 1 * (16 * (M ^ 3 * Real.exp (-(3 / 2) * L)) * LamE1 * (CΛ ^ 12 * L ^ 6 * Real.exp (6 * ε * L)))
        = Real.exp 1 * (16 * M ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6) *
            (Real.exp (-(3 / 2) * L) * Real.exp (6 * ε * L)) := by ring
      _ ≤ 3 * (16 * M ^ 3 * LamE1 * CΛ ^ 12 * L ^ 6) * (Real.exp (-(3 / 2) * L) * Real.exp (6 * ε * L)) := by
          gcongr
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hP; linarith
  have hEI10 : 0 ≤ EI1 α3 α4 α5 ρ (s / Λ) := by
    rw [EI1_norm _ _ _ _ hsΛ]
    exact mul_nonneg (one_div_nonneg.mpr (pow_pos hsΛ 2).le) (sum_nonneg fun i _ => mul_nonneg (ebC_nonneg
      (div_nonneg hα30 (pow_pos hsΛ 3).le) (div_nonneg hα40 (pow_pos hsΛ 4).le)
      (div_nonneg hα50 (pow_pos hsΛ 5).le) (div_nonneg hρ0 (pow_pos hsΛ 6).le) i) (Am_nonneg _))
  have hpart1 : Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * EI1 α3 α4 α5 ρ (s / Λ) ≤
      Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 7 * ε) * L) / s ^ 2) := by
    calc Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * EI1 α3 α4 α5 ρ (s / Λ)
        ≤ (Real.exp 1 * Real.exp (ν ^ 2 / (2 * s ^ 2))) * (16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 11 / s ^ 2) :=
          mul_le_mul hE hEIs hEI10 (by positivity)
      _ = Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp 1 * (16 * (M ^ 3 * x ^ 3) * LamE1 * Λ ^ 11) / s ^ 2) := by
          ring
      _ ≤ _ := by gcongr
  -- the tail
  have hE2 : Real.exp (2 * ε * L) / (1024 * L) ≤ s ^ 2 * τ ^ 2 := by
    have h1' : (Real.exp (3 / 2 * L) / D) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 * τ ^ 2 = Real.exp (2 * ε * L) / (1024 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hτe, ← Real.exp_nat_mul,
        div_mul_eq_mul_div, ← Real.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right h1' (by positivity)
  have hpart2 : Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs1 α3 α4 s ≤
      Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by
    set E := Real.exp (2 * ε * L)
    have hEpos : 0 < E := Real.exp_pos _
    have h6 := hk6
    have hL32 : L ^ (3 / 2 : ℝ) = L * √L := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL0, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hL32] at h6
    have hsqE : √L ≤ E / (16384 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 16384 * (L * √L) ≤ E := h6.trans (Real.exp_le_exp.mpr (by nlinarith))
      linarith
    have hM2 : M ^ 2 * LamT4 ≤ Real.exp (√L) := by
      have h := hk5
      have e : L ^ (12 * B + 6) = (L ^ (6 * B) * L ^ 3) ^ 2 := by rw [hpow]; congr 1; push_cast; ring
      have hm2 : M ^ 2 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 := pow_le_pow_left₀ hM0 (by linarith) 2
      calc M ^ 2 * LamT4 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 * LamT4 := by gcongr
        _ = K₀ ^ 2 * LamT4 * L ^ (12 * B + 6) := by rw [e]; ring
        _ ≤ Real.exp (1 * √L) := h
        _ = _ := by rw [one_mul]
    have hTs : TIs1 α3 α4 s ≤ M ^ 2 * LamT4 := by
      have hb3 : α3 / s ^ 3 ≤ M := b3.trans (by nlinarith)
      have hb4 : α4 / s ^ 4 ≤ M := b4.trans (by nlinarith [pow_le_one₀ hx0 hx1 (n := 2)])
      refine (TIs_le hs0 hα30 hα40 hM1 hb3 hb4).2.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ M ^ 2 * LamT4 := by positivity
      have : 1 ≤ s ^ 2 := one_le_pow₀ hs1
      nlinarith
    have hTI0 : 0 ≤ TIs1 α3 α4 s := by
      unfold TIs1; have := Am_nonneg 1; have := Am_nonneg 4; have := Am_nonneg 5; have := Am_nonneg 7
      positivity
    calc Real.exp (-(s ^ 2 * τ ^ 2) / 8) * TIs1 α3 α4 s
        ≤ Real.exp (-(E / (1024 * L)) / 8) * (M ^ 2 * LamT4) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hTs hTI0 (Real.exp_pos _).le
      _ ≤ Real.exp (-(E / (1024 * L)) / 8) * Real.exp (E / (16384 * L)) := by
          gcongr; exact hM2.trans (Real.exp_le_exp.mpr hsqE)
      _ = Real.exp (-E / (16384 * L)) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
  have h2pi : 1 / (2 * π) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hb1 : 0 ≤ w * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 7 * ε) * L) / s ^ 2)) := by
    positivity
  have hb2 : 0 ≤ w * Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by positivity
  have hsum : Real.exp (ν ^ 2 / (2 * (s ^ 2 - (s / Λ) ^ 2))) * (0 * EI α3 α4 α5 ρ (s / Λ) + w * EI1 α3 α4 α5 ρ (s / Λ)) +
      Real.exp (-(s ^ 2 * τ ^ 2) / 8) * (0 * TIs α3 α4 s + w * TIs1 α3 α4 s) ≤
      w * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 7 * ε) * L) / s ^ 2)) +
        w * Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L)) := by
    simp only [zero_mul, zero_add]
    have := mul_le_mul_of_nonneg_left hpart1 hw
    have := mul_le_mul_of_nonneg_left hpart2 hw
    nlinarith
  calc _ ≤ 1 * (w * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * (Real.exp ((-(3 / 2) + 7 * ε) * L) / s ^ 2)) +
        w * Real.exp (-(Real.exp (2 * ε * L)) / (16384 * L))) :=
        mul_le_mul h2pi hsum (by
          have h0 := hEI10
          have h1 : 0 ≤ TIs1 α3 α4 s := by
            unfold TIs1; have := Am_nonneg 1; have := Am_nonneg 4; have := Am_nonneg 5; have := Am_nonneg 7
            positivity
          simp only [zero_mul, zero_add]; positivity) (by norm_num)
    _ = _ := one_mul _



set_option maxHeartbeats 16000000 in
/-- **The core with the vanishing factor at the centre** (Remark (the formula of Proposition C),
`𝒱(a/q) = {w₀}`): fix `B > 0`, `0 < ε < 1/8`, `C_ν > 0`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1` and
`|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`, with the cumulants of `G̃` at `a/q` (those of Proposition C, the vanishing
factor contributing exactly `w₀/2, w₀²/12, 0, −w₀⁴/120`), uniformly in `T`:
`|∫_{|θ−a/q|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)·w₀·Ĥ′(T)| ≤ |G(a/q)|w₀(e^{ν²/(2s̃²)}N^{−3/2+7ε}/s̃² + e^{−N^{2ε}/(16384 log N)})`. -/
theorem thmC_vanish (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ w₀ ∈ WN N, vanish q a w₀ → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
        0 < sV N q a w₀ 0 ∧ (kV N q a w₀ 0 1).im = nuW (WN N) q a ∧ ∀ T : ℝ,
        ‖Rcore N ((a : ℝ) / q) ((N : ℝ) ^ (-(3 / 2 : ℝ) + ε)) T -
            ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ 0 T) T)‖ ≤
          ‖Gw (WN N) q a ((a : ℝ) / q)‖ *
            (w₀ * (Real.exp (nuW (WN N) q a ^ 2 / (2 * sV N q a w₀ 0 ^ 2)) *
                ((N : ℝ) ^ (-(3 / 2 : ℝ) + 7 * ε) / sV N q a w₀ 0 ^ 2)) +
              w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N))) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  have hLamE1 : 0 ≤ LamE1 := sum_nonneg fun i _ => Am_nonneg _
  set CΛ : ℝ := (Cν + 2) * 32 with hCΛ
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (6 * B) hε3 (32 * 8 ^ 6)
  obtain ⟨K₇, hK₇, hk7⟩ := ev_poly_exp 1 one_pos 5632
  obtain ⟨Ka, hKa, hka⟩ := ev_poly_exp 1 hε1 (CΛ ^ 2)
  obtain ⟨Kb, hKb, hkb⟩ := ev_poly_exp (18 * B + 15) hε0 (48 * (8 * 8 ^ 6 * 32 ^ 6) ^ 3 * LamE1 * CΛ ^ 12)
  obtain ⟨Kc, hKc, hkc⟩ := ev_poly_exp (12 * B + 6) one_pos ((8 * 8 ^ 6 * 32 ^ 6) ^ 2 * LamT4)
  obtain ⟨Kd, hKd, hkd⟩ := ev_poly_exp (3 / 2) (by positivity : 0 < 2 * ε) 16384
  obtain ⟨Ke, hKe, hke⟩ := ev_poly_exp 1 (by positivity : 0 < ε / 2) (2048 * Cν)
  set Kmax := max (max (max K₂ K₃) (max K₇ Ka)) (max (max Kb Kc) (max Kd Ke))
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha w₀ hw₀ hv hnu => ?_⟩
  obtain ⟨-, hS2pos, hwin, hrat, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  obtain ⟨ts, hts0⟩ : ∃ ts : ℝ, ts = 0 := ⟨0, rfl⟩
  suffices key : 0 < sV N q a w₀ ts ∧ (kV N q a w₀ ts 1).im = nuW (WN N) q a ∧ ∀ T : ℝ,
      ‖Rcore N ((a : ℝ) / q + ts / (2 * π)) ((N : ℝ) ^ (-(3 / 2 : ℝ) + ε)) T -
          ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
        ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
          (w₀ * (Real.exp (nuW (WN N) q a ^ 2 / (2 * sV N q a w₀ ts ^ 2)) *
              ((N : ℝ) ^ (-(3 / 2 : ℝ) + 7 * ε) / sV N q a w₀ ts ^ 2)) +
            w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N))) by
    subst hts0; simp only [zero_div, add_zero] at key; exact key
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL7 : K₇ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hLa : Ka ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hLb : Kb ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hLc : Kc ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hLd : Kd ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hLe : Ke ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hKL
  have hLone : 1 ≤ L := le_trans hK₂ hL2
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hnp : ∀ k : ℕ, Nr ^ k = Real.exp (k * L) := fun k => by rw [← hexpL, ← Real.exp_nat_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  -- `N|t*| ≤ 1/(12q)`
  have hts' : Nr * |ts| ≤ 1 / (12 * q) := by rw [hts0, abs_zero, mul_zero]; positivity
  have hts1 : Nr * |ts| ≤ 1 / q := hts'.trans (by
    rw [div_le_div_iff₀ (by positivity) hq0]; nlinarith)
  have hw₀N : (w₀ : ℝ) ≤ Nr := WN_le hw₀
  have hw₀q : (w₀ : ℝ) ≤ q := by
    have := vanish_eq hq ha (mem_filter.mp hw₀).2 hv
    have : (2 * w₀ : ℝ) = q := by exact_mod_cast this
    have : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
    linarith
  have hw₀0 : (0 : ℝ) ≤ w₀ := Nat.cast_nonneg w₀
  have hwts : (w₀ : ℝ) * |ts| ≤ 1 / (12 * q) :=
    (mul_le_mul_of_nonneg_right hw₀N (abs_nonneg ts)).trans hts'
  have hwts12 : (w₀ : ℝ) * |ts| ≤ 1 / 36 := hwts.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hwts2 : (w₀ : ℝ) ^ 2 * |ts| ≤ 1 := by
    have : (w₀ : ℝ) ^ 2 * |ts| = w₀ * (w₀ * |ts|) := by ring
    rw [this]
    calc (w₀ : ℝ) * (w₀ * |ts|) ≤ q * (1 / (12 * q)) :=
          mul_le_mul hw₀q hwts (by positivity) hq0.le
      _ ≤ 1 := by rw [show (q : ℝ) * (1 / (12 * q)) = 1 / 12 by field_simp]; norm_num
  set x₀ : ℂ := I * w₀ * ts with hx₀def
  have hx₀ : ‖x₀‖ = w₀ * |ts| := norm_Iwt w₀ ts
  have hx₀6 : ‖x₀‖ ≤ 1 / 6 := by rw [hx₀]; linarith
  have hx₀12 : ‖x₀‖ ≤ 1 / 12 := by rw [hx₀]; linarith
  have hg0 : gS x₀ ≠ 0 := slitPlane_ne_zero (gS_slit (by linarith))
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  have hpar := fun w (hw : w ∈ Wv N q a) => pStar_le_v hq hw hts1
  have hne : ∀ w ∈ Wv N q a, 1 + ee (w * θs) ≠ 0 := fun w hw => (hpar w hw).1
  have hpq : ∀ w ∈ Wv N q a, ‖pStar θs w‖ ≤ q := fun w hw => (hpar w hw).2
  have hWv : ∀ w ∈ Wv N q a, (w : ℝ) ≤ Nr := fun w hw => WN_le (Wv_sub N q a hw)
  have htsw : |ts| < π / (q * Nr) := by
    have : |ts| ≤ 1 / (q * Nr) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at hts1; linarith
    exact lt_of_le_of_lt this (div_lt_div_of_pos_right (by linarith [Real.two_le_pi]) (by positivity))
  have hN1 : 1 ≤ N := by omega
  -- `κ̃₂` and `s̃`
  have h11 : 81 / 8 * (w₀ : ℝ) ^ 2 ≤ Nr ^ 3 / (512 * L) := by
    have h7 := hk7 L hL7; rw [Real.rpow_one] at h7
    have hN7 : 5632 * L ≤ Nr := h7.trans (by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
    rw [le_div_iff₀ (by positivity)]
    have : (w₀ : ℝ) ^ 2 ≤ Nr ^ 2 := pow_le_pow_left₀ hw₀0 hw₀N 2
    nlinarith [mul_le_mul_of_nonneg_left hN7 (by positivity : (0 : ℝ) ≤ Nr ^ 2)]
  obtain ⟨hkV2im, hre⟩ := vanish_k2 (a := a) hq hN1 hts1 (by linarith) hS2lo hL0 h11
  have hre0 : 0 < (kV N q a w₀ ts 2).re := lt_of_lt_of_le (by positivity) hre
  set s := sV N q a w₀ ts with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hre0
  have hs2 : s ^ 2 = (kV N q a w₀ ts 2).re := Real.sq_sqrt hre0.le
  have h2 : kV N q a w₀ ts 2 = ((s ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, hs2]
    · rw [Complex.ofReal_im, hkV2im]
  set D := 32 * √L with hD
  have hsD : Real.exp (3 / 2 * L) / D ≤ s := by
    rw [hsdef]; unfold sV
    rw [Real.le_sqrt (by positivity) hre0.le]
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 = Nr ^ 3 / (1024 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hnp 3]
      congr 1; push_cast; ring_nf; ring
    rw [e]
    have : Nr ^ 3 / (1024 * L) ≤ Nr ^ 3 / (512 * L) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
    linarith
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ hsD
    rw [le_div_iff₀ (by positivity), one_mul, hD]
    have h7 := hk7 L hL7; rw [Real.rpow_one] at h7
    calc 32 * √L ≤ 5632 * L := by nlinarith
      _ ≤ Real.exp (1 * √L) := h7
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hk0 : kV N q a w₀ ts 0 = 0 := by unfold kV; simp [kap, cB]
  set k1 := kV N q a w₀ ts 1 with hk1def
  have hk1im : k1.im = nuW (WN N) q a := by rw [hk1def, hts0]; exact kV_one_c hq
  -- the cumulants of order 3, 4, 5 and the remainder
  obtain ⟨hαN, hρN⟩ := vanish_alpha (a := a) hq hN1 hts1 (by linarith) hw₀N
  set A : ℝ := 8 * 8 ^ 6 * (q : ℝ) ^ 6 with hA
  set α3 := ‖kV N q a w₀ ts 3‖ / 6
  set α4 := ‖kV N q a w₀ ts 4‖ / 24
  set α5 := ‖kV N q a w₀ ts 5‖ / 120
  set ρ := 2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ Wv N q a, (w : ℝ) ^ 6 + 4 ^ 6 * (w₀ : ℝ) ^ 6 with hρ
  have hα3 : α3 ≤ A * Real.exp (4 * L) := by
    have := hαN 3 le_rfl (by norm_num); norm_num [Nat.factorial] at this; rw [hnp] at this; norm_num at this
    exact this
  have hα4 : α4 ≤ A * Real.exp (5 * L) := by
    have := hαN 4 (by norm_num) (by norm_num); norm_num [Nat.factorial] at this; rw [hnp] at this
    norm_num at this; exact this
  have hα5 : α5 ≤ A * Real.exp (6 * L) := by
    have := hαN 5 (by norm_num) le_rfl; norm_num [Nat.factorial] at this; rw [hnp] at this
    norm_num at this; exact this
  have hρb : ρ ≤ A * Real.exp (7 * L) := by
    have := hρN; rw [hnp] at this; norm_num at this; exact this
  have hα30 : 0 ≤ α3 := by positivity
  have hα40 : 0 ≤ α4 := by positivity
  have hα50 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  -- the window
  set τ := Nr ^ (-(3 / 2 : ℝ) + ε) with hτdef
  have hτe : τ = Real.exp ((-(3 / 2) + ε) * L) := hrp _
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
  obtain ⟨hτ', hy⟩ := vanish_window hL0 hLone hε0 hε hq1 hqL hτe (hk2 L hL2) (hk3 L hL3) hA hα3 hα4 hα5 hρb
  rw [hexpL] at hτ'
  have hexpf : ∀ σ : ℝ, |σ| ≤ τ → ∃ R : ℂ, ‖R‖ ≤ ρ * σ ^ 6 ∧
      fV N q a w₀ ts σ = Complex.exp (∑ n ∈ range 6, kV N q a w₀ ts n * (I * σ) ^ n / (Nat.factorial n : ℂ) + R) :=
    fun σ hσ => vanish_expand hq hts1 (by linarith) hw₀N hτ' hσ
  -- the conditions on `κ̃₁`
  -- the tilt condition
  have hnu' : |nuW (WN N) q a| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L) := by rw [← hrp]; exact hnu
  have hyt : |k1.im| ≤ s ^ 2 * τ / 4 := by
    rw [hk1im, hs2]
    have h1 : Nr ^ 3 / (512 * L) * τ / 4 ≤ (kV N q a w₀ ts 2).re * τ / 4 := by
      have := mul_le_mul_of_nonneg_right hre hτ0.le; linarith
    have he8 := hke L hLe; rw [Real.rpow_one] at he8
    have he8' : 2048 * Cν * L ≤ Real.exp (ε / 2 * L) := he8.trans (Real.exp_le_exp.mpr (by nlinarith))
    have e : Nr ^ 3 / (512 * L) * τ / 4 = Real.exp ((3 / 2 + ε) * L) / (2048 * L) := by
      rw [hnp, hτe, show (3 / 2 + ε) * L = ((3 : ℕ) : ℝ) * L + (-(3 / 2) + ε) * L by push_cast; ring,
        Real.exp_add]
      field_simp; ring
    have e2 : Real.exp ((3 / 2 + ε) * L) = Real.exp (ε / 2 * L) * Real.exp ((3 / 2 + ε / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Cν * Real.exp ((3 / 2 + ε / 2) * L) ≤ Real.exp ((3 / 2 + ε) * L) / (2048 * L) := by
      rw [e2, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right he8' (Real.exp_pos ((3 / 2 + ε / 2) * L)).le
      nlinarith [Real.exp_pos ((3 / 2 + ε / 2) * L)]
    linarith
  obtain ⟨s1, hs10, hs1s, hsz⟩ := vanishC_size (q := (q : ℝ)) (w := (w₀ : ℝ)) hB hL0 hLone hε0 hε hq1 hqL hτe hA
    hw₀0 hα3 hα4 hα5 hρb hα30 hα40 hα50 hρ0 hsD hs1 hCν hnu' (hka L hLa) (hkb L hLb) (hkc L hLc) (hkd L hLd)
  refine ⟨hs0, hk1im, fun T => ?_⟩
  have hcore := core_intS (fV N q a w₀ ts) (continuous_fV N q a w₀ ts) (kV N q a w₀ ts) (k1 := k1) (s1 := s1)
    (a := 0) (b := w₀) 0 ((w₀ : ℝ) : ℂ) hs0 hs10 hs1s hτ0 hρ0 (by simp)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw₀0]) hk0 rfl h2 hexpf hy hyt T
  have hid := vanish_identity hq ha hw₀ hv hts1 (by linarith) hs0 τ T
  have hint : ∫ σ in (-τ)..τ, (-(I * ((w₀ : ℝ) : ℂ) * (ts + σ))) * fV N q a w₀ ts σ * Complex.exp (-(I * T * σ)) =
      ∫ σ in (-τ)..τ, (0 + ((w₀ : ℝ) : ℂ) * (-(I * σ))) * fV N q a w₀ ts σ * Complex.exp (-(I * T * σ)) :=
    intervalIntegral.integral_congr (fun σ _ => by simp only [hts0]; push_cast; ring)
  have hmain : ((w₀ : ℝ) : ℂ) * (-(I * ts) * mainEC k1 s (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T +
      dmainEC k1 s (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T) =
      0 * mainEC k1 s (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T +
        ((w₀ : ℝ) : ℂ) * dmainEC k1 s (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T := by
    rw [hts0]; push_cast; ring
  rw [hid, hint, hmain, norm_mul, norm_mul, norm_mul, norm_ee, norm_cexp_IT, one_mul, one_mul]
  have hGt : ‖GtV N q a w₀ ts‖ = ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ := by
    unfold GtV; rw [norm_mul, hts0]; simp [gS_zero]
  rw [hGt]
  refine mul_le_mul_of_nonneg_left (hcore.trans ?_) (norm_nonneg _)
  rw [hk1im, hrp (-(3 / 2) + 7 * ε), hrp (2 * ε)]
  exact hsz

end ArcsAlgo.Core
