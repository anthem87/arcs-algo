module

public import ArcsAlgo.SecondMoment.BPRatio
set_option autoImplicit false

/-!
# Proposition B′: the constants, as in the paper

`κ = Var(w²)/(4(Ew²)²)` (`kapB`), `κ_c = (Var(w²) − Cov(w², w)²/Var(w))/(4(Ew²)²)` (`kapcB`) and
`γ_M = σ(B − 2βA)/(4(Ew²)²)` (`gamB`, with `A`, `β`, `B`, `R` as in the paper) are the coefficients found in
the expansions: `KK2_eq`, `KK3_eq`, `KKu_eq`; and the coefficient of `m⁻²` without conditioning depends on `u`:
`c₂(M, u) = c₂(M, 0) − 2κu²/Ew²` (`CCu_eq`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

/-! ### The constants of Proposition B′, as in the paper -/

/-- `Var(w) = E w² − (E w)²`. -/
noncomputable def varW (M : ℕ) : ℝ := mw M 2 - mw M 1 ^ 2
/-- `Var(w²) = E w⁴ − (E w²)²`. -/
noncomputable def varW2 (M : ℕ) : ℝ := mw M 4 - mw M 2 ^ 2
/-- `Cov(w², w) = E w³ − E w² E w`. -/
noncomputable def covW (M : ℕ) : ℝ := mw M 3 - mw M 2 * mw M 1

/-- `κ = Var(w²)/(4(E w²)²)`. -/
noncomputable def kapB (M : ℕ) : ℝ := varW2 M / (4 * mw M 2 ^ 2)
/-- `A = Var(w²) − Cov(w², w)²/Var(w)`. -/
noncomputable def AB (M : ℕ) : ℝ := varW2 M - covW M ^ 2 / varW M
/-- `κ_c = A/(4(E w²)²)`. -/
noncomputable def kapcB (M : ℕ) : ℝ := AB M / (4 * mw M 2 ^ 2)
/-- `β = Cov(w, w²)/(Var(w) E w²)`. -/
noncomputable def betaB (M : ℕ) : ℝ := covW M / (varW M * mw M 2)
/-- `R = w² − E w² − (Cov(w², w)/Var(w))(w − μ)`. -/
noncomputable def RB (M : ℕ) (w : ℝ) : ℝ := w ^ 2 - mw M 2 - covW M / varW M * (w - mw M 1)
/-- `B = E[R²(w − μ)]/Var(w)`. -/
noncomputable def BB (M : ℕ) : ℝ :=
  (∑ a : Fin M, RB M (((a : ℕ) : ℝ) + 1) ^ 2 * (((a : ℕ) : ℝ) + 1 - mw M 1)) / M / varW M
/-- `γ_M = σ(B − 2βA)/(4(E w²)²)`. -/
noncomputable def gamB (M : ℕ) : ℝ := √(sig2 M) * (BB M - 2 * betaB M * AB M) / (4 * mw M 2 ^ 2)

theorem varW_eq (hM : 1 ≤ M) : varW M = sig2 M := (sig2_mw hM).symm

theorem varW_pos (hM : 2 ≤ M) : 0 < varW M := by rw [varW_eq (by omega)]; exact sig2_pos' hM

theorem mw2_pos (hM : 1 ≤ M) : 0 < mw M 2 := by rw [← ew2_mw hM]; exact ew2_pos M

theorem sqe2 (hM : 1 ≤ M) : √(ew2 M) ^ (2 : ℕ) = mw M 2 := by
  rw [Real.sq_sqrt (ew2_pos M).le, ew2_mw hM]
theorem sqe4 (hM : 1 ≤ M) : √(ew2 M) ^ (4 : ℕ) = mw M 2 ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqe2 hM]
theorem sqe6 (hM : 1 ≤ M) : √(ew2 M) ^ (6 : ℕ) = mw M 2 ^ 3 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sqe2 hM]
theorem sqe8 (hM : 1 ≤ M) : √(ew2 M) ^ (8 : ℕ) = mw M 2 ^ 4 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sqe2 hM]
theorem sqs2 (hM : 2 ≤ M) : √(sig2 M) ^ (2 : ℕ) = varW M := by
  rw [Real.sq_sqrt (sig2_pos' hM).le, varW_eq (by omega)]
theorem sqs3 (hM : 2 ≤ M) : √(sig2 M) ^ (3 : ℕ) = √(sig2 M) * varW M := by
  rw [pow_succ, sqs2 hM, mul_comm]

theorem sum_poly5 (hM : 1 ≤ M) (c0 c1 c2 c3 c4 c5 : ℝ) :
    (∑ a : Fin M, (c5 * (((a : ℕ) : ℝ) + 1) ^ 5 + c4 * (((a : ℕ) : ℝ) + 1) ^ 4 + c3 * (((a : ℕ) : ℝ) + 1) ^ 3 +
      c2 * (((a : ℕ) : ℝ) + 1) ^ 2 + c1 * (((a : ℕ) : ℝ) + 1) ^ 1 + c0)) / M =
      c5 * mw M 5 + c4 * mw M 4 + c3 * mw M 3 + c2 * mw M 2 + c1 * mw M 1 + c0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold mw; field_simp

/-- `E[R²(w − μ)]` in moments. -/
theorem BB_eq (hM : 2 ≤ M) : BB M =
    (mw M 5 + (-2 * (covW M / varW M) - mw M 1) * mw M 4 +
      ((covW M / varW M) ^ 2 + 4 * (covW M / varW M) * mw M 1 - 2 * mw M 2) * mw M 3 +
      (-3 * (covW M / varW M) ^ 2 * mw M 1 - 2 * (covW M / varW M) * mw M 1 ^ 2 +
        2 * (covW M / varW M) * mw M 2 + 2 * mw M 1 * mw M 2) * mw M 2 +
      ((covW M / varW M) * mw M 1 - mw M 2) * (3 * (covW M / varW M) * mw M 1 - mw M 2) * mw M 1 -
      mw M 1 * ((covW M / varW M) * mw M 1 - mw M 2) ^ 2) / varW M := by
  have hM1 : 1 ≤ M := by omega
  unfold BB
  congr 1
  set c := covW M / varW M
  set m1 := mw M 1
  set m2 := mw M 2
  rw [show mw M 5 + (-2 * c - m1) * mw M 4 + (c ^ 2 + 4 * c * m1 - 2 * m2) * mw M 3 +
      (-3 * c ^ 2 * m1 - 2 * c * m1 ^ 2 + 2 * c * m2 + 2 * m1 * m2) * m2 +
      (c * m1 - m2) * (3 * c * m1 - m2) * m1 - m1 * (c * m1 - m2) ^ 2 =
      1 * mw M 5 + (-2 * c - m1) * mw M 4 + (c ^ 2 + 4 * c * m1 - 2 * m2) * mw M 3 +
      (-3 * c ^ 2 * m1 - 2 * c * m1 ^ 2 + 2 * c * m2 + 2 * m1 * m2) * mw M 2 +
      ((c * m1 - m2) * (3 * c * m1 - m2)) * mw M 1 + (-(m1 * (c * m1 - m2) ^ 2)) by ring,
    ← sum_poly5 hM1]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold RB; ring

set_option maxHeartbeats 2000000 in
theorem KK2_eq (hM : 2 ≤ M) : KK2 M = kapcB M := by
  have hM1 : 1 ≤ M := by omega
  have hV := (varW_pos hM).ne'
  have hm := (mw2_pos hM1).ne'
  unfold KK2 kapcB AB varW2 covW
  rw [cX_022 hM1, cX_102 hM1]
  simp only [div_pow, mul_pow, ← pow_mul, sqe4 hM1, sqs2 hM]
  norm_num [sqe4 hM1, sqs2 hM]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
theorem KKu_eq (hM : 2 ≤ M) : KKu M = kapB M := by
  have hM1 : 1 ≤ M := by omega
  have hm := (mw2_pos hM1).ne'
  unfold KKu FXut2 FYut2 kapB varW2
  rw [cXu_04 hM1, cXu_22 hM1, cXu_40 hM1, cYu_4 hM1, sqe4 hM1]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
theorem CCu_eq (hM : 2 ≤ M) (u : ℝ) : CCu M u = CCu M 0 - 2 * kapB M * u ^ 2 / mw M 2 := by
  have hM1 : 1 ≤ M := by omega
  have hm := (mw2_pos hM1).ne'
  rw [← KKu_eq hM]
  unfold CCu KKu FXut2 FYut2 FXut4 FYut4
  simp only [sqe4 hM1, sqe6 hM1, sqe8 hM1]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
theorem KK3_eq (hM : 2 ≤ M) : KK3 M = gamB M := by
  have hM1 : 1 ≤ M := by omega
  have hV := (varW_pos hM).ne'
  have hm := (mw2_pos hM1).ne'
  have hσ : √(sig2 M) ≠ 0 := (Real.sqrt_pos.mpr (sig2_pos' hM)).ne'
  unfold KK3 gamB
  rw [BB_eq hM]
  unfold betaB AB varW2 covW
  rw [cX_022 hM1, cX_102 hM1, cX_202 hM1, cX_122 hM1]
  simp only [div_pow, mul_pow, ← pow_mul]
  norm_num only [sqe2 hM1, sqe4 hM1, sqe6 hM1, sqs2 hM, sqs3 hM]
  field_simp
  rw [sqs2 hM]
  unfold varW
  rw [mw1 hM1, mw2 hM1, mw3 hM1, mw4 hM1, mw5 hM1]
  ring

end ArcsAlgo.LLT
