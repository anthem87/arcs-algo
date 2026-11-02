module

public import ArcsAlgo.SecondMoment.BPEval
set_option autoImplicit false

/-!
# Proposition B′: the moments of `w` uniform in `{1, …, M}`

Faulhaber's formulas for `m_k = E w^k`, `k ≤ 6`; `σ² = m₂ − m₁²`, `E w² = m₂`; and the third and fifth
cumulants of `w` vanish (`w` is symmetric about its mean).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

theorem sumw_pow (M k : ℕ) : ∑ a : Fin M, ((a : ℕ) + 1 : ℝ) ^ k = ∑ i ∈ range M, ((i : ℝ) + 1) ^ k :=
  Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) ^ k) M

theorem fh1 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 1 = (M : ℝ) * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
theorem fh2 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 2 = (M : ℝ) * (M + 1) * (2 * M + 1) / 6 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
theorem fh3 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 3 = (M : ℝ) ^ 2 * (M + 1) ^ 2 / 4 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
theorem fh4 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 4 =
    (M : ℝ) * (M + 1) * (2 * M + 1) * (3 * M ^ 2 + 3 * M - 1) / 30 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
theorem fh5 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 5 =
    (M : ℝ) ^ 2 * (M + 1) ^ 2 * (2 * M ^ 2 + 2 * M - 1) / 12 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
theorem fh6 (M : ℕ) : ∑ i ∈ range M, ((i : ℝ) + 1) ^ 6 =
    (M : ℝ) * (M + 1) * (2 * M + 1) * (3 * M ^ 4 + 6 * M ^ 3 - 3 * M + 1) / 42 := by
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

theorem mw1 (hM : 1 ≤ M) : mw M 1 = ((M : ℝ) + 1) / 2 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh1]; field_simp
theorem mw2 (hM : 1 ≤ M) : mw M 2 = ((M : ℝ) + 1) * (2 * M + 1) / 6 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh2]; field_simp
theorem mw3 (hM : 1 ≤ M) : mw M 3 = (M : ℝ) * (M + 1) ^ 2 / 4 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh3]; field_simp
theorem mw4 (hM : 1 ≤ M) : mw M 4 = ((M : ℝ) + 1) * (2 * M + 1) * (3 * M ^ 2 + 3 * M - 1) / 30 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh4]; field_simp
theorem mw5 (hM : 1 ≤ M) : mw M 5 = (M : ℝ) * (M + 1) ^ 2 * (2 * M ^ 2 + 2 * M - 1) / 12 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh5]; field_simp
theorem mw6 (hM : 1 ≤ M) : mw M 6 = ((M : ℝ) + 1) * (2 * M + 1) * (3 * M ^ 4 + 6 * M ^ 3 - 3 * M + 1) / 42 := by
  have : (M : ℝ) ≠ 0 := by positivity
  rw [mw, sumw_pow, fh6]; field_simp

/-- `Var w = σ²`, `E w² = ew2`. -/
theorem sig2_mw (hM : 1 ≤ M) : sig2 M = mw M 2 - mw M 1 ^ 2 := by
  rw [mw1 hM, mw2 hM, sig2]; ring
theorem ew2_mw (hM : 1 ≤ M) : ew2 M = mw M 2 := by rw [mw2 hM, ew2]

/-- `w` uniform is symmetric about its mean: its third and fifth cumulants vanish. -/
theorem k3w_zero (hM : 1 ≤ M) : 2 * mw M 1 ^ 3 - 3 * mw M 1 * mw M 2 + mw M 3 = 0 := by
  rw [mw1 hM, mw2 hM, mw3 hM]; ring
theorem k5w_zero (hM : 1 ≤ M) :
    24 * mw M 1 ^ 5 - 60 * mw M 1 ^ 3 * mw M 2 + 20 * mw M 1 ^ 2 * mw M 3 + 30 * mw M 1 * mw M 2 ^ 2 -
      5 * mw M 1 * mw M 4 - 10 * mw M 2 * mw M 3 + mw M 5 = 0 := by
  rw [mw1 hM, mw2 hM, mw3 hM, mw4 hM, mw5 hM]; ring

theorem cX300 (hM : 1 ≤ M) : cX M 3 0 0 = 0 := by rw [cX_300 hM]; linarith [k3w_zero hM]
theorem cX500 (hM : 1 ≤ M) : cX M 5 0 0 = 0 := by rw [cX_500 hM]; linarith [k5w_zero hM]
theorem cY30 (hM : 1 ≤ M) : cY M 3 0 = 0 := by rw [cY_30 hM]; linarith [k3w_zero hM]
theorem cY50 (hM : 1 ≤ M) : cY M 5 0 = 0 := by rw [cY_50 hM]; linarith [k5w_zero hM]
theorem cS3 (hM : 1 ≤ M) : cS M 3 = 0 := by rw [cS_3 hM]; linarith [k3w_zero hM]
theorem cS5 (hM : 1 ≤ M) : cS M 5 = 0 := by rw [cS_5 hM]; linarith [k5w_zero hM]

end ArcsAlgo.LLT
