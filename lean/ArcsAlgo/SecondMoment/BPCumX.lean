module

public import ArcsAlgo.SecondMoment.EdgeSym
public import ArcsAlgo.SecondMoment.LemmaB
set_option autoImplicit false

/-!
# Proposition B′: the cumulants of `X = (w, εw, ε′w)`

The moments `momX` (`E X^l = m_{|l|}` if the numbers of `εw` and `ε′w` factors are even, else `0`, with
`m_k = E w^k`), the cumulants `cX a b c = χ_{(a,b,c)}` up to order 5 (each by the moment–cumulant
recursion `mom_cum`), and the vanishing of the cumulants odd in a sign coordinate (`cX_odd1`, `cX_odd2`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

/-- The raw moments `m_k = E w^k` of `w` uniform in `{1, …, M}`. -/
noncomputable def mw (M k : ℕ) : ℝ := (∑ a : Fin M, ((a : ℝ) + 1) ^ k) / M

theorem mw_zero (hM : 1 ≤ M) : mw M 0 = 1 := by
  have : (M : ℝ) ≠ 0 := by positivity
  simp [mw, this]

/-- The law of `X = (w, εw, ε′w)`. -/
noncomputable abbrev pX (M : ℕ) : Fin M × Bool × Bool → ℝ := fun _ => 1 / (4 * M)

theorem pX_nonneg (a : Fin M × Bool × Bool) : 0 ≤ pX M a := by positivity

theorem pX_sum (hM : 1 ≤ M) : ∑ a, pX M a = 1 := by
  have : (M : ℝ) ≠ 0 := by positivity
  simp [Fintype.card_prod]; field_simp

theorem sum_sg_pow (c : ℕ) : ∑ b : Bool, (sg b : ℝ) ^ c = if Even c then 2 else 0 := by
  simp only [Fintype.sum_bool, sg, if_true, Bool.false_eq_true, if_false]
  push_cast
  split_ifs with h
  · rw [h.neg_one_pow]; norm_num
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]; norm_num

theorem prod_xiX (a : Fin M × Bool × Bool) (l : List (Fin 3)) :
    (l.map fun i => (xiX M a i : ℝ)).prod =
      (((a.1 : ℕ) : ℝ) + 1) ^ l.length * (sg a.2.1 : ℝ) ^ (l.count 1) * (sg a.2.2 : ℝ) ^ (l.count 2) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    fin_cases j <;> simp [xiX, List.count_cons, pow_succ] <;> ring

theorem momX (hM : 1 ≤ M) (l : List (Fin 3)) :
    momL (pX M) (xiX M) l = if Even (l.count 1) ∧ Even (l.count 2) then mw M l.length else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  unfold momL
  simp only [prod_xiX]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have e : ∀ w : Fin M, ∑ x : Bool, ∑ y : Bool, (1 / (4 * (M : ℝ))) *
      ((((w : ℕ) : ℝ) + 1) ^ l.length * (sg x : ℝ) ^ (l.count 1) * (sg y : ℝ) ^ (l.count 2)) =
      (1 / (4 * (M : ℝ))) * (((w : ℕ) : ℝ) + 1) ^ l.length *
        ((∑ x : Bool, (sg x : ℝ) ^ (l.count 1)) * (∑ y : Bool, (sg y : ℝ) ^ (l.count 2))) := by
    intro w
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  simp only [e, sum_sg_pow]
  unfold mw
  by_cases h1 : Even (l.count 1) <;> by_cases h2 : Even (l.count 2) <;>
    simp only [h1, h2, if_true, if_false, and_true, and_false, true_and, false_and, mul_zero,
      zero_mul, Finset.sum_const_zero, not_false_eq_true, and_self]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; field_simp; ring

/-- The canonical list with `a` zeros, `b` ones and `c` twos. -/
def canonX (a b c : ℕ) : List (Fin 3) := List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2

/-- The cumulant `χ_{(a,b,c)}` of `X`. -/
noncomputable def cX (M a b c : ℕ) : ℝ := cumL (pX M) (xiX M) (canonX a b c)

theorem cumL_eq_cX (hM : 1 ≤ M) (l : List (Fin 3)) :
    cumL (pX M) (xiX M) l = cX M (l.count 0) (l.count 1) (l.count 2) := by
  unfold cX
  apply cumL_perm _ pX_nonneg (pX_sum hM)
  rw [List.perm_iff_count]
  intro x
  fin_cases x <;> simp [canonX, List.count_replicate]

theorem cX_odd1 (hM : 1 ≤ M) {a b c : ℕ} (hb : Odd b) : cX M a b c = 0 := by
  unfold cX
  refine cumL_refl_zero pX_nonneg (pX_sum hM) 1
    ⟨fun a => (a.1, !a.2.1, a.2.2), fun a => (a.1, !a.2.1, a.2.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonX, List.count_replicate] using hb)
  fin_cases j <;> simp [xiX, sg] <;> split_ifs <;> simp_all

theorem cX_odd2 (hM : 1 ≤ M) {a b c : ℕ} (hc : Odd c) : cX M a b c = 0 := by
  unfold cX
  refine cumL_refl_zero pX_nonneg (pX_sum hM) 2
    ⟨fun a => (a.1, a.2.1, !a.2.2), fun a => (a.1, a.2.1, !a.2.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonX, List.count_replicate] using hc)
  fin_cases j <;> simp [xiX, sg] <;> split_ifs <;> simp_all

theorem cX_100 (hM : 1 ≤ M) : cX M 1 0 0 = mw M 1 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 []
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM] at h
  linarith

theorem cX_200 (hM : 1 ≤ M) : cX M 2 0 0 = mw M 2 - mw M 1 ^ 2 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM] at h
  linarith

theorem cX_120 (hM : 1 ≤ M) : cX M 1 2 0 = mw M 3 - mw M 1 * mw M 2 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [1, 1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_odd1 hM] at h
  linarith

theorem cX_002 (hM : 1 ≤ M) : cX M 0 0 2 = mw M 2 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 2 [2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_020 (hM : 1 ≤ M) : cX M 0 2 0 = mw M 2 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 1 [1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_300 (hM : 1 ≤ M) : cX M 3 0 0 = 2*mw M 1 ^ 3 - 3*mw M 1*mw M 2 + mw M 3 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 0]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_102 (hM : 1 ≤ M) : cX M 1 0 2 = -mw M 1*mw M 2 + mw M 3 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_400 (hM : 1 ≤ M) : cX M 4 0 0 = -6*mw M 1 ^ 4 + 12*mw M 1 ^ 2*mw M 2 - 4*mw M 1*mw M 3 - 3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 0, 0]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_202 (hM : 1 ≤ M) : cX M 2 0 2 = 2*mw M 1 ^ 2*mw M 2 - 2*mw M 1*mw M 3 - mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_220 (hM : 1 ≤ M) : cX M 2 2 0 = 2*mw M 1 ^ 2*mw M 2 - 2*mw M 1*mw M 3 - mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 1, 1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_004 (hM : 1 ≤ M) : cX M 0 0 4 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 2 [2, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_022 (hM : 1 ≤ M) : cX M 0 2 2 = -mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 1 [1, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_040 (hM : 1 ≤ M) : cX M 0 4 0 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 1 [1, 1, 1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_500 (hM : 1 ≤ M) : cX M 5 0 0 = 24*mw M 1 ^ 5 - 60*mw M 1 ^ 3*mw M 2 + 20*mw M 1 ^ 2*mw M 3 + 30*mw M 1*mw M 2 ^ 2 - 5*mw M 1*mw M 4 - 10*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 0, 0, 0]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_302 (hM : 1 ≤ M) : cX M 3 0 2 = -6*mw M 1 ^ 3*mw M 2 + 6*mw M 1 ^ 2*mw M 3 + 6*mw M 1*mw M 2 ^ 2 - 3*mw M 1*mw M 4 - 4*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 0, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM, cX_500 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_320 (hM : 1 ≤ M) : cX M 3 2 0 = -6*mw M 1 ^ 3*mw M 2 + 6*mw M 1 ^ 2*mw M 3 + 6*mw M 1*mw M 2 ^ 2 - 3*mw M 1*mw M 4 - 4*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [0, 0, 1, 1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM, cX_500 hM, cX_302 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_104 (hM : 1 ≤ M) : cX M 1 0 4 = 6*mw M 1*mw M 2 ^ 2 - mw M 1*mw M 4 - 6*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [2, 2, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM, cX_500 hM, cX_302 hM, cX_320 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_122 (hM : 1 ≤ M) : cX M 1 2 2 = 2*mw M 1*mw M 2 ^ 2 - mw M 1*mw M 4 - 2*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [1, 1, 2, 2]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM, cX_500 hM, cX_302 hM, cX_320 hM, cX_104 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cX_140 (hM : 1 ≤ M) : cX M 1 4 0 = 6*mw M 1*mw M 2 ^ 2 - mw M 1*mw M 4 - 6*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pX M) (ξ := xiX M) pX_nonneg (pX_sum hM) 0 [1, 1, 1, 1]
  simp [splits, momX hM, cumL_eq_cX hM, mw_zero hM, Nat.even_iff, cX_100 hM, cX_200 hM, cX_120 hM, cX_002 hM, cX_020 hM, cX_300 hM, cX_102 hM, cX_400 hM, cX_202 hM, cX_220 hM, cX_004 hM, cX_022 hM, cX_040 hM, cX_500 hM, cX_302 hM, cX_320 hM, cX_104 hM, cX_122 hM] at h
  first | linarith | linear_combination -h | linear_combination h


end ArcsAlgo.LLT
