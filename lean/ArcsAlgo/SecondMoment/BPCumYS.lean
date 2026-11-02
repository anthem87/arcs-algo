module

public import ArcsAlgo.SecondMoment.BPCumX
set_option autoImplicit false

/-!
# Proposition B′: the cumulants of `Y = (w, εw)`, `S = w`, `X′ = (εw, ε′w)`, `Y′ = εw`

Moments, cumulants up to order 5 (`cY`, `cS`) and 6 (`cXu`, `cYu`), each by the moment–cumulant
recursion, and the vanishing of the cumulants odd in a sign coordinate.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

/-! ### `Y = (w, εw)` -/

noncomputable abbrev pY (M : ℕ) : Fin M × Bool → ℝ := fun _ => 1 / (2 * M)

theorem pY_nonneg (a : Fin M × Bool) : 0 ≤ pY M a := by positivity

theorem pY_sum (hM : 1 ≤ M) : ∑ a, pY M a = 1 := by
  have : (M : ℝ) ≠ 0 := by positivity
  simp [Fintype.card_prod]; field_simp

theorem prod_xiY (a : Fin M × Bool) (l : List (Fin 2)) :
    (l.map fun i => (xiY M a i : ℝ)).prod = (((a.1 : ℕ) : ℝ) + 1) ^ l.length * (sg a.2 : ℝ) ^ (l.count 1) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    fin_cases j <;> simp [xiY, pow_succ] <;> ring

theorem momY (hM : 1 ≤ M) (l : List (Fin 2)) :
    momL (pY M) (xiY M) l = if Even (l.count 1) then mw M l.length else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  unfold momL
  simp only [prod_xiY]
  rw [Fintype.sum_prod_type]
  have e : ∀ w : Fin M, ∑ x : Bool, (1 / (2 * (M : ℝ))) *
      ((((w : ℕ) : ℝ) + 1) ^ l.length * (sg x : ℝ) ^ (l.count 1)) =
      (1 / (2 * (M : ℝ))) * (((w : ℕ) : ℝ) + 1) ^ l.length * (∑ x : Bool, (sg x : ℝ) ^ (l.count 1)) := by
    intro w; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  simp only [e, sum_sg_pow]
  unfold mw
  by_cases h1 : Even (l.count 1) <;> simp only [h1, if_true, if_false, mul_zero, Finset.sum_const_zero]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; field_simp <;> ring

def canonY (a b : ℕ) : List (Fin 2) := List.replicate a 0 ++ List.replicate b 1

noncomputable def cY (M a b : ℕ) : ℝ := cumL (pY M) (xiY M) (canonY a b)

theorem cumL_eq_cY (hM : 1 ≤ M) (l : List (Fin 2)) :
    cumL (pY M) (xiY M) l = cY M (l.count 0) (l.count 1) := by
  unfold cY
  apply cumL_perm _ pY_nonneg (pY_sum hM)
  rw [List.perm_iff_count]
  intro x
  fin_cases x <;> simp [canonY, List.count_replicate]

theorem cY_odd1 (hM : 1 ≤ M) {a b : ℕ} (hb : Odd b) : cY M a b = 0 := by
  unfold cY
  refine cumL_refl_zero pY_nonneg (pY_sum hM) 1
    ⟨fun a => (a.1, !a.2), fun a => (a.1, !a.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonY, List.count_replicate] using hb)
  fin_cases j <;> simp [xiY, sg] <;> split_ifs <;> simp_all

/-! ### `S = w` -/

noncomputable abbrev pS (M : ℕ) : Fin M → ℝ := fun _ => 1 / M

theorem pS_nonneg (a : Fin M) : 0 ≤ pS M a := by positivity

theorem pS_sum (hM : 1 ≤ M) : ∑ a, pS M a = 1 := by
  have : (M : ℝ) ≠ 0 := by positivity
  simp; field_simp

theorem momS (l : List (Fin 1)) : momL (pS M) (xi1 M) l = mw M l.length := by
  unfold momL mw
  have e : ∀ a : Fin M, (l.map fun i => (xi1 M a i : ℝ)).prod = (((a : ℕ) : ℝ) + 1) ^ l.length := by
    intro a
    induction l with
    | nil => simp
    | cons j l ih => rw [List.map_cons, List.prod_cons, ih]; fin_cases j; simp [xi1, pow_succ]; ring
  simp only [e]; rw [← Finset.mul_sum]; ring

def canonS (a : ℕ) : List (Fin 1) := List.replicate a 0

noncomputable def cS (M a : ℕ) : ℝ := cumL (pS M) (xi1 M) (canonS a)

theorem cumL_eq_cS (hM : 1 ≤ M) (l : List (Fin 1)) : cumL (pS M) (xi1 M) l = cS M (l.count 0) := by
  unfold cS
  apply cumL_perm _ pS_nonneg (pS_sum hM)
  rw [List.perm_iff_count]
  intro x
  fin_cases x; simp [canonS, List.count_replicate]

/-! ### `X′ = (εw, ε′w)` and `Y′ = εw` (the unconditional statement) -/

def xiXu (M : ℕ) (a : Fin M × Bool × Bool) : Fin 2 → ℤ :=
  ![sg a.2.1 * ((a.1 : ℤ) + 1), sg a.2.2 * ((a.1 : ℤ) + 1)]

def xiYu (M : ℕ) (a : Fin M × Bool) : Fin 1 → ℤ := ![sg a.2 * ((a.1 : ℤ) + 1)]

theorem prod_xiXu (a : Fin M × Bool × Bool) (l : List (Fin 2)) :
    (l.map fun i => (xiXu M a i : ℝ)).prod =
      (((a.1 : ℕ) : ℝ) + 1) ^ l.length * (sg a.2.1 : ℝ) ^ (l.count 0) * (sg a.2.2 : ℝ) ^ (l.count 1) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    fin_cases j <;> simp [xiXu, pow_succ] <;> ring

theorem momXu (hM : 1 ≤ M) (l : List (Fin 2)) :
    momL (pX M) (xiXu M) l = if Even (l.count 0) ∧ Even (l.count 1) then mw M l.length else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  unfold momL
  simp only [prod_xiXu]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have e : ∀ w : Fin M, ∑ x : Bool, ∑ y : Bool, (1 / (4 * (M : ℝ))) *
      ((((w : ℕ) : ℝ) + 1) ^ l.length * (sg x : ℝ) ^ (l.count 0) * (sg y : ℝ) ^ (l.count 1)) =
      (1 / (4 * (M : ℝ))) * (((w : ℕ) : ℝ) + 1) ^ l.length *
        ((∑ x : Bool, (sg x : ℝ) ^ (l.count 0)) * (∑ y : Bool, (sg y : ℝ) ^ (l.count 1))) := by
    intro w
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  simp only [e, sum_sg_pow]
  unfold mw
  by_cases h1 : Even (l.count 0) <;> by_cases h2 : Even (l.count 1) <;>
    simp only [h1, h2, if_true, if_false, and_true, and_false, mul_zero,
      zero_mul, Finset.sum_const_zero, and_self]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; field_simp <;> ring

noncomputable def cXu (M a b : ℕ) : ℝ := cumL (pX M) (xiXu M) (canonY a b)

theorem cumL_eq_cXu (hM : 1 ≤ M) (l : List (Fin 2)) :
    cumL (pX M) (xiXu M) l = cXu M (l.count 0) (l.count 1) := by
  unfold cXu
  apply cumL_perm _ pX_nonneg (pX_sum hM)
  rw [List.perm_iff_count]
  intro x
  fin_cases x <;> simp [canonY, List.count_replicate]

theorem cXu_odd0 (hM : 1 ≤ M) {a b : ℕ} (ha : Odd a) : cXu M a b = 0 := by
  unfold cXu
  refine cumL_refl_zero pX_nonneg (pX_sum hM) 0
    ⟨fun a => (a.1, !a.2.1, a.2.2), fun a => (a.1, !a.2.1, a.2.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonY, List.count_replicate] using ha)
  fin_cases j <;> simp [xiXu, sg] <;> split_ifs <;> simp_all

theorem cXu_odd1 (hM : 1 ≤ M) {a b : ℕ} (hb : Odd b) : cXu M a b = 0 := by
  unfold cXu
  refine cumL_refl_zero pX_nonneg (pX_sum hM) 1
    ⟨fun a => (a.1, a.2.1, !a.2.2), fun a => (a.1, a.2.1, !a.2.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonY, List.count_replicate] using hb)
  fin_cases j <;> simp [xiXu, sg] <;> split_ifs <;> simp_all

theorem momYu (hM : 1 ≤ M) (l : List (Fin 1)) :
    momL (pY M) (xiYu M) l = if Even l.length then mw M l.length else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hp : ∀ a : Fin M × Bool, (l.map fun i => (xiYu M a i : ℝ)).prod =
      (((a.1 : ℕ) : ℝ) + 1) ^ l.length * (sg a.2 : ℝ) ^ l.length := by
    intro a
    induction l with
    | nil => simp
    | cons j l ih => rw [List.map_cons, List.prod_cons, ih]; fin_cases j; simp [xiYu, pow_succ]; ring
  unfold momL
  simp only [hp]
  rw [Fintype.sum_prod_type]
  have e : ∀ w : Fin M, ∑ x : Bool, (1 / (2 * (M : ℝ))) *
      ((((w : ℕ) : ℝ) + 1) ^ l.length * (sg x : ℝ) ^ l.length) =
      (1 / (2 * (M : ℝ))) * (((w : ℕ) : ℝ) + 1) ^ l.length * (∑ x : Bool, (sg x : ℝ) ^ l.length) := by
    intro w; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  simp only [e, sum_sg_pow]
  unfold mw
  by_cases h1 : Even l.length <;> simp only [h1, if_true, if_false, mul_zero, Finset.sum_const_zero]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; field_simp <;> ring

noncomputable def cYu (M a : ℕ) : ℝ := cumL (pY M) (xiYu M) (canonS a)

theorem cumL_eq_cYu (hM : 1 ≤ M) (l : List (Fin 1)) : cumL (pY M) (xiYu M) l = cYu M (l.count 0) := by
  unfold cYu
  apply cumL_perm _ pY_nonneg (pY_sum hM)
  rw [List.perm_iff_count]
  intro x
  fin_cases x; simp [canonS, List.count_replicate]

theorem cYu_odd (hM : 1 ≤ M) {a : ℕ} (ha : Odd a) : cYu M a = 0 := by
  unfold cYu
  refine cumL_refl_zero pY_nonneg (pY_sum hM) 0
    ⟨fun a => (a.1, !a.2), fun a => (a.1, !a.2), fun a => by simp, fun a => by simp⟩
    (fun _ => rfl) (fun a j => ?_) _ (by simpa [canonS, List.count_replicate] using ha)
  fin_cases j; simp [xiYu, sg]; split_ifs <;> simp_all

theorem cY_10 (hM : 1 ≤ M) : cY M 1 0 = mw M 1 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 []
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_20 (hM : 1 ≤ M) : cY M 2 0 = -mw M 1 ^ 2 + mw M 2 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_02 (hM : 1 ≤ M) : cY M 0 2 = mw M 2 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 1 [1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_30 (hM : 1 ≤ M) : cY M 3 0 = 2*mw M 1 ^ 3 - 3*mw M 1*mw M 2 + mw M 3 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0, 0]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_12 (hM : 1 ≤ M) : cY M 1 2 = -mw M 1*mw M 2 + mw M 3 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [1, 1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_40 (hM : 1 ≤ M) : cY M 4 0 = -6*mw M 1 ^ 4 + 12*mw M 1 ^ 2*mw M 2 - 4*mw M 1*mw M 3 - 3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0, 0, 0]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_22 (hM : 1 ≤ M) : cY M 2 2 = 2*mw M 1 ^ 2*mw M 2 - 2*mw M 1*mw M 3 - mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0, 1, 1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM, cY_40 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_04 (hM : 1 ≤ M) : cY M 0 4 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 1 [1, 1, 1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM, cY_40 hM, cY_22 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_50 (hM : 1 ≤ M) : cY M 5 0 = 24*mw M 1 ^ 5 - 60*mw M 1 ^ 3*mw M 2 + 20*mw M 1 ^ 2*mw M 3 + 30*mw M 1*mw M 2 ^ 2 - 5*mw M 1*mw M 4 - 10*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0, 0, 0, 0]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM, cY_40 hM, cY_22 hM, cY_04 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_32 (hM : 1 ≤ M) : cY M 3 2 = -6*mw M 1 ^ 3*mw M 2 + 6*mw M 1 ^ 2*mw M 3 + 6*mw M 1*mw M 2 ^ 2 - 3*mw M 1*mw M 4 - 4*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [0, 0, 1, 1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM, cY_40 hM, cY_22 hM, cY_04 hM, cY_50 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cY_14 (hM : 1 ≤ M) : cY M 1 4 = 6*mw M 1*mw M 2 ^ 2 - mw M 1*mw M 4 - 6*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pY M) (ξ := xiY M) pY_nonneg (pY_sum hM) 0 [1, 1, 1, 1]
  simp [splits, momY hM, cumL_eq_cY hM, mw_zero hM, Nat.even_iff, cY_10 hM, cY_20 hM, cY_02 hM, cY_30 hM, cY_12 hM, cY_40 hM, cY_22 hM, cY_04 hM, cY_50 hM, cY_32 hM] at h
  first | linarith | linear_combination -h | linear_combination h
theorem cS_1 (hM : 1 ≤ M) : cS M 1 = mw M 1 := by
  have h := mom_cum (p := pS M) (ξ := xi1 M) pS_nonneg (pS_sum hM) 0 []
  simp [splits, momS, cumL_eq_cS hM, mw_zero hM, Nat.even_iff] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cS_2 (hM : 1 ≤ M) : cS M 2 = -mw M 1 ^ 2 + mw M 2 := by
  have h := mom_cum (p := pS M) (ξ := xi1 M) pS_nonneg (pS_sum hM) 0 [0]
  simp [splits, momS, cumL_eq_cS hM, mw_zero hM, Nat.even_iff, cS_1 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cS_3 (hM : 1 ≤ M) : cS M 3 = 2*mw M 1 ^ 3 - 3*mw M 1*mw M 2 + mw M 3 := by
  have h := mom_cum (p := pS M) (ξ := xi1 M) pS_nonneg (pS_sum hM) 0 [0, 0]
  simp [splits, momS, cumL_eq_cS hM, mw_zero hM, Nat.even_iff, cS_1 hM, cS_2 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cS_4 (hM : 1 ≤ M) : cS M 4 = -6*mw M 1 ^ 4 + 12*mw M 1 ^ 2*mw M 2 - 4*mw M 1*mw M 3 - 3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pS M) (ξ := xi1 M) pS_nonneg (pS_sum hM) 0 [0, 0, 0]
  simp [splits, momS, cumL_eq_cS hM, mw_zero hM, Nat.even_iff, cS_1 hM, cS_2 hM, cS_3 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cS_5 (hM : 1 ≤ M) : cS M 5 = 24*mw M 1 ^ 5 - 60*mw M 1 ^ 3*mw M 2 + 20*mw M 1 ^ 2*mw M 3 + 30*mw M 1*mw M 2 ^ 2 - 5*mw M 1*mw M 4 - 10*mw M 2*mw M 3 + mw M 5 := by
  have h := mom_cum (p := pS M) (ξ := xi1 M) pS_nonneg (pS_sum hM) 0 [0, 0, 0, 0]
  simp [splits, momS, cumL_eq_cS hM, mw_zero hM, Nat.even_iff, cS_1 hM, cS_2 hM, cS_3 hM, cS_4 hM] at h
  first | linarith | linear_combination -h | linear_combination h
theorem cXu_20 (hM : 1 ≤ M) : cXu M 2 0 = mw M 2 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_02 (hM : 1 ≤ M) : cXu M 0 2 = mw M 2 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 1 [1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_40 (hM : 1 ≤ M) : cXu M 4 0 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0, 0, 0]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_22 (hM : 1 ≤ M) : cXu M 2 2 = -mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0, 1, 1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_04 (hM : 1 ≤ M) : cXu M 0 4 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 1 [1, 1, 1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM, cXu_22 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_60 (hM : 1 ≤ M) : cXu M 6 0 = 30*mw M 2 ^ 3 - 15*mw M 2*mw M 4 + mw M 6 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0, 0, 0, 0, 0]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM, cXu_22 hM, cXu_04 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_42 (hM : 1 ≤ M) : cXu M 4 2 = 6*mw M 2 ^ 3 - 7*mw M 2*mw M 4 + mw M 6 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0, 0, 0, 1, 1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM, cXu_22 hM, cXu_04 hM, cXu_60 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_24 (hM : 1 ≤ M) : cXu M 2 4 = 6*mw M 2 ^ 3 - 7*mw M 2*mw M 4 + mw M 6 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 0 [0, 1, 1, 1, 1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM, cXu_22 hM, cXu_04 hM, cXu_60 hM, cXu_42 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cXu_06 (hM : 1 ≤ M) : cXu M 0 6 = 30*mw M 2 ^ 3 - 15*mw M 2*mw M 4 + mw M 6 := by
  have h := mom_cum (p := pX M) (ξ := xiXu M) pX_nonneg (pX_sum hM) 1 [1, 1, 1, 1, 1]
  simp [splits, momXu hM, cumL_eq_cXu hM, mw_zero hM, Nat.even_iff, cXu_20 hM, cXu_02 hM, cXu_40 hM, cXu_22 hM, cXu_04 hM, cXu_60 hM, cXu_42 hM, cXu_24 hM] at h
  first | linarith | linear_combination -h | linear_combination h
theorem cYu_2 (hM : 1 ≤ M) : cYu M 2 = mw M 2 := by
  have h := mom_cum (p := pY M) (ξ := xiYu M) pY_nonneg (pY_sum hM) 0 [0]
  simp [splits, momYu hM, cumL_eq_cYu hM, mw_zero hM, Nat.even_iff] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cYu_4 (hM : 1 ≤ M) : cYu M 4 = -3*mw M 2 ^ 2 + mw M 4 := by
  have h := mom_cum (p := pY M) (ξ := xiYu M) pY_nonneg (pY_sum hM) 0 [0, 0, 0]
  simp [splits, momYu hM, cumL_eq_cYu hM, mw_zero hM, Nat.even_iff, cYu_2 hM] at h
  first | linarith | linear_combination -h | linear_combination h

theorem cYu_6 (hM : 1 ≤ M) : cYu M 6 = 30*mw M 2 ^ 3 - 15*mw M 2*mw M 4 + mw M 6 := by
  have h := mom_cum (p := pY M) (ξ := xiYu M) pY_nonneg (pY_sum hM) 0 [0, 0, 0, 0, 0]
  simp [splits, momYu hM, cumL_eq_cYu hM, mw_zero hM, Nat.even_iff, cYu_2 hM, cYu_4 hM] at h
  first | linarith | linear_combination -h | linear_combination h


end ArcsAlgo.LLT
