module

public import ArcsAlgo.Uniform.FirstId
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false

/-!
# Theorem LV: the factors against the Gaussian (paper §6.6)

`cos x ≤ e^{−x²/2}` for `|x| ≤ 2` and `cos x ≥ e^{−x²/2}(1 − x⁴/4)` for `|x| ≤ 1`, and the
corresponding bounds for products (`prod_cos_le`, `prod_cos_ge`).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- `cos y ≤ e^{−y²/2}` for `|y| ≤ 1`. -/
theorem cos_le_exp_one {y : ℝ} (hy : |y| ≤ 1) : Real.cos y ≤ Real.exp (-(y ^ 2 / 2)) := by
  have hc := Real.cos_bound hy
  set t := y ^ 2 / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hy2 : y ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy 2; rwa [sq_abs, one_pow] at this
  have ht1 : t ≤ 1 / 2 := by rw [ht]; linarith
  have he := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg ht0]; linarith) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one] at he
  norm_num at he
  rw [abs_of_nonneg ht0] at he
  have he1 := (abs_le.mp he).1
  have hcu := (abs_le.mp hc).2
  have hy4 : |y| ^ 4 = y ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [hy4] at hcu
  have hy4' : y ^ 4 = 4 * t ^ 2 := by rw [ht]; ring
  rw [hy4'] at hcu
  nlinarith [mul_nonneg ht0 ht0, mul_nonneg (mul_nonneg ht0 ht0) ht0]

/-- `cos x ≤ e^{−x²/2}` for `|x| ≤ 2` (by halving: `cos x = 2cos²(x/2) − 1`). -/
theorem cos_le_exp {x : ℝ} (hx : |x| ≤ 2) : Real.cos x ≤ Real.exp (-(x ^ 2 / 2)) := by
  have hx2 : |x / 2| ≤ 1 := by rw [abs_div, abs_two]; linarith
  have hc := cos_le_exp_one hx2
  have hc0 : 0 ≤ Real.cos (x / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    have := abs_le.mp hx2
    constructor <;> linarith [Real.pi_gt_three]
  have e : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    rw [Real.cos_sq (x / 2), show 2 * (x / 2) = x by ring]; ring
  set t := Real.exp (-((x / 2) ^ 2 / 2))
  have ht : Real.exp (-(x ^ 2 / 2)) = (t ^ 2) ^ 2 := by
    rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ht]
  have : Real.cos (x / 2) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc0 hc 2
  nlinarith [sq_nonneg (t ^ 2 - 1)]

/-- `e^{−x²/2}(1 − x⁴/4) ≤ cos x` for `|x| ≤ 1`. -/
theorem exp_mul_le_cos {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp (-(x ^ 2 / 2)) * (1 - x ^ 4 / 4) ≤ Real.cos x := by
  have hx2 : x ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2; rwa [sq_abs, one_pow] at this
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 : 1 + x ^ 2 / 2 ≤ Real.exp (x ^ 2 / 2) := by
    have := Real.add_one_le_exp (x ^ 2 / 2); linarith
  have h3 : 0 ≤ Real.exp (-(x ^ 2 / 2)) * (1 - x ^ 2 / 2) := by
    apply mul_nonneg (Real.exp_pos _).le; linarith
  have e : Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have e2 : 1 - x ^ 4 / 4 = (1 - x ^ 2 / 2) * (1 + x ^ 2 / 2) := by ring
  calc Real.exp (-(x ^ 2 / 2)) * (1 - x ^ 4 / 4)
      = Real.exp (-(x ^ 2 / 2)) * (1 - x ^ 2 / 2) * (1 + x ^ 2 / 2) := by rw [e2]; ring
    _ ≤ Real.exp (-(x ^ 2 / 2)) * (1 - x ^ 2 / 2) * Real.exp (x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 1 - x ^ 2 / 2 := by rw [mul_right_comm, e, one_mul]
    _ ≤ Real.cos x := h1

/-- `Π(1 − a_i) ≥ 1 − Σ a_i` for `a_i ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hp0 : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hp1 : ∏ i ∈ s, (1 - a i) ≤ 1 :=
      prod_le_one₀ (fun i hi => by linarith [h1 i (mem_insert_of_mem hi)])
        (fun i hi => by linarith [h0 i (mem_insert_of_mem hi)])
    have ha0 := h0 j (mem_insert_self j s)
    have ha1 := h1 j (mem_insert_self j s)
    have hs0 : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

/-- **The product against the Gaussian.** With `x_i = πW_iθ`, `g = Π e^{−x_i²/2}`:
if every `|x_i| ≤ 2` then `Π cos x_i ≤ g` (and `≥ 0` when every `|x_i| ≤ π/2`);
if every `|x_i| ≤ 1` then `Π cos x_i ≥ g(1 − Σ x_i⁴/4)`. -/
theorem prod_cos_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| ≤ π / 2) :
    0 ≤ ∏ i ∈ s, Real.cos (x i) ∧
      ∏ i ∈ s, Real.cos (x i) ≤ Real.exp (-(∑ i ∈ s, x i ^ 2) / 2) := by
  have hc0 : ∀ i ∈ s, 0 ≤ Real.cos (x i) := fun i hi => by
    apply Real.cos_nonneg_of_mem_Icc
    have := abs_le.mp (hx i hi); constructor <;> linarith
  refine ⟨prod_nonneg hc0, ?_⟩
  rw [neg_div, sum_div, ← sum_neg_distrib, Real.exp_sum]
  refine prod_le_prod₀ hc0 fun i hi => ?_
  exact cos_le_exp ((hx i hi).trans (by linarith [Real.pi_le_four]))

theorem prod_cos_ge {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| ≤ 1) :
    Real.exp (-(∑ i ∈ s, x i ^ 2) / 2) * (1 - ∑ i ∈ s, x i ^ 4 / 4) ≤ ∏ i ∈ s, Real.cos (x i) := by
  have hx4 : ∀ i ∈ s, x i ^ 4 / 4 ≤ 1 := fun i hi => by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hx i hi) 4
    rw [one_pow, pow_abs, abs_of_nonneg (by positivity)] at h
    linarith
  have hw := one_sub_sum_le_prod s (fun i => x i ^ 4 / 4) (fun i _ => by positivity) hx4
  rw [neg_div, sum_div, ← sum_neg_distrib, Real.exp_sum]
  calc (∏ i ∈ s, Real.exp (-(x i ^ 2 / 2))) * (1 - ∑ i ∈ s, x i ^ 4 / 4)
      ≤ (∏ i ∈ s, Real.exp (-(x i ^ 2 / 2))) * ∏ i ∈ s, (1 - x i ^ 4 / 4) :=
        mul_le_mul_of_nonneg_left hw (prod_nonneg fun _ _ => (Real.exp_pos _).le)
    _ = ∏ i ∈ s, (Real.exp (-(x i ^ 2 / 2)) * (1 - x i ^ 4 / 4)) := by rw [prod_mul_distrib]
    _ ≤ ∏ i ∈ s, Real.cos (x i) := by
        refine prod_le_prod₀ (fun i hi => mul_nonneg (Real.exp_pos _).le (by linarith [hx4 i hi]))
          fun i hi => exp_mul_le_cos (hx i hi)

end ArcsAlgo.LLT
