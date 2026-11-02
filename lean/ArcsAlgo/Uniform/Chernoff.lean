module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false

/-!
# A Chernoff bound for the binomial (paper §6.3)

`binom_tail`: `Σ_{|k − m/2| ≥ t} C(m,k) ≤ 2·2^m e^{−2t²/m}`, through
`Σ_k C(m,k) e^{θ(k−m/2)} = (2 cosh(θ/2))^m ≤ 2^m e^{mθ²/8}`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- `Σ_k C(m,k) e^{θ(k − m/2)} ≤ 2^m e^{mθ²/8}`. -/
theorem binom_mgf (m : ℕ) (θ : ℝ) :
    ∑ k ∈ range (m + 1), (m.choose k : ℝ) * exp (θ * ((k : ℝ) - m / 2)) ≤
      2 ^ m * exp (m * θ ^ 2 / 8) := by
  have h := add_pow (exp (θ / 2)) (exp (-(θ / 2))) m
  have hterm : ∀ k ∈ range (m + 1), (m.choose k : ℝ) * exp (θ * ((k : ℝ) - m / 2)) =
      exp (θ / 2) ^ k * exp (-(θ / 2)) ^ (m - k) * (m.choose k : ℝ) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, Nat.cast_sub hk']
    rw [mul_comm]; congr 2; ring
  rw [sum_congr rfl hterm, ← h]
  have hc : exp (θ / 2) + exp (-(θ / 2)) = 2 * cosh (θ / 2) := by rw [cosh_eq]; ring
  rw [hc, mul_pow]
  have : cosh (θ / 2) ^ m ≤ exp ((θ / 2) ^ 2 / 2) ^ m :=
    pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) m
  rw [← exp_nat_mul] at this
  calc 2 ^ m * cosh (θ / 2) ^ m ≤ 2 ^ m * exp (m * ((θ / 2) ^ 2 / 2)) := by gcongr
    _ = 2 ^ m * exp (m * θ ^ 2 / 8) := by congr 2; ring

/-- **Chernoff bound for the binomial, upper tail.** -/
theorem binom_upper {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2), (m.choose k : ℝ) ≤
      2 ^ m * exp (-(2 * t ^ 2 / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set θ := 4 * t / m
  have hθ : 0 ≤ θ := by positivity
  calc ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2), (m.choose k : ℝ)
      ≤ ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2),
          (m.choose k : ℝ) * exp (θ * ((k : ℝ) - m / 2) - θ * t) := by
        refine sum_le_sum fun k hk => ?_
        have := (mem_filter.mp hk).2
        have h1 : 1 ≤ exp (θ * ((k : ℝ) - m / 2) - θ * t) :=
          one_le_exp (by nlinarith)
        nlinarith [(Nat.cast_nonneg (m.choose k) : (0 : ℝ) ≤ _)]
    _ ≤ ∑ k ∈ range (m + 1), (m.choose k : ℝ) * exp (θ * ((k : ℝ) - m / 2) - θ * t) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = exp (-(θ * t)) * ∑ k ∈ range (m + 1), (m.choose k : ℝ) * exp (θ * ((k : ℝ) - m / 2)) := by
        rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
        rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (-(θ * t)) * (2 ^ m * exp (m * θ ^ 2 / 8)) := by gcongr; exact binom_mgf m θ
    _ = 2 ^ m * exp (-(2 * t ^ 2 / m)) := by
        rw [mul_comm, mul_assoc, ← exp_add]; congr 2
        simp only [θ]; field_simp; ring

/-- **Chernoff bound for the binomial, two tails.** -/
theorem binom_tail {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ |(k : ℝ) - m / 2|), (m.choose k : ℝ) ≤
      2 * 2 ^ m * exp (-(2 * t ^ 2 / m)) := by
  have hsplit : (range (m + 1)).filter (fun k : ℕ => t ≤ |(k : ℝ) - m / 2|) ⊆
      (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2) ∪
      (range (m + 1)).filter (fun k : ℕ => t ≤ ((m - k : ℕ) : ℝ) - m / 2) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk1)
    rw [mem_union, mem_filter, mem_filter, Nat.cast_sub hkm]
    rcases le_abs'.mp hk2 with h | h
    · right; exact ⟨hk1, by linarith⟩
    · left; exact ⟨hk1, h⟩
  have hlow : ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ ((m - k : ℕ) : ℝ) - m / 2),
      (m.choose k : ℝ) =
      ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2), (m.choose k : ℝ) := by
    apply sum_nbij' (fun k => m - k) (fun k => m - k)
    · intro k hk
      obtain ⟨hk1, hk2⟩ := mem_filter.mp (mem_coe.mp hk)
      exact mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr (by omega), hk2⟩)
    · intro k hk
      obtain ⟨hk1, hk2⟩ := mem_filter.mp (mem_coe.mp hk)
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk1)
      refine mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩)
      rwa [Nat.sub_sub_self hkm]
    · intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp (mem_coe.mp hk)).1)
      exact Nat.sub_sub_self hkm
    · intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp (mem_coe.mp hk)).1)
      exact Nat.sub_sub_self hkm
    · intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)
      rw [Nat.choose_symm hkm]
  calc _ ≤ ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2) ∪
        (range (m + 1)).filter (fun k : ℕ => t ≤ ((m - k : ℕ) : ℝ) - m / 2), (m.choose k : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => by positivity
    _ ≤ 2 * 2 ^ m * exp (-(2 * t ^ 2 / m)) := by
        have hu := sum_union_inter (s₁ := (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2))
          (s₂ := (range (m + 1)).filter (fun k : ℕ => t ≤ ((m - k : ℕ) : ℝ) - m / 2))
          (f := fun k => (m.choose k : ℝ))
        have hi : 0 ≤ ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => t ≤ (k : ℝ) - m / 2) ∩
            (range (m + 1)).filter (fun k : ℕ => t ≤ ((m - k : ℕ) : ℝ) - m / 2),
            (m.choose k : ℝ) := sum_nonneg fun _ _ => by positivity
        have := binom_upper hm ht
        linarith

end ArcsAlgo.LLT
