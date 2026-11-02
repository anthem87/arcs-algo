module

public import ArcsAlgo.Uniform.Unif
set_option autoImplicit false

/-!
# The binomial weights through Lemma B0′ with `M = 2` (paper §6.3)

`choose_div_eq_lawS`: `C(m,j)/2^m = Pr(S_m = m + j)` for weights in `{1, 2}`; hence
`binom_gauss`: `|C(m,j)/2^m − √(2/(πm)) e^{−2(j − m/2)²/m}| ≤ 34/(m√m)` for `m ≥ 2`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

theorem card_sum_two (m j : ℕ) :
    (univ.filter fun w : Fin m → Fin 2 => ∑ i, ((w i : ℤ) + 1) = (m : ℤ) + j).card = m.choose j := by
  let e : (Fin m → Fin 2) ≃ Finset (Fin m) :=
    { toFun := fun w => univ.filter fun i => w i = 1
      invFun := fun P i => if i ∈ P then 1 else 0
      left_inv := fun w => by
        funext i; rcases fin2_cases (w i) with h | h <;> simp [h]
      right_inv := fun P => by ext i; by_cases h : i ∈ P <;> simp [h] }
  have hsum : ∀ w : Fin m → Fin 2, ∑ i, ((w i : ℤ) + 1) = (m : ℤ) + (e w).card := by
    intro w
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin]
    simp only [e, Equiv.coe_fn_mk, nsmul_eq_mul, mul_one]
    rw [add_comm]; congr 1
    rw [card_filter]; push_cast
    refine sum_congr rfl fun i _ => ?_
    rcases fin2_cases (w i) with h | h <;> simp [h]
  have hc : m.choose j = (powersetCard j (univ : Finset (Fin m))).card := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hc]
  apply card_bij (fun w _ => e w)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, hsum] at hw
    simp only [mem_powersetCard, subset_univ, true_and]; omega
  · intro w _ w' _ h; exact e.injective h
  · intro P hP
    refine ⟨e.symm P, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, hsum, Equiv.apply_symm_apply]
    rw [(mem_powersetCard.mp hP).2]

/-- The binomial weights are the law of `S_m` for `M = 2`: `C(m,j)/2^m = Pr(S_m = m + j)`. -/
theorem choose_div_eq_lawS (m j : ℕ) : (m.choose j : ℝ) / 2 ^ m = lawS 2 m ((m : ℤ) + j) := by
  unfold lawS; rw [card_sum_two]; norm_num

/-- The Gaussian of the binomial: `b(j) = √(2/(πm)) e^{−2(j − m/2)²/m}`. -/
noncomputable def binG (m : ℕ) (x : ℝ) : ℝ := √(2 / (π * m)) * exp (-(2 * (x - m / 2) ^ 2 / m))

/-- **De Moivre–Laplace, uniform**: `|C(m,j)/2^m − b(j)| ≤ 34/(m√m)` for `m ≥ 2`
(Lemma B0′ with `M = 2`). -/
theorem binom_gauss {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    |(m.choose j : ℝ) / 2 ^ m - binG m j| ≤ 34 / (m * √(m : ℝ)) := by
  have h := lemmaB0'_gauss (M := 2) (le_refl 2) hm ((m : ℤ) + j)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs : sig2 2 = 1 / 4 := by unfold sig2; norm_num
  have hss : √(sig2 2) = 1 / 2 := by
    rw [hs, show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hg : gaussB 2 m ((m : ℤ) + j) = binG m j := by
    unfold gaussB binG zB tB
    rw [hss, hs, muW]
    congr 1
    · rw [show 2 * π * (m : ℝ) * (1 / 4) = π * m / 2 by ring, one_div, ← Real.sqrt_inv]
      congr 1; field_simp
    · congr 1
      have hsq : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
      push_cast
      field_simp
      rw [hsq]; ring
  rw [choose_div_eq_lawS, ← hg]
  refine h.trans ?_
  rw [hss]
  have hCB := CB_le (M := 2) (le_refl 2) hm
  calc CB 2 m / (1 / 2 * (m * √(m : ℝ))) ≤ 17 / (1 / 2 * (m * √(m : ℝ))) := by gcongr
    _ = 34 / (m * √(m : ℝ)) := by field_simp; ring

end ArcsAlgo.LLT
