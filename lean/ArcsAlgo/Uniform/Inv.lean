module

public import ArcsAlgo.LocalLimit.Fourier
set_option autoImplicit false

/-!
# The trivial bound (T1) (paper §6.7, Lemma V)

`lawS_le_inv`: `Pr(S_k = v) ≤ 1/M` for `k ≥ 1`, since the last weight is determined by the others;
`lawS_zero_ne`: `Pr(S_0 = v) = 0` for `v ≠ 0`.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

/-- (T1) `Pr(S_k = v) ≤ 1/M` for `k ≥ 1`: the last weight is determined by the others. -/
theorem lawS_le_inv {M n : ℕ} (hM : 0 < M) (v : ℤ) : lawS M (n + 1) v ≤ 1 / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (univ.filter fun w : Fin (n + 1) → Fin M => ∑ i, ((w i : ℤ) + 1) = v).card ≤
      (univ : Finset (Fin n → Fin M)).card := by
    apply card_le_card_of_injOn (fun w => Fin.init w)
    · intro w _; simp
    · intro w hw w' hw' h
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
      have hinit : Fin.init w = Fin.init w' := h
      rw [Fin.sum_univ_castSucc] at hw hw'
      have hi : ∀ i : Fin n, w (Fin.castSucc i) = w' (Fin.castSucc i) := fun i =>
        congrFun hinit i
      have hs : ∑ i : Fin n, ((w (Fin.castSucc i) : ℤ) + 1) =
          ∑ i : Fin n, ((w' (Fin.castSucc i) : ℤ) + 1) := by simp only [hi]
      have hl : w (Fin.last n) = w' (Fin.last n) := by
        apply Fin.ext; omega
      funext i
      refine Fin.lastCases hl (fun j => hi j) i
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard
  unfold lawS
  rw [div_le_div_iff₀ (by positivity) hM', pow_succ]
  have : ((univ.filter fun w : Fin (n + 1) → Fin M => ∑ i, ((w i : ℤ) + 1) = v).card : ℝ) ≤
      (M : ℝ) ^ n := by exact_mod_cast hcard
  nlinarith [pow_pos hM' n]

/-- `Pr(S_0 = v) = [v = 0]`. -/
theorem lawS_zero_ne {M : ℕ} {v : ℤ} (hv : v ≠ 0) : lawS M 0 v = 0 := by
  unfold lawS; simp [hv.symm]

end ArcsAlgo.LLT
