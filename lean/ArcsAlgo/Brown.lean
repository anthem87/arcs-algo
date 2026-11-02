module

public import ArcsAlgo.Checker
set_option autoImplicit false

/-!
# Gap filling (Brown), paper Lemma 2.1

Let `w₁ ≤ … ≤ wₙ` be positive integers and `S_k = Σ_{i ≤ k} w_i`, `S₀ = 0`. Every integer
`0 ≤ T ≤ Sₙ` is a subset sum iff `w_{k+1} ≤ 1 + S_k` for every `0 ≤ k < n`.

With `W : List ℕ`, the weight `w_{k+1}` is `W.get ⟨k, _⟩` and `S_k` is `(W.take k).sum`.
Sortedness is stated as `W.Pairwise (· ≤ ·)`, which is what `List.Sorted (· ≤ ·)` unfolded to;
the pinned Mathlib no longer has `List.Sorted`.

* The direction `←` (`brown_mpr`) holds for any list, sorted or not.
* The direction `→` (`brown_mp`) needs sortedness: `W = [2, 1]` has every `T ∈ [0, 3]` as a
  subset sum, but `w₁ = 2 > 1 + S₀`.
* Positivity of the weights is not needed in either direction.
-/

@[expose] public section

namespace ArcsAlgo

/-- The direction `←` of paper Lemma 2.1, for the prefix of length `k`: if
`w_{j+1} ≤ 1 + S_j` for every `j < k`, every `T ≤ S_k` is a sum of a sublist of `W.take k`.
No sortedness is needed. -/
theorem brown_prefix (W : List ℕ)
    (h : ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum) :
    ∀ k ≤ W.length, ∀ T ≤ (W.take k).sum, ∃ L : List ℕ, L.Sublist (W.take k) ∧ L.sum = T := by
  intro k
  induction k with
  | zero => intro _ T hT; exact ⟨[], List.nil_sublist _, by simp at hT; simp [hT]⟩
  | succ k ih =>
    intro hk T hT
    have hk' : k < W.length := hk
    have htake : W.take (k + 1) = W.take k ++ [W[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some]
    have hw := h k hk'
    simp only [List.get_eq_getElem] at hw
    rw [htake] at hT ⊢
    rw [List.sum_append, List.sum_singleton] at hT
    by_cases hT' : T ≤ (W.take k).sum
    · obtain ⟨L, hL, rfl⟩ := ih (by omega) T hT'
      exact ⟨L, hL.trans (List.sublist_append_left _ _), rfl⟩
    · obtain ⟨L, hL, hs⟩ := ih (by omega) (T - W[k]) (by omega)
      exact ⟨L ++ [W[k]], hL.append_right _, by rw [List.sum_append, hs]; simp; omega⟩

/-- The direction `←` of paper Lemma 2.1 (gap filling): if `w_{k+1} ≤ 1 + S_k` for every
`k < n`, every `T ≤ Sₙ` is a subset sum. This holds for any list of weights, sorted or not. -/
theorem brown_mpr (W : List ℕ)
    (h : ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum) :
    ∀ T ≤ W.sum, IsSubsetSum W T := by
  intro T hT
  obtain ⟨L, hL, hs⟩ := brown_prefix W h W.length le_rfl T (by rwa [List.take_length])
  exact isSubsetSum_iff_sublist.2 ⟨L, by rwa [List.take_length] at hL, hs⟩

/-- The direction `→` of paper Lemma 2.1: if `W` is sorted increasingly and every
`T ≤ Sₙ` is a subset sum, then `w_{k+1} ≤ 1 + S_k` for every `k < n`. Sortedness is needed
(`W = [2, 1]` is a counterexample without it); positivity is not. -/
theorem brown_mp (W : List ℕ) (hW : W.Pairwise (· ≤ ·))
    (h : ∀ T ≤ W.sum, IsSubsetSum W T) :
    ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum := by
  intro k hk
  simp only [List.get_eq_getElem]
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  -- The target `S_k + 1` lies in `[0, Sₙ]` but is not a subset sum.
  have hdrop := List.drop_eq_getElem_cons hk
  have hsum : (W.take k).sum + 1 ≤ W.sum := by
    rw [← List.sum_take_add_sum_drop W k, hdrop, List.sum_cons]
    omega
  obtain ⟨L, hL, hs⟩ := isSubsetSum_iff_sublist.1 (h _ hsum)
  rw [← List.take_append_drop k W, List.sublist_append_iff] at hL
  obtain ⟨L₁, L₂, rfl, hL₁, hL₂⟩ := hL
  have h₁ : L₁.sum ≤ (W.take k).sum := hL₁.sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [List.sum_append] at hs
  cases L₂ with
  | nil => simp at hs; omega
  | cons x L₂ =>
    -- `x` is a weight of index `≥ k`, hence `x ≥ w_{k+1} > S_k + 1`.
    have hx : x ∈ W.drop k := hL₂.subset List.mem_cons_self
    have hsorted : (W.drop k).Pairwise (· ≤ ·) := hW.sublist (List.drop_sublist _ _)
    rw [hdrop] at hx hsorted
    have hkx : W[k] ≤ x := by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact List.pairwise_cons.1 hsorted |>.1 x hx
    have : x ≤ (x :: L₂).sum := List.le_sum_of_mem List.mem_cons_self
    omega

/-- Paper Lemma 2.1 (gap filling, Brown): for weights `w₁ ≤ … ≤ wₙ`, every
`0 ≤ T ≤ Sₙ` is a subset sum iff `w_{k+1} ≤ 1 + S_k` for every `0 ≤ k < n`.
Sortedness is used only in the direction `→` (see `brown_mp`, `brown_mpr`); the positivity
hypothesis of the paper is not used in either direction. -/
theorem brown (W : List ℕ) (hW : W.Pairwise (· ≤ ·)) (_hpos : ∀ w ∈ W, 0 < w) :
    (∀ T ≤ W.sum, IsSubsetSum W T) ↔
      ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum :=
  ⟨brown_mp W hW, brown_mpr W⟩

end ArcsAlgo
