module

public import ArcsAlgo.Chain
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
set_option autoImplicit false

/-!
# The floor: the primes without the weight 1 (paper §2)

* `reach_primes` (Proposition 2.3): for `N ≥ 5` the subset sums of the primes `≤ N` are exactly
  `[0, Σ_N] ∖ {1, 4, 6, Σ_N − 6, Σ_N − 4, Σ_N − 1}`; `reach_primes_small` covers `N = 2, 3`;
  `reach_primes_intervals` gives the seven maximal intervals for `N ≥ 7`.
* `richert`: every integer greater than 6 is a sum of distinct primes [Richert].
* Remark 2.4: `reach_eq_sum` (`R_n = Π_k ({0} ⊕ {w_k})` in the Boolean group semiring, written
  with the pointwise sum of finite sets) and `card_reach_le` (`|R_n| ≤ min(2^n, S_n + 1)`).
-/

@[expose] public section

namespace ArcsAlgo

open Finset

/-- The primes `≤ N`, in increasing order. -/
def primesUpTo (N : ℕ) : List ℕ := (List.range (N + 1)).filter Nat.Prime

theorem primesUpTo_succ (N : ℕ) :
    primesUpTo (N + 1) = if (N + 1).Prime then primesUpTo N ++ [N + 1] else primesUpTo N := by
  simp only [primesUpTo, List.range_succ, List.filter_append]
  split_ifs with h <;> simp [h]

theorem sum_primesUpTo_mono {N M : ℕ} (h : N ≤ M) : (primesUpTo N).sum ≤ (primesUpTo M).sum := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [primesUpTo_succ]
    split_ifs
    · simp only [List.sum_append, List.sum_singleton]; omega
    · exact ih

/-- The bound used in the induction of Proposition 2.3: for a prime `p ≥ 13`, the primes below
`p` sum to at least `p + 13` (Bertrand's postulate; `D_n` is increasing). -/
theorem sum_primes_below (p : ℕ) (hp : p.Prime) (h13 : 13 ≤ p) : p + 13 ≤ (primesUpTo (p - 1)).sum := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    obtain ⟨q, hq, hqp, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul ((p - 1) / 2) (by omega)
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hqlt : q < p := by omega
    have hsum : (primesUpTo (q - 1)).sum + q ≤ (primesUpTo (p - 1)).sum := by
      have h1 : primesUpTo q = primesUpTo (q - 1) ++ [q] := by
        have := primesUpTo_succ (q - 1)
        rw [show q - 1 + 1 = q from by have := hq.two_le; omega] at this
        rw [this, ite_eq_left_of_eq_true _ _ (eq_true hq)]
      have h2 := sum_primesUpTo_mono (N := q) (M := p - 1) (by omega)
      rw [h1, List.sum_append, List.sum_singleton] at h2
      exact h2
    by_cases hq13 : 13 ≤ q
    · have := ih q hqlt hq hq13
      omega
    · -- here `p < 26`, and `p ∈ {13, 17, 19, 23}`
      have hp26 : p < 26 := by omega
      interval_cases p <;> first | (exfalso; revert hp; decide) | decide

/-- The six holes `{1, 4, 6, Σ − 6, Σ − 4, Σ − 1}`. -/
def IsHole (S t : ℕ) : Prop := t = 1 ∨ t = 4 ∨ t = 6 ∨ t + 6 = S ∨ t + 4 = S ∨ t + 1 = S

instance (S t : ℕ) : Decidable (IsHole S t) := by unfold IsHole; infer_instance

theorem iff_of_checks {R : Finset ℕ} {S : ℕ} (h1 : ∀ t ∈ R, t ≤ S ∧ ¬ IsHole S t)
    (h2 : ∀ t ∈ range (S + 1), ¬ IsHole S t → t ∈ R) : ∀ t, t ∈ R ↔ t ≤ S ∧ ¬ IsHole S t :=
  fun t => ⟨h1 t, fun ⟨ht, hh⟩ => h2 t (mem_range.2 (by omega)) hh⟩

theorem reach_primes_base (N : ℕ) (h5 : 5 ≤ N) (h11 : N ≤ 11) :
    ∀ t, t ∈ reach (primesUpTo N) ↔ t ≤ (primesUpTo N).sum ∧ ¬ IsHole (primesUpTo N).sum t := by
  interval_cases N <;> exact iff_of_checks (by decide) (by decide)

/-- **Proposition 2.3 (the primes without the weight 1)** (paper §2): for `N ≥ 5` the subset sums
of `P_N = {p ≤ N}` are exactly `[0, Σ_N] ∖ {1, 4, 6, Σ_N − 6, Σ_N − 4, Σ_N − 1}`. -/
theorem reach_primes (N : ℕ) (h5 : 5 ≤ N) :
    ∀ t, t ∈ reach (primesUpTo N) ↔ t ≤ (primesUpTo N).sum ∧ ¬ IsHole (primesUpTo N).sum t := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h11 : N + 1 ≤ 11
    · exact reach_primes_base (N + 1) h5 h11
    have ih := ih (by omega)
    rw [primesUpTo_succ]
    split_ifs with hp
    · have hbound := sum_primes_below (N + 1) hp (by
        by_contra h
        have : N + 1 = 12 := by omega
        rw [this] at hp; exact absurd hp (by decide))
      simp only [Nat.add_sub_cancel] at hbound
      set S := (primesUpTo N).sum
      intro t
      rw [reach_append_singleton, mem_union, mem_image, List.sum_append, List.sum_singleton]
      constructor
      · rintro (h | ⟨a, ha, rfl⟩)
        · obtain ⟨h1, h2⟩ := (ih t).1 h
          refine ⟨by omega, ?_⟩
          unfold IsHole at h2 ⊢
          -- below 7 only `R_n` contributes; the top holes move up
          by_contra hh
          rcases hh with hh | hh | hh | hh | hh | hh <;> exact h2 (by omega)
        · obtain ⟨h1, h2⟩ := (ih a).1 ha
          refine ⟨by omega, ?_⟩
          unfold IsHole at h2 ⊢
          omega
      · rintro ⟨h1, h2⟩
        unfold IsHole at h2
        by_cases hlow : t ≤ S ∧ ¬ IsHole S t
        · left; exact (ih t).2 hlow
        · right
          refine ⟨t - (N + 1), (ih _).2 ⟨by unfold IsHole at hlow; omega, ?_⟩, by
            unfold IsHole at hlow; omega⟩
          unfold IsHole at hlow ⊢
          omega
    · exact ih

/-- **Proposition 2.3, small cases** (paper §2): for `N = 2` and `N = 3` the missing values in
`[0, Σ_N]` are `{1}` and `{1, 4}`. -/
theorem reach_primes_small :
    (∀ t, t ∈ reach (primesUpTo 2) ↔ t ≤ 2 ∧ t ≠ 1) ∧
      ∀ t, t ∈ reach (primesUpTo 3) ↔ t ≤ 5 ∧ t ≠ 1 ∧ t ≠ 4 := by
  refine ⟨fun t => ⟨fun h => ?_, fun h => ?_⟩, fun t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : ∀ t ∈ reach (primesUpTo 2), t ≤ 2 ∧ t ≠ 1 := by decide
    exact this t h
  · have : ∀ t ∈ range 3, t ≠ 1 → t ∈ reach (primesUpTo 2) := by decide
    exact this t (mem_range.2 (by omega)) h.2
  · have : ∀ t ∈ reach (primesUpTo 3), t ≤ 5 ∧ t ≠ 1 ∧ t ≠ 4 := by decide
    exact this t h
  · have : ∀ t ∈ range 6, t ≠ 1 → t ≠ 4 → t ∈ reach (primesUpTo 3) := by decide
    exact this t (mem_range.2 (by omega)) h.2.1 h.2.2

/-- **Proposition 2.3, the seven intervals** (paper §2): for `N ≥ 7` the reachable set is
`{0} ∪ [2, 3] ∪ {5} ∪ [7, Σ_N − 7] ∪ {Σ_N − 5} ∪ [Σ_N − 3, Σ_N − 2] ∪ {Σ_N}`, and the seven
pieces are separated by the six holes. -/
theorem reach_primes_intervals (N : ℕ) (h7 : 7 ≤ N) (t : ℕ) :
    t ∈ reach (primesUpTo N) ↔
      t = 0 ∨ (2 ≤ t ∧ t ≤ 3) ∨ t = 5 ∨ (7 ≤ t ∧ t + 7 ≤ (primesUpTo N).sum) ∨
        t + 5 = (primesUpTo N).sum ∨ (t + 3 ≥ (primesUpTo N).sum ∧ t + 2 ≤ (primesUpTo N).sum) ∨
        t = (primesUpTo N).sum := by
  have hS : 17 ≤ (primesUpTo N).sum := by
    have := sum_primesUpTo_mono h7
    have h7' : (primesUpTo 7).sum = 17 := by decide
    omega
  rw [reach_primes N (by omega)]
  unfold IsHole
  omega

/-- **Richert's theorem** [Richert], as a corollary of Proposition 2.3 (paper §2): every integer
greater than 6 is a sum of distinct primes. -/
theorem richert (m : ℕ) (hm : 6 < m) : ∃ L : List ℕ, L.Nodup ∧ (∀ p ∈ L, p.Prime) ∧ L.sum = m := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (m + 13)
  have hS := sum_primes_below p hp (by omega)
  have hmem : m ∈ reach (primesUpTo (p - 1)) := by
    rw [reach_primes (p - 1) (by omega)]
    refine ⟨by omega, ?_⟩
    unfold IsHole; omega
  obtain ⟨L, hL, hsum⟩ := isSubsetSum_iff_sublist.1 ((mem_reach _ _).1 hmem)
  refine ⟨L, (List.nodup_range.filter _).sublist hL, fun q hq => ?_, hsum⟩
  have := hL.subset hq
  simp only [primesUpTo, List.mem_filter, decide_eq_true_eq] at this
  exact this.2

/-! ### Remark 2.4 -/

open Pointwise in
/-- **Remark 2.4 (interval representation)** (paper §2): in the Boolean group semiring (union as
addition, Minkowski sum as multiplication, unit `{0}`), `R_n = Π_k ({0} ⊕ {w_k})`. -/
theorem reach_eq_sum (W : List ℕ) : reach W = (W.map fun w => ({0, w} : Finset ℕ)).sum := by
  induction W using List.reverseRecOn with
  | nil => rfl
  | append_singleton W w ih =>
    rw [reach_append_singleton, List.map_append, List.sum_append, ← ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ext t
    simp only [mem_union, mem_image, Finset.mem_add, mem_insert, mem_singleton]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact ⟨t, h, 0, Or.inl rfl, by simp⟩
      · exact ⟨a, ha, w, Or.inr rfl, rfl⟩
    · rintro ⟨a, ha, b, hb | hb, rfl⟩ <;> subst hb
      · left; simpa using ha
      · right; exact ⟨a, ha, rfl⟩

/-- **Remark 2.4, size of the reachable sets** (paper §2): `|R_n| ≤ min(2^n, S_n + 1)`; hence the
number `K_n` of maximal intervals is at most `min(2^n, S_n + 1)`. -/
theorem card_reach_le (W : List ℕ) :
    (reach W).card ≤ 2 ^ W.length ∧ (reach W).card ≤ W.sum + 1 := by
  refine ⟨?_, ?_⟩
  · induction W using List.reverseRecOn with
    | nil => simp [reach]
    | append_singleton W w ih =>
      rw [reach_append_singleton, List.length_append, List.length_singleton, pow_succ]
      calc _ ≤ (reach W).card + ((reach W).image (· + w)).card := card_union_le _ _
        _ ≤ (reach W).card + (reach W).card := Nat.add_le_add_left card_image_le _
        _ ≤ _ := by omega
  · have : reach W ⊆ range (W.sum + 1) := by
      intro t ht
      rw [mem_reach] at ht
      have := le_sum_of_isSubsetSum ht
      rw [mem_range]; omega
    simpa using card_le_card this

end ArcsAlgo
