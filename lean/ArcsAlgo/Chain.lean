module

public import ArcsAlgo.Blur
public import ArcsAlgo.Brown
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.BigOperators.Intervals
set_option autoImplicit false

/-!
# The Subset Sum algorithm as propagation (paper §8)

Subset Sum is the chain `s₀ = 0`, `s_i = s_{i−1} + w_i x_i`, `x_i ∈ {0, 1}`, with the assertion
`s_n = T`. The domains of the chain are finite sets of naturals.

* `reach W`: the forward pass `R_i = R_{i−1} ∪ (R_{i−1} + w_i)` of Remark 2.4;
  `mem_reach` (Proposition 8.1): it is exactly the forward image of the definitions, i.e. the set
  of subset sums.
* `back W T j`: one backward round of the arc-consistency filters, from `i = n` down to `1`;
  `back_eq` and `back_greatest` (Proposition 8.2): it is the set of reachable and extendable
  values, and it is the greatest arc-consistent family below the forward domains (the fixpoint
  `W*` of `T_comp`); `greedy_spec`: the backward choice never gets stuck.
* Proposition 8.3: the dummies give a relaxation (`reach_subset_append`), complete but strictly
  larger on an explicit instance.
* Proposition 8.4: class counts mod `q` and Eval on the chain reduced mod `q`.
* Proposition 8.5: the telescoping inversion on counts, and an explicit pair of instances with
  the same dummies and the same `R(W ∪ D)` but different `R(W)`.
-/

@[expose] public section

namespace ArcsAlgo

open Finset

/-! ### Proposition 8.1 -/

/-- One forward step of the chain: the image of `s_{i−1} + w·x_i`, `x_i ∈ {0, 1}`. -/
def evalStep (R : Finset ℕ) (w : ℕ) : Finset ℕ := (R ×ˢ ({0, 1} : Finset ℕ)).image fun p => p.1 + w * p.2

/-- The forward pass `R_i = R_{i−1} ∪ (R_{i−1} + w_i)` (paper Remark 2.4). -/
def reach (W : List ℕ) : Finset ℕ := W.foldl (fun R w => R ∪ R.image (· + w)) {0}

theorem evalStep_eq (R : Finset ℕ) (w : ℕ) : evalStep R w = R ∪ R.image (· + w) := by
  ext v
  simp only [evalStep, mem_image, mem_product, mem_insert, mem_singleton, mem_union]
  constructor
  · rintro ⟨⟨a, x⟩, ⟨ha, hx | hx⟩, rfl⟩ <;> subst hx
    · left; simpa using ha
    · right; exact ⟨a, ha, by simp⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact ⟨⟨v, 0⟩, ⟨h, Or.inl rfl⟩, by simp⟩
    · exact ⟨⟨a, 1⟩, ⟨ha, Or.inr rfl⟩, by simp⟩

theorem reach_append_singleton (W : List ℕ) (w : ℕ) :
    reach (W ++ [w]) = reach W ∪ (reach W).image (· + w) := by
  simp [reach, List.foldl_append]

private theorem isSubsetSum_singleton {w t : ℕ} : IsSubsetSum [w] t ↔ t = 0 ∨ t = w := by
  rw [isSubsetSum_iff_sublist]
  constructor
  · rintro ⟨L, hL, rfl⟩
    rcases List.sublist_singleton.1 hL with rfl | rfl <;> simp
  · rintro (h | h)
    · exact ⟨[], List.nil_sublist _, by simp [h]⟩
    · exact ⟨[w], List.Sublist.refl _, by simp [h]⟩

/-- **Proposition 8.1 (forward pass = Eval)** (paper §8): the forward pass of Remark 2.4,
which is the forward image of the definitions `s_i = s_{i−1} + w_i x_i` (`evalStep_eq`),
computes exactly the values of `s_n`, i.e. the subset sums. -/
theorem mem_reach (W : List ℕ) (t : ℕ) : t ∈ reach W ↔ IsSubsetSum W t := by
  induction W using List.reverseRecOn generalizing t with
  | nil =>
    simp only [reach, List.foldl_nil, mem_singleton]
    exact ⟨fun h => h ▸ ⟨∅, by simp⟩, fun h => by simpa using le_sum_of_isSubsetSum h⟩
  | append_singleton W w ih =>
    rw [reach_append_singleton, mem_union, mem_image, isSubsetSum_append]
    simp only [ih, isSubsetSum_singleton]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact ⟨t, 0, h, Or.inl rfl, by simp⟩
      · exact ⟨a, w, ha, Or.inr rfl, rfl⟩
    · rintro ⟨a, b, ha, hb | hb, rfl⟩
      · left; simpa [hb] using ha
      · right; exact ⟨a, ha, by simp [hb]⟩

/-! ### Proposition 8.2 -/

/-- Forward domain of `s_i`: the subset sums of the first `i` weights. -/
def fwd (W : List ℕ) (i : ℕ) : Finset ℕ := reach (W.take i)

/-- The weight `w_{i+1}` at position `i` (`0` past the end). -/
def wAt (W : List ℕ) (i : ℕ) : ℕ := W.getD i 0

/-- One backward round of the arc-consistency filters on the chain, from `i = n` down to `1`:
`back W T j` is the domain of `s_{n−j}`. The domain of `s_n` is `R_n ∩ {T}`; the filter of the
constraint `s_i = s_{i−1} + w_i x_i` keeps in `s_{i−1}` the values `v` with `v` or `v + w_i` in the
domain of `s_i`. -/
def back (W : List ℕ) (T : ℕ) : ℕ → Finset ℕ
  | 0 => (fwd W W.length).filter (· = T)
  | j + 1 => (fwd W (W.length - (j + 1))).filter fun v =>
      v ∈ back W T j ∨ v + wAt W (W.length - (j + 1)) ∈ back W T j

/-- The values of `s_i` that are reachable from `0` and extendable to `T`. -/
def extendable (W : List ℕ) (T i v : ℕ) : Prop :=
  IsSubsetSum (W.take i) v ∧ ∃ e, IsSubsetSum (W.drop i) e ∧ v + e = T

private theorem drop_eq_wAt_cons {W : List ℕ} {i : ℕ} (hi : i < W.length) :
    W.drop i = wAt W i :: W.drop (i + 1) := by
  unfold wAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.drop_eq_getElem_cons hi

private theorem take_succ_eq {W : List ℕ} {i : ℕ} (hi : i < W.length) :
    W.take (i + 1) = W.take i ++ [wAt W i] := by
  unfold wAt
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

private theorem isSubsetSum_cons_iff {w : ℕ} {L : List ℕ} {e : ℕ} :
    IsSubsetSum (w :: L) e ↔ IsSubsetSum L e ∨ (w ≤ e ∧ IsSubsetSum L (e - w)) := by
  rw [show w :: L = [w] ++ L from rfl, isSubsetSum_append]
  simp only [isSubsetSum_singleton]
  constructor
  · rintro ⟨a, b, ha | ha, hb, rfl⟩ <;> subst ha
    · left; simpa using hb
    · right; exact ⟨by omega, by simpa using hb⟩
  · rintro (h | ⟨hw, h⟩)
    · exact ⟨0, e, Or.inl rfl, h, by simp⟩
    · exact ⟨w, e - w, Or.inr rfl, h, by omega⟩

/-- **Proposition 8.2, first part** (paper §8): after Eval, one backward round leaves in the
domain of `s_i` exactly the values that are reachable from `0` and extendable to `T`. -/
theorem back_eq (W : List ℕ) (T : ℕ) (j : ℕ) (hj : j ≤ W.length) (v : ℕ) :
    v ∈ back W T j ↔ extendable W T (W.length - j) v := by
  induction j generalizing v with
  | zero =>
    simp only [back, fwd, mem_filter, mem_reach, extendable, Nat.sub_zero, List.drop_length]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨h, 0, ⟨∅, by simp⟩, rfl⟩
    · rintro ⟨h, e, he, rfl⟩
      have := le_sum_of_isSubsetSum he
      simp at this; subst this; exact ⟨h, by simp⟩
  | succ j ih =>
    have hi : W.length - (j + 1) < W.length := by omega
    have hi1 : W.length - j = W.length - (j + 1) + 1 := by omega
    simp only [back, fwd, mem_filter, mem_reach, ih (by omega), extendable]
    rw [hi1]
    generalize W.length - (j + 1) = i at hi ⊢
    rw [drop_eq_wAt_cons hi, take_succ_eq hi]
    simp only [isSubsetSum_cons_iff]
    constructor
    · rintro ⟨hv, ⟨_, e, he, hsum⟩ | ⟨_, e, he, hsum⟩⟩
      · exact ⟨hv, e, Or.inl he, hsum⟩
      · exact ⟨hv, wAt W i + e, Or.inr ⟨by omega, by simpa using he⟩, by omega⟩
    · rintro ⟨hv, e, he | ⟨hwe, he⟩, hsum⟩
      · exact ⟨hv, Or.inl ⟨isSubsetSum_append.2 ⟨v, 0, hv, isSubsetSum_singleton.2 (Or.inl rfl),
          rfl⟩, e, he, hsum⟩⟩
      · exact ⟨hv, Or.inr ⟨isSubsetSum_append.2 ⟨v, _, hv, isSubsetSum_singleton.2 (Or.inr rfl),
          rfl⟩, e - wAt W i, he, by omega⟩⟩

/-- A family of domains `D i ⊆ R_i` (`i = 0, …, n`) is arc consistent for the chain when every
value of `s_{i−1}` has a support in `s_i` and every value of `s_i` has a support in `s_{i−1}`;
the assertion `s_n = T` restricts `D n ⊆ {T}`. -/
def ArcConsistent (W : List ℕ) (T : ℕ) (D : ℕ → Set ℕ) : Prop :=
  (∀ v ∈ D W.length, v = T) ∧
  ∀ i < W.length, (∀ v ∈ D i, v ∈ D (i + 1) ∨ v + wAt W i ∈ D (i + 1)) ∧
    (∀ v ∈ D (i + 1), v ∈ D i ∨ (wAt W i ≤ v ∧ v - wAt W i ∈ D i))

/-- **Proposition 8.2, fixpoint** (paper §8): the domains left by one backward round are arc
consistent, so one round reaches a fixpoint of the filters. -/
theorem back_arcConsistent (W : List ℕ) (T : ℕ) :
    ArcConsistent W T (fun i => {v | extendable W T i v}) := by
  refine ⟨?_, fun i hi => ⟨?_, ?_⟩⟩
  · rintro v ⟨_, e, he, hsum⟩
    rw [List.drop_length] at he
    have := le_sum_of_isSubsetSum he; simp at this; omega
  · rintro v ⟨hv, e, he, hsum⟩
    simp only [Set.mem_ofPred_eq, extendable]
    rw [drop_eq_wAt_cons hi, isSubsetSum_cons_iff] at he
    rw [take_succ_eq hi]
    rcases he with he | ⟨hwe, he⟩
    · left; exact ⟨isSubsetSum_append.2 ⟨v, 0, hv, isSubsetSum_singleton.2 (Or.inl rfl), rfl⟩,
        e, he, hsum⟩
    · right; exact ⟨isSubsetSum_append.2 ⟨v, _, hv, isSubsetSum_singleton.2 (Or.inr rfl), rfl⟩,
        e - wAt W i, he, by omega⟩
  · rintro v ⟨hv, e, he, hsum⟩
    simp only [Set.mem_ofPred_eq, extendable]
    rw [take_succ_eq hi, isSubsetSum_append] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := hv
    rcases isSubsetSum_singleton.1 hb with rfl | rfl
    · left; refine ⟨by simpa using ha, e, ?_, by simpa using hsum⟩
      rw [drop_eq_wAt_cons hi, isSubsetSum_cons_iff]; exact Or.inl he
    · right; refine ⟨by omega, by simpa using ha, wAt W i + e, ?_, by omega⟩
      rw [drop_eq_wAt_cons hi, isSubsetSum_cons_iff]; exact Or.inr ⟨by omega, by simpa using he⟩

/-- **Proposition 8.2, greatest fixpoint** (paper §8): every arc-consistent family below the
forward domains is contained in the domains left by one backward round; hence these are the
fixpoint `W*` of `T_comp` (the greatest arc-consistent family below the forward domains). -/
theorem back_greatest (W : List ℕ) (T : ℕ) (D : ℕ → Set ℕ) (hD : ArcConsistent W T D)
    (hR : ∀ i ≤ W.length, ∀ v ∈ D i, IsSubsetSum (W.take i) v) :
    ∀ i ≤ W.length, ∀ v ∈ D i, extendable W T i v := by
  have key : ∀ j ≤ W.length, ∀ v ∈ D (W.length - j),
      ∃ e, IsSubsetSum (W.drop (W.length - j)) e ∧ v + e = T := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [Nat.sub_zero] at hv ⊢
      exact ⟨0, by rw [List.drop_length]; exact ⟨∅, by simp⟩, by rw [hD.1 v hv]; simp⟩
    | succ j ih =>
      intro hj v hv
      have hi : W.length - (j + 1) < W.length := by omega
      have hi1 : W.length - j = W.length - (j + 1) + 1 := by omega
      have ih' := ih (by omega)
      rw [hi1] at ih'
      generalize W.length - (j + 1) = i at hi hv ih' ⊢
      rw [drop_eq_wAt_cons hi]
      rcases (hD.2 i hi).1 v hv with h | h
      · obtain ⟨e, he, hs⟩ := ih' v h
        exact ⟨e, isSubsetSum_cons_iff.2 (Or.inl he), hs⟩
      · obtain ⟨e, he, hs⟩ := ih' _ h
        exact ⟨wAt W i + e, isSubsetSum_cons_iff.2 (Or.inr ⟨by omega, by
          rwa [Nat.add_sub_cancel_left]⟩), by omega⟩
  intro i hi v hv
  refine ⟨hR i hi v hv, ?_⟩
  have := key (W.length - i) (by omega) v (by rwa [show W.length - (W.length - i) = i by omega])
  rwa [show W.length - (W.length - i) = i by omega] at this

/-- The backward choice "take `w_i` if `t − w_i ∈ R_{i−1}`", on the weights read from the last
one. `greedy W t` returns the chosen weights (in their order in `W`). -/
def greedy : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: W, t => if w ≤ t ∧ t - w ∈ reach W.reverse then greedy W (t - w) ++ [w] else greedy W t

/-- **Proposition 8.2, the backward choice never gets stuck** (paper §8): if `t ∈ R_n` then the
backward choice, run from `i = n` down to `1`, returns a sub-list of `W` with sum `t`. -/
theorem greedy_spec (W : List ℕ) (t : ℕ) (ht : t ∈ reach W) :
    (greedy W.reverse t).Sublist W ∧ (greedy W.reverse t).sum = t := by
  induction W using List.reverseRecOn generalizing t with
  | nil =>
    simp only [reach, List.foldl_nil, mem_singleton] at ht
    subst ht; simp [greedy]
  | append_singleton W w ih =>
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, greedy,
      List.reverse_reverse]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (t - w) h.2
      exact ⟨h1.append (List.Sublist.refl _), by simp [h2]; omega⟩
    · rw [reach_append_singleton, mem_union, mem_image] at ht
      rcases ht with ht | ⟨a, ha, rfl⟩
      · obtain ⟨h1, h2⟩ := ih t ht
        exact ⟨h1.trans (List.sublist_append_left _ _), h2⟩
      · exact absurd ⟨by omega, by simpa using ha⟩ h

/-! ### Proposition 8.3 -/

theorem reach_subset_append (W D : List ℕ) : reach W ⊆ reach (W ++ D) := by
  intro t ht
  rw [mem_reach] at ht ⊢
  exact isSubsetSum_append.2 ⟨t, 0, ht, ⟨∅, by simp⟩, by simp⟩

/-- **Proposition 8.3 (the dummies are an extension that does not block but does not
conserve)** (paper §8): `R(W) ⊆ R(W ∪ D)` for every `D`, so a negative answer on `W ∪ D` is
valid for `W` (`T ∉ R(W ∪ D) → T ∉ R(W)`). -/
theorem not_mem_of_not_mem_append {W D : List ℕ} {T : ℕ} (h : T ∉ reach (W ++ D)) :
    T ∉ reach W :=
  fun hT => h (reach_subset_append W D hT)

/-- **Proposition 8.3, strict inclusion** (paper §8): with `W = {3}` and the dummies `{1, 2}`,
`W ∪ D` is complete (`K = 1`), and the inclusion `R(W) ⊊ R(W ∪ D)` is strict. -/
theorem dummies_strict_example :
    reach [3] = {0, 3} ∧ reach ([3] ++ dummies 2) = {0, 1, 2, 3, 4, 5, 6} ∧
      reach [3] ⊂ reach ([3] ++ dummies 2) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The gap augmentation of paper §5.4 makes the chain complete (`K = 1`): if every weight of a
sorted list is at most one plus the sum of the earlier ones, every `T ≤ Σ` is reachable
(Lemma 2.1). -/
theorem reach_complete_of_gap (W : List ℕ)
    (h : ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum) :
    ∀ T ≤ W.sum, T ∈ reach W := fun T hT => (mem_reach W T).2 (brown_mpr W h T hT)

/-! ### Proposition 8.4 -/

/-- The class count `N_c(q)`: the number of sub-multisets with sum `≡ c (mod q)`. -/
def classCount (W : List ℕ) (q c : ℕ) : ℕ := W.sublists'.countP fun L => L.sum % q = c

/-- **Proposition 8.4 (the arcs are Eval on a quotient)** (paper §8): `N_c(q) > 0` iff the class
`c` survives Eval on the chain reduced mod `q` (the residue table `reachableMod` of the
checker, built by the same recurrence on `ℤ/q`). -/
theorem classCount_pos_iff {q c : ℕ} (W : List ℕ) (hq : 0 < q) (hc : c < q) :
    0 < classCount W q c ↔ (reachableMod q W)[c]! = true := by
  rw [reachableMod_exact hq hc, classCount, List.countP_pos_iff]
  constructor
  · rintro ⟨L, hL, h⟩
    obtain ⟨s, hs⟩ := isSubsetSum_iff_sublist.2 ⟨L, List.mem_sublists'.1 hL, rfl⟩
    exact ⟨s, by rw [hs]; simpa using h⟩
  · rintro ⟨s, hs⟩
    obtain ⟨L, hL, hsum⟩ := isSubsetSum_iff_sublist.1 ⟨s, rfl⟩
    exact ⟨L, List.mem_sublists'.2 hL, by simpa [hsum] using hs⟩

/-! ### Proposition 8.5 -/

/-- **Proposition 8.5 (the blur is invertible on counts)** (paper §8): with the dummies
`1, 2, …, 2^{k−1}`, `M = 2^k`,
`r_W(T) = Σ_{j ≥ 0} [r_{W∪D}(T − jM) − r_{W∪D}(T − jM − 1)]`; the terms with `jM > T` vanish,
so the sum is over `0 ≤ j ≤ T / M`. -/
theorem blur_telescoping (W : List ℕ) (k T : ℕ) :
    (count W T : ℤ) = ∑ j ∈ range (T / 2 ^ k + 1),
      (countZ (W ++ dummies k) ((T : ℤ) - j * 2 ^ k) -
        countZ (W ++ dummies k) ((T : ℤ) - j * 2 ^ k - 1)) := by
  have hstep : ∀ j : ℕ, countZ (W ++ dummies k) ((T : ℤ) - j * 2 ^ k) -
      countZ (W ++ dummies k) ((T : ℤ) - j * 2 ^ k - 1) =
      countZ W ((T : ℤ) - j * 2 ^ k) - countZ W ((T : ℤ) - (j + 1 : ℕ) * 2 ^ k) := by
    intro j
    rw [← blur_recovery]
    push_cast; ring_nf
  simp only [hstep]
  rw [Finset.sum_range_sub' (fun j : ℕ => countZ W ((T : ℤ) - j * 2 ^ k))]
  have hneg : (T : ℤ) - ((T / 2 ^ k + 1 : ℕ) : ℤ) * 2 ^ k < 0 := by
    have h := Nat.lt_div_mul_add (a := T) (b := 2 ^ k) (by positivity)
    push_cast
    have : (T : ℤ) < (T / 2 ^ k : ℕ) * 2 ^ k + 2 ^ k := by exact_mod_cast h
    push_cast at this
    linarith
  rw [show countZ W ((T : ℤ) - ((T / 2 ^ k + 1 : ℕ) : ℤ) * 2 ^ k) = 0 by
    unfold countZ; exact ite_eq_left_of_eq_true _ _ (eq_true hneg)]
  simp [countZ]

/-- **Proposition 8.5, Boolean part** (paper §8): in `𝔹[ℤ]` the blur cannot be inverted:
with the same dummy `D = {1}`, `W₁ = {2, 2, 4}` and `W₂ = {2, 3, 3}` have the same
`R(W ∪ D)` but different `R(W)`. -/
theorem blur_not_invertible_on_sets :
    reach ([2, 2, 4] ++ dummies 1) = reach ([2, 3, 3] ++ dummies 1) ∧
      reach [2, 2, 4] ≠ reach [2, 3, 3] := by
  refine ⟨by decide, by decide⟩

end ArcsAlgo
