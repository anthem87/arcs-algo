module

public import ArcsAlgo.Checker
public import Mathlib.Data.Nat.ModEq
set_option autoImplicit false

/-!
# The exhaustive NO certificate `(-3, -3)`

In the default solver ARCS, the answer `(NO, -3, -3)` means that an exhaustive endgame ran on the
whole instance and found no subset with sum `T` (paper §5.7, *Parameters derived from the
instance*; pseudocode `ARCS`, line 29). It carries no data: it is checked by any exact search.

* `existsSubsetSum`: an exact decision procedure by meet-in-the-middle (pseudocode `MITM`): all
  subset sums of the first half, the subset sums of the second half sorted, and a binary search
  for `T - a` for each sum `a` of the first half; `existsSubsetSum_iff` proves it equal to
  `IsSubsetSum`.
* `checkExhaustiveNo W T = !existsSubsetSum W T`, with `checkExhaustiveNo_sound`.
* `isSubsetSum_iff_residue`: the residue decomposition of `RESIDUE-SCAN`. For `P ≥ 1` and any
  split of `W` into two parts `A`, `B`, `T` is a subset sum iff for some `r < P` there are subset
  sums `a` of `A` and `b` of `B` with `a ≡ r`, `b ≡ T - r (mod P)` and `a + b = T`; and the
  residue is unique (`residue_unique`: it is `a % P`). So the scan over all `r ∈ [0, P)` is
  exhaustive and finds each solution at exactly one `r`.
-/

@[expose] public section

namespace ArcsAlgo

/-! ### Subset sums of a concatenation and of a permutation -/

/-- A subset sum of `A ++ B` is a subset sum of `A` plus a subset sum of `B` (paper §5.7;
pseudocode `MITM` and `RESIDUE-SCAN`). -/
theorem isSubsetSum_append {A B : List ℕ} {T : ℕ} :
    IsSubsetSum (A ++ B) T ↔ ∃ a b, IsSubsetSum A a ∧ IsSubsetSum B b ∧ a + b = T := by
  simp only [isSubsetSum_iff_sublist, List.sublist_append_iff]
  constructor
  · rintro ⟨L, ⟨L₁, L₂, rfl, h₁, h₂⟩, rfl⟩
    exact ⟨L₁.sum, L₂.sum, ⟨L₁, h₁, rfl⟩, ⟨L₂, h₂, rfl⟩, (List.sum_append).symm⟩
  · rintro ⟨_, _, ⟨L₁, h₁, rfl⟩, ⟨L₂, h₂, rfl⟩, rfl⟩
    exact ⟨L₁ ++ L₂, ⟨L₁, L₂, rfl, h₁, h₂⟩, List.sum_append⟩

/-- The subset sums do not depend on the order of the weights (paper §5.7; pseudocode `ARCS`,
line 3, sorts the weights). -/
theorem isSubsetSum_perm {W W' : List ℕ} (h : W.Perm W') {T : ℕ} :
    IsSubsetSum W T ↔ IsSubsetSum W' T := by
  suffices H : ∀ {W W' : List ℕ}, W.Perm W' → IsSubsetSum W T → IsSubsetSum W' T from
    ⟨H h, H h.symm⟩
  intro W W' h hs
  obtain ⟨L, hL, rfl⟩ := isSubsetSum_iff_sublist.1 hs
  obtain ⟨L', hp, hL'⟩ := hL.subperm.trans h.subperm
  exact isSubsetSum_iff_sublist.2 ⟨L', hL', hp.sum_eq⟩

/-! ### Residue decomposition (`RESIDUE-SCAN`) -/

/-- The residue `r < P` of `a` is unique: it is `a % P` (paper §5.7; pseudocode `RESIDUE-SCAN`,
line 3: every solution has exactly one `r`). -/
theorem residue_unique {P : ℕ} (hP : 1 ≤ P) (a : ℕ) : ∃! r, r < P ∧ a ≡ r [MOD P] := by
  refine ⟨a % P, ⟨Nat.mod_lt _ hP, (Nat.mod_modEq a P).symm⟩, ?_⟩
  rintro r ⟨hr, h⟩
  have : a % P = r % P := h
  rw [this, Nat.mod_eq_of_lt hr]

/-- The residue decomposition of `RESIDUE-SCAN` (paper §5.7; pseudocode `RESIDUE-SCAN`,
lines 3–5): for `P ≥ 1` and any split of `W` into two parts `A` and `B` (`W` a permutation of
`A ++ B`), `T` is a subset sum of `W` iff for some `r < P` there are a subset sum `a` of `A` and
a subset sum `b` of `B` with `a ≡ r`, `b ≡ T - r (mod P)` and `a + b = T`. -/
theorem isSubsetSum_iff_residue {P : ℕ} (hP : 1 ≤ P) {W A B : List ℕ} (hW : W.Perm (A ++ B))
    (T : ℕ) :
    IsSubsetSum W T ↔ ∃ r < P, ∃ a b, IsSubsetSum A a ∧ IsSubsetSum B b ∧
      a ≡ r [MOD P] ∧ b ≡ T - r [MOD P] ∧ a + b = T := by
  rw [isSubsetSum_perm hW, isSubsetSum_append]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine ⟨a % P, Nat.mod_lt _ hP, a, b, ha, hb, (Nat.mod_modEq a P).symm, ?_, rfl⟩
    have h := Nat.mod_add_div a P
    have : a + b - a % P = b + P * (a / P) := by omega
    show b % P = (a + b - a % P) % P
    rw [this, Nat.add_mul_mod_self_left]
  · rintro ⟨_, _, a, b, ha, hb, _, _, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩

/-! ### All subset sums -/

/-- All subset sums of `L`, with multiplicity, as an array (pseudocode `ALL-SUMS`): start from
`[0]`; each weight `w` appends the sums shifted by `w`. -/
def allSums (L : List ℕ) : Array ℕ :=
  L.foldl (fun acc w => acc ++ acc.map (· + w)) #[0]

/-- Invariant of the fold of `allSums`. -/
private theorem mem_foldl_allSums (L : List ℕ) :
    ∀ (acc : Array ℕ) (x : ℕ), x ∈ L.foldl (fun acc w => acc ++ acc.map (· + w)) acc ↔
      ∃ y ∈ acc, ∃ L' : List ℕ, L'.Sublist L ∧ x = y + L'.sum := by
  induction L with
  | nil =>
    intro acc x
    simp only [List.foldl_nil, List.sublist_nil]
    constructor
    · exact fun h => ⟨x, h, [], rfl, by simp⟩
    · rintro ⟨y, hy, _, rfl, rfl⟩
      simpa using hy
  | cons w L ih =>
    intro acc x
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨y, hy, L', hL', rfl⟩
      rcases Array.mem_append.1 hy with hy | hy
      · exact ⟨y, hy, L', hL'.cons w, rfl⟩
      · obtain ⟨z, hz, rfl⟩ := Array.mem_map.1 hy
        exact ⟨z, hz, w :: L', hL'.cons_cons w, by simp; omega⟩
    · rintro ⟨y, hy, L', hL', rfl⟩
      rcases List.sublist_cons_iff.1 hL' with hL' | ⟨r, rfl, hr⟩
      · exact ⟨y, Array.mem_append.2 (Or.inl hy), L', hL', rfl⟩
      · exact ⟨y + w, Array.mem_append.2 (Or.inr (Array.mem_map.2 ⟨y, hy, rfl⟩)), r, hr,
          by simp; omega⟩

/-- `x` is in `allSums L` iff some sublist of `L` sums to `x` (pseudocode `ALL-SUMS`). -/
theorem mem_allSums {L : List ℕ} {x : ℕ} :
    x ∈ allSums L ↔ ∃ L' : List ℕ, L'.Sublist L ∧ L'.sum = x := by
  unfold allSums
  rw [mem_foldl_allSums]
  constructor
  · rintro ⟨y, hy, L', hL', rfl⟩
    have : y = 0 := by simpa using hy
    exact ⟨L', hL', by simp [this]⟩
  · rintro ⟨L', hL', rfl⟩
    exact ⟨0, by simp, L', hL', by simp⟩

/-! ### Binary search in a sorted array -/

/-- Binary search for `x` in `s[lo‥hi)`; `s` is assumed sorted increasingly. -/
def bsearchGo (s : Array ℕ) (x : ℕ) (lo hi : ℕ) : Bool :=
  if lo < hi then
    if s.getD ((lo + hi) / 2) 0 < x then bsearchGo s x ((lo + hi) / 2 + 1) hi
    else if x < s.getD ((lo + hi) / 2) 0 then bsearchGo s x lo ((lo + hi) / 2)
    else true
  else false
termination_by hi - lo
decreasing_by all_goals omega

/-- Binary search for `x` in the sorted array `s`. -/
def bsearch (s : Array ℕ) (x : ℕ) : Bool := bsearchGo s x 0 s.size

/-- A successful search has found `x` at some index `< hi`. -/
theorem bsearchGo_sound (s : Array ℕ) (x : ℕ) :
    ∀ lo hi, bsearchGo s x lo hi = true → ∃ i, i < hi ∧ s.getD i 0 = x := by
  intro lo hi
  induction lo, hi using bsearchGo.induct s x with
  | case1 lo hi h h1 ih =>
    intro H; rw [bsearchGo] at H; simp only [h, h1, ↓reduceIte] at H; exact ih H
  | case2 lo hi h h1 h2 ih =>
    intro H; rw [bsearchGo] at H; simp only [h, h1, h2, ↓reduceIte] at H
    obtain ⟨i, hi, hx⟩ := ih H; exact ⟨i, by omega, hx⟩
  | case3 lo hi h h1 h2 =>
    intro _; exact ⟨(lo + hi) / 2, by omega, by omega⟩
  | case4 lo hi h =>
    intro H; rw [bsearchGo] at H; simp [h] at H

/-- The search finds `x` if it occurs in `s[lo‥hi)` and `s` is sorted on `[0, hi)`. -/
theorem bsearchGo_complete (s : Array ℕ) (x : ℕ)
    (hs : ∀ i j, i ≤ j → j < s.size → s.getD i 0 ≤ s.getD j 0) :
    ∀ lo hi, hi ≤ s.size → ∀ i, lo ≤ i → i < hi → s.getD i 0 = x → bsearchGo s x lo hi = true := by
  intro lo hi
  induction lo, hi using bsearchGo.induct s x with
  | case1 lo hi h h1 ih =>
    intro hhi i hlo hi' hx
    rw [bsearchGo]; simp only [h, h1, ↓reduceIte]
    refine ih hhi i ?_ hi' hx
    by_contra hc
    have := hs i ((lo + hi) / 2) (by omega) (by omega)
    omega
  | case2 lo hi h h1 h2 ih =>
    intro hhi i hlo hi' hx
    rw [bsearchGo]; simp only [h, h1, h2, ↓reduceIte]
    refine ih (by omega) i hlo ?_ hx
    by_contra hc
    have := hs ((lo + hi) / 2) i (by omega) (by omega)
    omega
  | case3 lo hi h h1 h2 =>
    intro _ _ _ _ _
    rw [bsearchGo]; simp only [h, h1, h2, ↓reduceIte]
  | case4 lo hi h =>
    intro _ i hlo hi' _; omega

/-- `bsearch s x = true` iff `x ∈ s`, for `s` sorted increasingly. -/
theorem bsearch_iff (s : Array ℕ) (x : ℕ) (hs : s.toList.Pairwise (· ≤ ·)) :
    bsearch s x = true ↔ x ∈ s := by
  have hs' : ∀ i j, i ≤ j → j < s.size → s.getD i 0 ≤ s.getD j 0 := by
    intro i j hij hj
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    have := List.pairwise_iff_getElem.1 hs i j (by simp; omega) (by simpa using hj) hij
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show i < s.size by omega),
      Array.getElem?_eq_getElem hj] using this
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := bsearchGo_sound s x 0 s.size h
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  · intro h
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem h
    exact bsearchGo_complete s _ hs' 0 s.size le_rfl i (Nat.zero_le _) hi
      (by simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi])

/-! ### Exact decision by meet-in-the-middle -/

/-- Exact decision of the subset-sum problem by meet-in-the-middle (paper §5.7; pseudocode
`MITM`, `ALL-SUMS`, `SORTED-SUMS`, `JOIN`): all subset sums of the first half of `W`, the subset
sums of the second half sorted, and a binary search for `T - a` for each sum `a ≤ T` of the first
half. -/
def existsSubsetSum (W : List ℕ) (T : ℕ) : Bool :=
  let h := W.length / 2
  let sb := (allSums (W.drop h)).mergeSort (fun a b => decide (a ≤ b))
  (allSums (W.take h)).any fun a => decide (a ≤ T) && bsearch sb (T - a)

/-- `existsSubsetSum` decides the subset-sum problem exactly (paper §5.7; pseudocode `MITM`):
`existsSubsetSum W T = true ↔ IsSubsetSum W T`. -/
theorem existsSubsetSum_iff (W : List ℕ) (T : ℕ) : existsSubsetSum W T = true ↔ IsSubsetSum W T := by
  have hsort : ((allSums (W.drop (W.length / 2))).mergeSort
      (fun a b => decide (a ≤ b))).toList.Pairwise (· ≤ ·) := by
    have := Array.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega)
      (xs := allSums (W.drop (W.length / 2)))
    simpa using this
  have hW : IsSubsetSum W T ↔ IsSubsetSum (W.take (W.length / 2) ++ W.drop (W.length / 2)) T := by
    rw [List.take_append_drop]
  rw [hW, isSubsetSum_append]
  simp only [existsSubsetSum, Array.any_eq_true', Bool.and_eq_true, decide_eq_true_eq,
    bsearch_iff _ _ hsort, Array.mem_mergeSort, mem_allSums, isSubsetSum_iff_sublist]
  constructor
  · rintro ⟨a, ⟨L₁, h₁, rfl⟩, hle, L₂, h₂, h₂s⟩
    exact ⟨_, _, ⟨L₁, h₁, rfl⟩, ⟨L₂, h₂, h₂s⟩, by omega⟩
  · rintro ⟨_, _, ⟨L₁, h₁, rfl⟩, ⟨L₂, h₂, rfl⟩, hT⟩
    exact ⟨L₁.sum, ⟨L₁, h₁, rfl⟩, by omega, L₂, h₂, by omega⟩

/-! ### The certificate `(-3, -3)` -/

/-- The exhaustive NO certificate `(-3, -3)` is valid when the exact search finds no subset with
sum `T` (paper §5.7, *Parameters derived from the instance*; pseudocode `ARCS`, line 29). -/
def checkExhaustiveNo (W : List ℕ) (T : ℕ) : Bool := !existsSubsetSum W T

/-- Soundness of the exhaustive NO certificate (paper §5.7, *Parameters derived from the
instance*; pseudocode `ARCS`, line 29): if `checkExhaustiveNo` accepts, then `T` is not a subset
sum. -/
theorem checkExhaustiveNo_sound {W : List ℕ} {T : ℕ} (h : checkExhaustiveNo W T = true) :
    ¬ IsSubsetSum W T := by
  rw [← existsSubsetSum_iff]
  simpa [checkExhaustiveNo] using h

/-- The exhaustive certificate is accepted exactly on the NO instances (paper §5.7; pseudocode
`ARCS`, line 29): `checkExhaustiveNo W T = true ↔ ¬ IsSubsetSum W T`. -/
theorem checkExhaustiveNo_iff (W : List ℕ) (T : ℕ) :
    checkExhaustiveNo W T = true ↔ ¬ IsSubsetSum W T := by
  rw [← existsSubsetSum_iff]
  simp [checkExhaustiveNo]

end ArcsAlgo
