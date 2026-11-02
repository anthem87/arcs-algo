module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
set_option autoImplicit false

/-!
# Certified checker for the answers of ARCS

Model: the weights are a list `W : List ℕ` and the target is `T : ℕ`. A subset is a set of
distinct indices into `W`; its sum is the sum of the weights at those indices.

* `checkYes`: a YES answer, given by a list of distinct indices whose weights sum to `T`;
* `reachableMod`: the table of residues mod `q` reachable by subset sums, built exactly as in the
  Python checker (start from `{0}`; for each weight `w`, mark `c` if `c` or `c - w (mod q)` was
  marked);
* `checkNo`: a NO certificate `(q, c)` with `q > 0` is valid when `T % q = c` and `c` is not
  reachable mod `q`;
* `checkRange`: the interval certificate `(q, c) = (0, 0)` is valid when `T > Σ W`.

Soundness: a certificate accepted by `checkYes` proves that `T` is a subset sum, and a
certificate accepted by `checkNo` or `checkRange` proves that it is not. With these, every
answer of the solver and of the benchmarks can be checked by a verified program, independently of
how the solver found it.
-/

@[expose] public section

namespace ArcsAlgo

open Finset

/-- `T` is a subset sum of `W`: some set of distinct indices into `W` has weights summing to `T`.
This is the subset-sum problem answered by ARCS (paper §5.2, Guarantees of the pseudocode). -/
def IsSubsetSum (W : List ℕ) (T : ℕ) : Prop :=
  ∃ s : Finset (Fin W.length), ∑ i ∈ s, W.get i = T

/-! ### Structural lemmas on `IsSubsetSum` -/

/-- Over the empty list the only subset sum is `0` (base case of the subset-sum predicate). -/
theorem isSubsetSum_nil {T : ℕ} : IsSubsetSum [] T ↔ T = 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
  · rintro rfl
    exact ⟨∅, by simp⟩

/-- Splitting a subset of the indices of `a :: W` into the part with index `0` and the rest
(auxiliary for the subset-sum predicate). -/
private theorem sum_cons_split (a : ℕ) (W : List ℕ) (s : Finset (Fin (W.length + 1))) :
    ∑ i ∈ s, (a :: W).get i =
      (if (0 : Fin (W.length + 1)) ∈ s then a else 0) +
        ∑ i ∈ s.preimage Fin.succ (Fin.succ_injective _).injOn, W.get i := by
  have h1 : ∀ {m : ℕ} (t : Finset (Fin m)) (f : Fin m → ℕ),
      ∑ i ∈ t, f i = ∑ i, if i ∈ t then f i else 0 := fun t f => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h1 (s.preimage _ _), Fin.sum_univ_succ]
  simp [Finset.mem_preimage]

/-- The recursion of the subset-sum predicate on the first weight: a subset of
`a :: W` either omits `a` or takes it. -/
theorem isSubsetSum_cons {a : ℕ} {W : List ℕ} {T : ℕ} :
    IsSubsetSum (a :: W) T ↔ IsSubsetSum W T ∨ ∃ T', IsSubsetSum W T' ∧ T = a + T' := by
  constructor
  · rintro ⟨s, hs⟩
    have := (sum_cons_split a W s).symm.trans hs
    split_ifs at this
    · exact Or.inr ⟨_, ⟨_, rfl⟩, this.symm⟩
    · exact Or.inl ⟨_, (zero_add _).symm.trans this⟩
  · rintro (⟨s, rfl⟩ | ⟨_, ⟨s, rfl⟩, rfl⟩)
    · refine ⟨s.map (Fin.succEmb _), ?_⟩
      rw [Finset.sum_map]
      simp
    · refine ⟨insert 0 (s.map (Fin.succEmb _)), ?_⟩
      rw [Finset.sum_insert (by simp [Fin.succ_ne_zero]), Finset.sum_map]
      simp

/-- The subset-sum predicate, phrased with sublists: `T` is a subset sum of
`W` iff some sublist of `W` sums to `T`. -/
theorem isSubsetSum_iff_sublist {W : List ℕ} {T : ℕ} :
    IsSubsetSum W T ↔ ∃ L : List ℕ, L.Sublist W ∧ L.sum = T := by
  induction W generalizing T with
  | nil => simp [isSubsetSum_nil, eq_comm]
  | cons a W ih =>
    rw [isSubsetSum_cons]
    simp only [ih, List.sublist_cons_iff]
    constructor
    · rintro (⟨L, hL, rfl⟩ | ⟨_, ⟨L, hL, rfl⟩, rfl⟩)
      · exact ⟨L, Or.inl hL, rfl⟩
      · exact ⟨a :: L, Or.inr ⟨L, rfl, hL⟩, by simp⟩
    · rintro ⟨L, hL | ⟨r, rfl, hr⟩, rfl⟩
      · exact Or.inl ⟨L, hL, rfl⟩
      · exact Or.inr ⟨_, ⟨r, hr, rfl⟩, by simp⟩

/-- Every subset sum is at most the total weight (used for the interval certificate `(0, 0)`,
paper §5.2; pseudocode `ARCS` line 12 (`ARCS-FIXED` lines 3–4)). -/
theorem le_sum_of_isSubsetSum {W : List ℕ} {T : ℕ} (h : IsSubsetSum W T) : T ≤ W.sum := by
  obtain ⟨L, hL, rfl⟩ := isSubsetSum_iff_sublist.1 h
  exact hL.sum_le_sum (fun _ _ => Nat.zero_le _)

/-! ### YES answers -/

/-- A YES certificate: `idx` has no repetitions, every index is `< W.length`, and the weights at
those indices sum to `T`. -/
def checkYes (W : List ℕ) (T : ℕ) (idx : List ℕ) : Bool :=
  decide idx.Nodup && idx.all (· < W.length) && (idx.map fun i => W.getD i 0).sum == T

/-- The weights at a list of in-range indices, read through `Fin` or through `getD`, have the
same sum (auxiliary for YES answers, paper §5.2, Guarantees of the pseudocode). -/
private theorem sum_pmap_get (W : List ℕ) :
    ∀ (idx : List ℕ) (H : ∀ i ∈ idx, i < W.length),
      ((idx.pmap Fin.mk H).map W.get).sum = (idx.map fun i => W.getD i 0).sum
  | [], _ => rfl
  | i :: idx, H => by
    simp only [List.pmap_cons, List.map_cons, List.sum_cons]
    rw [sum_pmap_get W idx]
    simp [List.getElem?_eq_getElem (H i List.mem_cons_self)]

/-- Soundness of YES answers (paper §5.2, Guarantees of the pseudocode: every YES can be
checked):
a list of indices accepted by `checkYes` is a subset with sum `T`. -/
theorem checkYes_sound {W : List ℕ} {T : ℕ} {idx : List ℕ} (h : checkYes W T idx = true) :
    IsSubsetSum W T := by
  simp only [checkYes, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hnd, hall⟩, hsum⟩ := h
  have hall' : ∀ i ∈ idx, i < W.length := fun i hi => by simpa using hall i hi
  refine ⟨(idx.pmap Fin.mk hall').toFinset, ?_⟩
  have hnd' : (idx.pmap Fin.mk hall').Nodup :=
    hnd.pmap (fun _ _ _ _ h => Fin.mk.inj_iff.1 h)
  rw [List.sum_toFinset _ hnd', sum_pmap_get, hsum]

/-! ### The residue table -/

/-- The initial table: only the residue `0` (of the empty subset) is reachable. -/
def initMod (q : ℕ) : Array Bool :=
  Array.ofFn fun c : Fin q => c.val == 0

/-- One step of the table for a weight `w`: residue `c` is reachable iff it was reachable before
or `c - w (mod q)` was. -/
def stepMod (q w : ℕ) (a : Array Bool) : Array Bool :=
  Array.ofFn fun c : Fin q => a[c.val]! || a[(c.val + q - w % q) % q]!

/-- The table of residues mod `q` reachable by subset sums of `W`, built as in the Python
checker. -/
def reachableMod (q : ℕ) (W : List ℕ) : Array Bool :=
  W.foldl (fun a w => stepMod q w a) (initMod q)

/-- One step keeps the table at `q` entries (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
theorem stepMod_size (q w : ℕ) (a : Array Bool) : (stepMod q w a).size = q := by
  simp [stepMod]

/-- The residue table has exactly `q` entries (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
theorem reachableMod_size (q : ℕ) (W : List ℕ) : (reachableMod q W).size = q := by
  unfold reachableMod
  induction W using List.reverseRecOn with
  | nil => simp [initMod]
  | append_singleton W w _ => simp [List.foldl_append, stepMod_size]

/-- The initial table marks only the residue `0` (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
theorem initMod_get {q c : ℕ} (hc : c < q) : (initMod q)[c]! = (c == 0) := by
  rw [getElem!_pos _ _ (by simpa [initMod] using hc)]
  simp [initMod]

/-- Entry `c` after one step: `c` or `c - w (mod q)` was marked (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
theorem stepMod_get {q w c : ℕ} (a : Array Bool) (hc : c < q) :
    (stepMod q w a)[c]! = (a[c]! || a[(c + q - w % q) % q]!) := by
  rw [getElem!_pos _ _ (by simpa [stepMod] using hc)]
  simp [stepMod]

/-- `((r + w) % q + q - w % q) % q = r` for `r < q` (auxiliary for the residue table). -/
private theorem mod_add_sub_mod {q r w : ℕ} (hr : r < q) :
    ((r + w) % q + q - w % q) % q = r := by
  have hq : 0 < q := by omega
  have hy : w % q < q := Nat.mod_lt _ hq
  have h1 : (r + w) % q = (r + w % q) % q := by rw [Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [h1]
  by_cases h : r + w % q < q
  · have hx : (r + w % q) % q = r + w % q := Nat.mod_eq_of_lt h
    rw [hx, show r + w % q + q - w % q = r + q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · have hx : (r + w % q) % q = r + w % q - q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hx, show r + w % q - q + q - w % q = r by omega, Nat.mod_eq_of_lt hr]

/-- Invariant of the fold: if `r` is marked, then `r + Σ L'` is marked after processing `L`, for
every sublist `L'` of `L` (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
private theorem foldl_stepMod_mark {q : ℕ} (hq : 0 < q) :
    ∀ (L : List ℕ) (A : Array Bool) (r : ℕ), r < q → A[r]! = true →
      ∀ L' : List ℕ, L'.Sublist L → (L.foldl (fun a w => stepMod q w a) A)[(r + L'.sum) % q]! = true
  | [], A, r, hr, hA, L', hL' => by
    rw [List.sublist_nil.1 hL']
    simpa [Nat.mod_eq_of_lt hr] using hA
  | w :: L, A, r, hr, hA, L', hL' => by
    rw [List.foldl_cons]
    rcases List.sublist_cons_iff.1 hL' with hL' | ⟨L'', rfl, hL''⟩
    · exact foldl_stepMod_mark hq L _ r hr (by rw [stepMod_get _ hr, hA, Bool.true_or]) L' hL'
    · have h := foldl_stepMod_mark hq L (stepMod q w A) ((r + w) % q) (Nat.mod_lt _ hq)
        (by rw [stepMod_get _ (Nat.mod_lt _ hq), mod_add_sub_mod hr, hA, Bool.or_true]) L'' hL''
      rwa [Nat.mod_add_mod, Nat.add_assoc, ← List.sum_cons] at h

/-- Completeness of the residue table (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)): the
residue of every subset sum is marked. -/
theorem reachableMod_complete {q : ℕ} {W : List ℕ} (hq : 0 < q) :
    ∀ s : Finset (Fin W.length), (reachableMod q W)[(∑ i ∈ s, W.get i) % q]! = true := by
  intro s
  obtain ⟨L, hL, hsum⟩ := isSubsetSum_iff_sublist.1 ⟨s, rfl⟩
  have h := foldl_stepMod_mark hq W (initMod q) 0 hq (by rw [initMod_get hq]; rfl) L hL
  rwa [Nat.zero_add, hsum] at h

/-- Invariant of the fold in the other direction: every marked residue is the residue of a sum of a
sublist of the weights processed so far (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)). -/
private theorem foldl_stepMod_exact {q : ℕ} (hq : 0 < q) :
    ∀ (L M : List ℕ) (A : Array Bool),
      (∀ c < q, A[c]! = true → ∃ L' : List ℕ, L'.Sublist M ∧ L'.sum % q = c) →
      ∀ c < q, (L.foldl (fun a w => stepMod q w a) A)[c]! = true →
        ∃ L' : List ℕ, L'.Sublist (M ++ L) ∧ L'.sum % q = c
  | [], M, A, hA, c, hc, h => by simpa using hA c hc h
  | w :: L, M, A, hA, c, hc, h => by
    rw [List.foldl_cons] at h
    have h' := foldl_stepMod_exact hq L (M ++ [w]) (stepMod q w A) (by
      intro c hc hc'
      rw [stepMod_get _ hc, Bool.or_eq_true] at hc'
      rcases hc' with hc' | hc'
      · obtain ⟨L', hL', hs⟩ := hA c hc hc'
        exact ⟨L', hL'.trans (List.sublist_append_left _ _), hs⟩
      · obtain ⟨L', hL', hs⟩ := hA _ (Nat.mod_lt _ hq) hc'
        refine ⟨L' ++ [w], hL'.append_right _, ?_⟩
        have hy : w % q < q := Nat.mod_lt _ hq
        rw [List.sum_append, List.sum_singleton, Nat.add_mod, hs, Nat.mod_add_mod,
          show c + q - w % q + w % q = c + q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hc])
      c hc h
    simpa using h'

/-- Exactness of the residue table (modular certificates,
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)): a residue
`c < q` is marked iff it is the residue of some subset sum. Only the direction `←`
(`reachableMod_complete`) is needed for the soundness of `checkNo`. -/
theorem reachableMod_exact {q : ℕ} {W : List ℕ} (hq : 0 < q) {c : ℕ} (hc : c < q) :
    (reachableMod q W)[c]! = true ↔ ∃ s : Finset (Fin W.length), (∑ i ∈ s, W.get i) % q = c := by
  constructor
  · intro h
    obtain ⟨L, hL, hs⟩ := foldl_stepMod_exact hq W [] (initMod q) (by
      intro c hc hc'
      rw [initMod_get hc, beq_iff_eq] at hc'
      exact ⟨[], List.nil_sublist _, by simp [hc']⟩) c hc h
    obtain ⟨s, hs'⟩ := isSubsetSum_iff_sublist.2 ⟨L, by simpa using hL, rfl⟩
    exact ⟨s, by rw [hs', hs]⟩
  · rintro ⟨s, rfl⟩
    exact reachableMod_complete hq s

/-! ### NO answers -/

/-- A residue NO certificate `(q, c)`: `q > 0`, `T % q = c`, `c < q`, and `c` is not reachable
mod `q`. -/
def checkNo (W : List ℕ) (T q c : ℕ) : Bool :=
  decide (0 < q) && T % q == c && decide (c < q) && !(reachableMod q W)[c]!

/-- Soundness of residue NO certificates (certificate `(q, c)`;
paper §5.7; pseudocode `ARCS` lines 13–14 (`ARCS-FIXED` lines 5–7)): if `checkNo` accepts
`(q, c)` then `T` is not a subset sum. -/
theorem checkNo_sound {W : List ℕ} {T q c : ℕ} (h : checkNo W T q c = true) :
    ¬ IsSubsetSum W T := by
  simp only [checkNo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hq, hTc⟩, _⟩, hc⟩ := h
  rintro ⟨s, hs⟩
  have := reachableMod_complete (W := W) hq s
  rw [hs, hTc, hc] at this
  exact Bool.false_ne_true this

/-- The interval NO certificate `(q, c) = (0, 0)`: the target exceeds the total weight. (A target
`T < 0` cannot occur in `ℕ`.) -/
def checkRange (W : List ℕ) (T : ℕ) : Bool :=
  decide (W.sum < T)

/-- Soundness of the interval NO certificate (certificate `(0, 0)`;
paper §5.2; pseudocode `ARCS` line 12 (`ARCS-FIXED` lines 3–4)): if `T > Σ W`
then `T` is not a subset sum. -/
theorem checkRange_sound {W : List ℕ} {T : ℕ} (h : checkRange W T = true) :
    ¬ IsSubsetSum W T := by
  simp only [checkRange, decide_eq_true_eq] at h
  exact fun hs => absurd (le_sum_of_isSubsetSum hs) (by omega)

end ArcsAlgo
