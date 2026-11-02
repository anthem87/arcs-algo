module

public import ArcsAlgo.Propagation
set_option autoImplicit false

/-!
# Convergence of the full operator (paper §7.6)

A state `s = (F, D, Cl)` has facts, domains and clusters; the information order is
`s ⪯ s' ⟺ F(s) ⊆ F(s') ∧ ∀v D_{s'}(v) ⊆ D_s(v)`, and the measure is
`ν(s) = |Cl(s)| + Σ_v |D_s(v)|`.

The paper describes the four components of `K = Merge ∘ Unary ∘ Bridge ∘ LocalDed` in words; here
each component is any operator obeying the laws used in the proofs (`Law`): it keeps the facts,
shrinks the domains, keeps the clusters or reduces their number, and is monotone for `⪯`.
`unary_law` and `merge_law` check the laws for concrete `Unary` and `Merge`.

* Lemma 7.11: `K_facts` (L1), `K_domains` (L2), `K_clusters` (L3), `K_measure` (L4),
  `K_mono` (L5), `K_le` (L6).
* Theorem 7.12 (termination): `termination`.
* Theorem 7.13 (closure): `closure`.
* Remark 7.14: `not_maximal`.
-/

@[expose] public section

namespace ArcsAlgo.Convergence

open Finset

variable {V Val Fact : Type*}

/-- A state: facts, domains and clusters. -/
@[ext]
structure St (V Val Fact : Type*) where
  F : Finset Fact
  D : V → Finset Val
  Cl : Finset (Finset V)

/-- The information order `s ⪯ s'`. -/
def Le (s s' : St V Val Fact) : Prop := s.F ⊆ s'.F ∧ ∀ v, s'.D v ⊆ s.D v

/-- The measure `ν(s) = |Cl(s)| + Σ_v |D_s(v)|`. -/
def nu [Fintype V] (s : St V Val Fact) : ℕ := s.Cl.card + ∑ v, (s.D v).card

theorem Le.refl (s : St V Val Fact) : Le s s := ⟨subset_rfl, fun _ => subset_rfl⟩

theorem Le.trans {s t u : St V Val Fact} (h1 : Le s t) (h2 : Le t u) : Le s u :=
  ⟨h1.1.trans h2.1, fun v => (h2.2 v).trans (h1.2 v)⟩

/-- The laws of a component of `K`. -/
structure Law (c : St V Val Fact → St V Val Fact) : Prop where
  facts : ∀ s, (c s).F = s.F
  domains : ∀ s v, (c s).D v ⊆ s.D v
  clusters : ∀ s, (c s).Cl = s.Cl ∨ (c s).Cl.card < s.Cl.card
  mono : ∀ s s', Le s s' → Le (c s) (c s')

theorem Law.comp {c d : St V Val Fact → St V Val Fact} (hc : Law c) (hd : Law d) :
    Law (c ∘ d) := by
  refine ⟨fun s => by simp [hc.facts, hd.facts], fun s v => (hc.domains _ v).trans (hd.domains s v),
    fun s => ?_, fun s s' h => hc.mono _ _ (hd.mono s s' h)⟩
  rcases hd.clusters s with h1 | h1 <;> rcases hc.clusters (d s) with h2 | h2
  · left; simp [h2, h1]
  · right; simp only [Function.comp_apply]; rw [← h1]; exact h2
  · right; simp only [Function.comp_apply, h2]; exact h1
  · right; exact h2.trans h1

section Operator

variable (LocalDed Bridge Unary Merge : St V Val Fact → St V Val Fact)

/-- The full operator `K = Merge ∘ Unary ∘ Bridge ∘ LocalDed`. -/
def K : St V Val Fact → St V Val Fact := Merge ∘ Unary ∘ Bridge ∘ LocalDed

variable {LocalDed Bridge Unary Merge}
variable (hL : Law LocalDed) (hB : Law Bridge) (hU : Law Unary) (hM : Law Merge)
include hL hB hU hM

theorem K_law : Law (K LocalDed Bridge Unary Merge) := hM.comp (hU.comp (hB.comp hL))

/-- **Lemma 7.11, L1** (paper §7.6): `F(K s) = F(s)`. -/
theorem K_facts (s : St V Val Fact) : (K LocalDed Bridge Unary Merge s).F = s.F :=
  (K_law hL hB hU hM).facts s

/-- **Lemma 7.11, L2** (paper §7.6): `D_{K s}(v) ⊆ D_s(v)`. -/
theorem K_domains (s : St V Val Fact) (v : V) : (K LocalDed Bridge Unary Merge s).D v ⊆ s.D v :=
  (K_law hL hB hU hM).domains s v

/-- **Lemma 7.11, L3** (paper §7.6): `Cl(K s) = Cl(s)` or `|Cl(K s)| < |Cl(s)|`. -/
theorem K_clusters (s : St V Val Fact) :
    (K LocalDed Bridge Unary Merge s).Cl = s.Cl ∨
      (K LocalDed Bridge Unary Merge s).Cl.card < s.Cl.card :=
  (K_law hL hB hU hM).clusters s

/-- **Lemma 7.11, L4** (paper §7.6): `K(s) ≠ s → ν(K s) < ν(s)`. -/
theorem K_measure [Fintype V] (s : St V Val Fact) (h : K LocalDed Bridge Unary Merge s ≠ s) :
    nu (K LocalDed Bridge Unary Merge s) < nu s := by
  have hC0 := K_clusters hL hB hU hM s
  set t := K LocalDed Bridge Unary Merge s
  have hF := K_facts hL hB hU hM s
  have hD := K_domains hL hB hU hM s
  have hsum : ∑ v, (t.D v).card ≤ ∑ v, (s.D v).card :=
    Finset.sum_le_sum fun v _ => card_le_card (hD v)
  unfold nu
  rcases hC0 with hC | hC
  · have hDne : t.D ≠ s.D := by
      intro hDe; exact h (St.ext hF hDe hC)
    obtain ⟨v, hv⟩ : ∃ v, t.D v ≠ s.D v := by
      by_contra hc; push Not at hc; exact hDne (funext hc)
    have hlt : ∑ v, (t.D v).card < ∑ v, (s.D v).card :=
      Finset.sum_lt_sum (fun u _ => card_le_card (hD u))
        ⟨v, mem_univ _, card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hD v, hv⟩)⟩
    rw [hC]; omega
  · omega

/-- **Lemma 7.11, L5** (paper §7.6): `s ⪯ s' → K(s) ⪯ K(s')`. -/
theorem K_mono {s s' : St V Val Fact} (h : Le s s') :
    Le (K LocalDed Bridge Unary Merge s) (K LocalDed Bridge Unary Merge s') :=
  (K_law hL hB hU hM).mono s s' h

/-- **Lemma 7.11, L6** (paper §7.6): `s ⪯ K(s)`. -/
theorem K_le (s : St V Val Fact) : Le s (K LocalDed Bridge Unary Merge s) :=
  ⟨(K_facts hL hB hU hM s).ge, K_domains hL hB hU hM s⟩

/-- **Theorem 7.12 (termination)** (paper §7.6): `∀s₀ ∃n ≤ ν(s₀) ∀m ≥ n, Kᵐ(s₀) = Kⁿ(s₀)`. -/
theorem termination [Fintype V] (s₀ : St V Val Fact) :
    ∃ n ≤ nu s₀, ∀ m ≥ n, (K LocalDed Bridge Unary Merge)^[m] s₀ =
      (K LocalDed Bridge Unary Merge)^[n] s₀ :=
  ⟨nu s₀, le_rfl, Propagation.iterate_stable_of_potential _ (fun _ => True) nu (fun _ _ => trivial)
    (fun s _ hne => K_measure hL hB hU hM s hne) s₀ trivial⟩

/-- **Theorem 7.13 (closure)** (paper §7.6): with `s* = Kⁿ(s₀)`, `n = ν(s₀)`: `s*` is a
fixpoint, `s₀ ⪯ s*`, and `s* ⪯ s'` for every fixpoint `s'` above `s₀`. -/
theorem closure [Fintype V] (s₀ : St V Val Fact) :
    let sStar := (K LocalDed Bridge Unary Merge)^[nu s₀] s₀
    K LocalDed Bridge Unary Merge sStar = sStar ∧ Le s₀ sStar ∧
      ∀ s', K LocalDed Bridge Unary Merge s' = s' → Le s₀ s' → Le sStar s' := by
  intro sStar
  have hstab := Propagation.iterate_stable_of_potential (K LocalDed Bridge Unary Merge)
    (fun _ => True) nu (fun _ _ => trivial) (fun s _ hne => K_measure hL hB hU hM s hne) s₀ trivial
  refine ⟨?_, ?_, ?_⟩
  · have := hstab (nu s₀ + 1) (by omega)
    rwa [Function.iterate_succ_apply'] at this
  · have : ∀ k, Le s₀ ((K LocalDed Bridge Unary Merge)^[k] s₀) := by
      intro k
      induction k with
      | zero => exact Le.refl _
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (K_le hL hB hU hM _)
    exact this _
  · intro s' hfix hle
    have : ∀ k, Le ((K LocalDed Bridge Unary Merge)^[k] s₀) s' := by
      intro k
      induction k with
      | zero => exact hle
      | succ k ih =>
        rw [Function.iterate_succ_apply', ← hfix]
        exact K_mono hL hB hU hM ih
    exact this _

end Operator

/-- **Remark 7.14 (a maximality statement that fails)** (paper §7.6): the fixpoint reached is
not maximal in general. With one variable of domain `{0, 1}`, no constraints and no facts, `K`
is the identity, the start state is the fixpoint reached, and the state with domain `{0}` and
the fact `(t, g, 0)` is a fixpoint above it but not below it. -/
theorem not_maximal :
    let s₀ : St Unit ℕ (Unit × Unit × ℕ) := ⟨∅, fun _ => {0, 1}, ∅⟩
    let s' : St Unit ℕ (Unit × Unit × ℕ) := ⟨{((), (), 0)}, fun _ => {0}, ∅⟩
    (id s' = s') ∧ Le s₀ s' ∧ ¬ Le s' s₀ := by
  intro s₀ s'
  refine ⟨rfl, ⟨by simp [s₀], fun _ => by simp [s₀, s']⟩, fun h => ?_⟩
  have := h.1 (show ((), (), 0) ∈ s'.F by simp [s'])
  simp [s₀] at this

/-! ### Concrete components -/

/-- `Unary`: intersect every domain with its unary constraint. -/
theorem unary_law [DecidableEq Val] (u : V → Finset Val) :
    Law fun s : St V Val Fact => ⟨s.F, fun v => s.D v ∩ u v, s.Cl⟩ := by
  refine ⟨fun _ => rfl, fun s v => inter_subset_left, fun _ => Or.inl rfl, ?_⟩
  intro s s' h
  exact ⟨h.1, fun v => inter_subset_inter (h.2 v) subset_rfl⟩

/-- One merging step: if two distinct clusters overlap, replace them by their union. -/
noncomputable def mergeStep (Cl : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact if h : ∃ a ∈ Cl, ∃ b ∈ Cl, a ≠ b ∧ (a ∩ b).Nonempty then
    insert (h.choose ∪ h.choose_spec.2.choose) ((Cl.erase h.choose).erase h.choose_spec.2.choose)
  else Cl

theorem mergeStep_card (Cl : Finset (Finset V)) :
    mergeStep Cl = Cl ∨ (mergeStep Cl).card < Cl.card := by
  classical
  unfold mergeStep
  split_ifs with h
  · right
    obtain ⟨ha, b, hb, hab, _⟩ := h.choose_spec
    have hb' := h.choose_spec.2.choose_spec
    calc _ ≤ ((Cl.erase h.choose).erase h.choose_spec.2.choose).card + 1 :=
          card_insert_le _ _
      _ = Cl.card - 1 - 1 + 1 := by
          rw [card_erase_of_mem (mem_erase.2 ⟨hb'.2.1.symm, hb'.1⟩), card_erase_of_mem ha]
      _ < Cl.card := by
          have : 2 ≤ Cl.card := by
            have h2 : ({h.choose, h.choose_spec.2.choose} : Finset (Finset V)) ⊆ Cl := by
              intro x hx; simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact ha
              · exact hb'.1
            have := card_le_card h2
            rwa [card_pair hb'.2.1] at this
          omega
  · left; rfl

/-- `Merge`: merging overlapping clusters, `k` steps (L3 by induction on the merging loop). -/
noncomputable def merge (k : ℕ) (Cl : Finset (Finset V)) : Finset (Finset V) := mergeStep^[k] Cl

theorem merge_card (k : ℕ) (Cl : Finset (Finset V)) :
    merge k Cl = Cl ∨ (merge k Cl).card < Cl.card := by
  induction k generalizing Cl with
  | zero => left; rfl
  | succ k ih =>
    simp only [merge, Function.iterate_succ_apply]
    rcases mergeStep_card Cl with h | h
    · rw [h]; exact ih Cl
    · right
      rcases ih (mergeStep Cl) with h' | h'
      · simp only [merge] at h'; rw [h']; exact h
      · exact h'.trans h

theorem merge_law (k : ℕ) : Law fun s : St V Val Fact => ⟨s.F, s.D, merge k s.Cl⟩ :=
  ⟨fun _ => rfl, fun _ _ => subset_rfl, fun s => merge_card k s.Cl, fun _ _ h => h⟩

end ArcsAlgo.Convergence
