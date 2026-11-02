module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.NNRat.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Basic
set_option autoImplicit false

/-!
# Constraint propagation: the computational part (paper §7.1, §7.3)

Variables `V` and values `Val` are finite. Domains are `W : V → Finset Val`, ordered pointwise
(`W' ≤ W` is `W' ⊑ W`). A constraint has a scope `vars` and a relation `sat` on total
assignments.

* `proj c W v`: the projection `π_v(c, W)`; `filter c W`: the generalized arc consistency
  filter `T_c`; `defect c W`: the support defect `υ(c, W)`.
* `Tcomp cs`: one round of the filters of `cs`, in the order of the list.
* Theorem 7.4: (i) `Tcomp_le`, `Tcomp_mono`; (ii) `Tcomp_eq_self_iff`; (iii) `Tfail_stable`
  (corrected: `μ(W) + 1` rounds, the empty domain absorbing; `Tcomp_bound_counterexample`
  shows that `μ(W)` rounds do not suffice); (iv) `limit_greatest`, `limit_perm`,
  `schedule_eq_limit`.
-/

@[expose] public section

namespace ArcsAlgo.Propagation

open Finset

variable {V Val : Type*} [Fintype V] [DecidableEq V] [Fintype Val] [DecidableEq Val]

/-- A constraint: a scope and a relation on assignments (paper §7.1). -/
structure Constraint (V Val : Type*) where
  vars : Finset V
  sat : (V → Val) → Bool

/-- Domains `W : V → 𝒫(Val)`; the pointwise order is the order `⊑` of paper §7.1. -/
abbrev Dom (V Val : Type*) := V → Finset Val

/-- An assignment supported by `W` on the scope of `c`. -/
def Supports (c : Constraint V Val) (W : Dom V Val) (α : V → Val) : Prop :=
  c.sat α = true ∧ ∀ u ∈ c.vars, α u ∈ W u

instance (c : Constraint V Val) (W : Dom V Val) (α : V → Val) : Decidable (Supports c W α) := by
  unfold Supports; infer_instance

/-- The projection `π_v(c, W) = {a ∈ W(v) | ∃α, α(v) = a ∧ c(α) ∧ ∀u ∈ vars(c), α(u) ∈ W(u)}`
(paper §7.1). -/
def proj (c : Constraint V Val) (W : Dom V Val) (v : V) : Finset Val :=
  (W v).filter fun a => ∃ α : V → Val, α v = a ∧ Supports c W α

/-- The generalized arc consistency filter `T_c(W)(v) = π_v(c, W)` on the scope of `c`
(paper §7.1). -/
def filter (c : Constraint V Val) (W : Dom V Val) : Dom V Val :=
  fun v => if v ∈ c.vars then proj c W v else W v

/-- The support defect `υ(c, W) = max_v |W(v) ∖ π_v(c, W)| / |W(v)|` (paper §7.1). -/
def defect (c : Constraint V Val) (W : Dom V Val) : ℚ≥0 :=
  c.vars.sup fun v => ((W v \ proj c W v).card : ℚ≥0) / (W v).card

/-- One round of the filters of `cs`, in the order of the list: `T_comp` (paper §7.3). -/
def Tcomp (cs : List (Constraint V Val)) (W : Dom V Val) : Dom V Val :=
  cs.foldl (fun W c => filter c W) W

theorem proj_subset (c : Constraint V Val) (W : Dom V Val) (v : V) : proj c W v ⊆ W v :=
  filter_subset _ _

theorem proj_mono (c : Constraint V Val) {W W' : Dom V Val} (h : W ≤ W') (v : V) :
    proj c W v ⊆ proj c W' v := by
  intro a ha
  simp only [proj, mem_filter] at ha ⊢
  obtain ⟨haW, α, hαv, hsat, hα⟩ := ha
  exact ⟨h v haW, α, hαv, hsat, fun u hu => h u (hα u hu)⟩

theorem filter_le (c : Constraint V Val) (W : Dom V Val) : filter c W ≤ W := by
  intro v
  simp only [filter]
  split_ifs
  · exact proj_subset c W v
  · exact le_rfl

theorem filter_mono (c : Constraint V Val) {W W' : Dom V Val} (h : W ≤ W') :
    filter c W ≤ filter c W' := by
  intro v
  simp only [filter]
  split_ifs
  · exact proj_mono c h v
  · exact h v

/-- `c` is supported in `W`: every value of every variable of its scope has a support. -/
def Supported (c : Constraint V Val) (W : Dom V Val) : Prop := ∀ v ∈ c.vars, proj c W v = W v

theorem filter_eq_self_iff (c : Constraint V Val) (W : Dom V Val) :
    filter c W = W ↔ Supported c W := by
  constructor
  · intro h v hv
    have := congrFun h v
    simpa [filter, hv] using this
  · intro h
    funext v
    simp only [filter]
    split_ifs with hv
    · exact h v hv
    · rfl

theorem defect_eq_zero_iff (c : Constraint V Val) (W : Dom V Val) :
    defect c W = 0 ↔ Supported c W := by
  have hb : (⊥ : ℚ≥0) = 0 := bot_eq_zero
  unfold defect Supported
  rw [← hb, Finset.sup_eq_bot_iff, hb]
  apply forall₂_congr
  intro v _
  rw [div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero, card_eq_zero, card_eq_zero,
    sdiff_eq_empty_iff_subset]
  constructor
  · rintro (h1 | h1)
    · exact Subset.antisymm (proj_subset c W v) h1
    · rw [h1]; exact Subset.antisymm (by rw [← h1]; exact proj_subset c W v) (by simp)
  · intro h
    exact Or.inl h.ge

/-- **Theorem 7.4 (i)** (paper §7.3): `T_comp` is decreasing, `T_comp(W) ⊑ W`. -/
theorem Tcomp_le (cs : List (Constraint V Val)) (W : Dom V Val) : Tcomp cs W ≤ W := by
  induction cs generalizing W with
  | nil => exact le_rfl
  | cons c cs ih => exact (ih (filter c W)).trans (filter_le c W)

/-- **Theorem 7.4 (i)** (paper §7.3): `T_comp` is monotone, `W ⊑ W' → T_comp(W) ⊑ T_comp(W')`. -/
theorem Tcomp_mono (cs : List (Constraint V Val)) {W W' : Dom V Val} (h : W ≤ W') :
    Tcomp cs W ≤ Tcomp cs W' := by
  induction cs generalizing W W' with
  | nil => exact h
  | cons c cs ih => exact ih (filter_mono c h)

/-- **Theorem 7.4 (ii)** (paper §7.3): `T_comp(W) = W` iff `υ(c, W) = 0` for every constraint. -/
theorem Tcomp_eq_self_iff (cs : List (Constraint V Val)) (W : Dom V Val) :
    Tcomp cs W = W ↔ ∀ c ∈ cs, defect c W = 0 := by
  simp only [defect_eq_zero_iff]
  induction cs with
  | nil => simp [Tcomp]
  | cons c cs ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have h' : Tcomp cs (filter c W) = W := h
      have h1 : filter c W = W :=
        le_antisymm (filter_le c W) (h'.symm.le.trans (Tcomp_le cs (filter c W)))
      have h2 : Tcomp cs W = W := by
        have : Tcomp (c :: cs) W = Tcomp cs (filter c W) := rfl
        rwa [this, h1] at h
      exact ⟨(filter_eq_self_iff c W).1 h1, ih.1 h2⟩
    · rintro ⟨h1, h2⟩
      have : Tcomp (c :: cs) W = Tcomp cs (filter c W) := rfl
      rw [this, (filter_eq_self_iff c W).2 h1, ih.2 h2]

/-! ### Stabilization under a decreasing potential -/

theorem iterate_stable_of_potential {α : Type*} (f : α → α) (P : α → Prop) (Φ : α → ℕ)
    (hP : ∀ x, P x → P (f x)) (hΦ : ∀ x, P x → f x ≠ x → Φ (f x) < Φ x) :
    ∀ x, P x → ∀ m ≥ Φ x, f^[m] x = f^[Φ x] x := by
  have key : ∀ n x, P x → Φ x ≤ n → f (f^[n] x) = f^[n] x := by
    intro n
    induction n with
    | zero =>
      intro x hx h0
      simp only [Function.iterate_zero, id_eq]
      by_contra hne
      have := hΦ x hx hne
      omega
    | succ n ih =>
      intro x hx hn
      by_cases hfx : f x = x
      · have : ∀ k, f^[k] x = x := fun k => Function.iterate_fixed hfx k
        rw [this, hfx]
      · have := hΦ x hx hfx
        rw [Function.iterate_succ_apply]
        exact ih (f x) (hP x hx) (by omega)
  intro x hx m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, Function.iterate_succ_apply', ih (by omega)]
    exact key _ x hx le_rfl

/-! ### Theorem 7.4 (iii) -/

/-- The measure `μ(W) = Σ_v (|W(v)| − 1)` (paper Theorem 7.4 (iii)). -/
def mu (W : Dom V Val) : ℕ := ∑ v, ((W v).card - 1)

/-- The total size `Σ_v |W(v)|`. -/
def size (W : Dom V Val) : ℕ := ∑ v, (W v).card

/-- The failure state: every domain empty. -/
def failure : Dom V Val := fun _ => ∅

/-- One round of `T_comp` with the empty domain counted as failure (absorbing). -/
def Tfail (cs : List (Constraint V Val)) (W : Dom V Val) : Dom V Val :=
  if ∃ v, Tcomp cs W v = ∅ then failure else Tcomp cs W

omit [DecidableEq V] [Fintype Val] in
theorem size_lt_of_lt {W W' : Dom V Val} (hle : W' ≤ W) (hne : W' ≠ W) : size W' < size W := by
  obtain ⟨v, hv⟩ : ∃ v, W' v ≠ W v := by
    by_contra h; push Not at h; exact hne (funext h)
  have hs : W' v ⊂ W v := Finset.ssubset_iff_subset_ne.2 ⟨hle v, hv⟩
  exact Finset.sum_lt_sum (fun u _ => card_le_card (hle u)) ⟨v, mem_univ _, card_lt_card hs⟩

omit [DecidableEq V] [Fintype Val] in
theorem mu_lt_of_lt {W W' : Dom V Val} (hle : W' ≤ W) (hne : W' ≠ W)
    (hpos : ∀ v, (W' v).Nonempty) : mu W' < mu W := by
  obtain ⟨v, hv⟩ : ∃ v, W' v ≠ W v := by
    by_contra h; push Not at h; exact hne (funext h)
  have hs : (W' v).card < (W v).card :=
    card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hle v, hv⟩)
  have h1 := (hpos v).card_pos
  refine Finset.sum_lt_sum (fun u _ => Nat.sub_le_sub_right (card_le_card (hle u)) 1)
    ⟨v, mem_univ _, by omega⟩

theorem Tcomp_failure (cs : List (Constraint V Val)) : Tcomp cs (failure : Dom V Val) = failure :=
  le_antisymm (Tcomp_le cs _) (fun _ => by simp [failure])

/-- **Theorem 7.4 (iii)** (paper §7.3): with the empty domain counted as failure,
`T^m(W) = T^{μ(W)+1}(W)` for every `m ≥ μ(W) + 1`, when every domain of `W` is non-empty. The
extra step is the one that empties a domain (`Tcomp_bound_counterexample`). -/
theorem Tfail_stable (cs : List (Constraint V Val)) (W : Dom V Val) (hW : ∀ v, (W v).Nonempty) :
    ∀ m ≥ mu W + 1, (Tfail cs)^[m] W = (Tfail cs)^[mu W + 1] W := by
  let P : Dom V Val → Prop := fun W => W = failure ∨ ∀ v, (W v).Nonempty
  let Φ : Dom V Val → ℕ := fun W => if ∃ v, W v = ∅ then 0 else mu W + 1
  have hP : ∀ W, P W → P (Tfail cs W) := by
    intro W _
    unfold Tfail
    split_ifs with h
    · exact Or.inl rfl
    · push Not at h; exact Or.inr h
  have hΦ : ∀ W, P W → Tfail cs W ≠ W → Φ (Tfail cs W) < Φ W := by
    intro W hPW hne
    rcases hPW with rfl | hpos
    · exact absurd (by simp [Tfail, Tcomp_failure, failure]) hne
    · have hW0 : ¬ ∃ v, W v = ∅ := fun ⟨v, hv⟩ => by simpa [hv] using hpos v
      simp only [Φ, hW0, ite_false]
      unfold Tfail at hne ⊢
      by_cases h : ∃ v, Tcomp cs W v = ∅
      · obtain ⟨v, _⟩ := h
        have hf : ∃ u, (failure : Dom V Val) u = ∅ := ⟨v, rfl⟩
        simp only [show ∃ v, Tcomp cs W v = ∅ from ⟨v, by assumption⟩, ite_true, hf]
        omega
      · have hpos' : ∀ v, (Tcomp cs W v).Nonempty := by push Not at h; exact h
        simp only [h, ite_false] at hne ⊢
        have := mu_lt_of_lt (Tcomp_le cs W) hne hpos'
        omega
  have hPW : P W := Or.inr hW
  have hΦW : Φ W = mu W + 1 := by
    have : ¬ ∃ v, W v = ∅ := fun ⟨v, hv⟩ => by simpa [hv] using hW v
    simp [Φ, this]
  intro m hm
  have := iterate_stable_of_potential (Tfail cs) P Φ hP hΦ W hPW m (by omega)
  rwa [hΦW] at this

/-- The example of Theorem 7.4 (iii) (paper §7.3): one Boolean variable with domain `{false}` and
the assertion "it is `true`" have `μ(W) = 0`, but one round of `T_comp` empties the domain, so
`μ(W)` rounds are not enough and `μ(W) + 1` are needed. -/
theorem Tcomp_bound_counterexample :
    let c : Constraint Unit Bool := ⟨{()}, fun α => α ()⟩
    let W : Dom Unit Bool := fun _ => {false}
    mu W = 0 ∧ Tcomp [c] W ≠ W := by
  intro c W
  refine ⟨by decide, fun h => ?_⟩
  have := congrFun h ()
  revert this
  decide

/-! ### Theorem 7.4 (iv) -/

/-- The limit `W*` of the rounds of `T_comp` from `W`. -/
def limit (cs : List (Constraint V Val)) (W : Dom V Val) : Dom V Val := (Tcomp cs)^[size W] W

theorem limit_stable (cs : List (Constraint V Val)) (W : Dom V Val) :
    ∀ m ≥ size W, (Tcomp cs)^[m] W = limit cs W :=
  iterate_stable_of_potential (Tcomp cs) (fun _ => True) size (fun _ _ => trivial)
    (fun W _ hne => size_lt_of_lt (Tcomp_le cs W) hne) W trivial

theorem limit_fixed (cs : List (Constraint V Val)) (W : Dom V Val) :
    Tcomp cs (limit cs W) = limit cs W := by
  have := limit_stable cs W (size W + 1) (by omega)
  rwa [Function.iterate_succ_apply'] at this

theorem iterate_le (cs : List (Constraint V Val)) (W : Dom V Val) (n : ℕ) :
    (Tcomp cs)^[n] W ≤ W := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (Tcomp_le cs _).trans ih

theorem limit_le (cs : List (Constraint V Val)) (W : Dom V Val) : limit cs W ≤ W :=
  iterate_le cs W _

/-- **Theorem 7.4 (iv)** (paper §7.3): the limit `W*` is the largest `W' ⊑ W` with
`υ(c, W') = 0` for every `c`. -/
theorem limit_greatest (cs : List (Constraint V Val)) (W W' : Dom V Val) (hle : W' ≤ W)
    (hW' : ∀ c ∈ cs, defect c W' = 0) : W' ≤ limit cs W := by
  have hfix : Tcomp cs W' = W' := (Tcomp_eq_self_iff cs W').2 hW'
  have : ∀ n, W' ≤ (Tcomp cs)^[n] W := by
    intro n
    induction n with
    | zero => exact hle
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← hfix]
      exact Tcomp_mono cs ih
  exact this _

theorem limit_supported (cs : List (Constraint V Val)) (W : Dom V Val) :
    ∀ c ∈ cs, defect c (limit cs W) = 0 :=
  (Tcomp_eq_self_iff cs _).1 (limit_fixed cs W)

/-- **Theorem 7.4 (iv), independence of the order** (paper §7.3): the limit does not depend on
the order of the filters. -/
theorem limit_perm {cs cs' : List (Constraint V Val)} (h : cs.Perm cs') (W : Dom V Val) :
    limit cs W = limit cs' W := by
  apply le_antisymm
  · exact limit_greatest cs' W _ (limit_le cs W)
      (fun c hc => limit_supported cs W c (h.mem_iff.2 hc))
  · exact limit_greatest cs W _ (limit_le cs' W)
      (fun c hc => limit_supported cs' W c (h.mem_iff.1 hc))

/-- Applying the filters of `cs` one at a time in any order (a schedule) never goes below `W*`. -/
theorem limit_le_schedule (cs : List (Constraint V Val)) (W : Dom V Val)
    (sched : List (Constraint V Val)) (hs : ∀ c ∈ sched, c ∈ cs) :
    limit cs W ≤ sched.foldl (fun W c => filter c W) W := by
  induction sched using List.reverseRecOn with
  | nil => exact limit_le cs W
  | append_singleton s c ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hc : filter c (limit cs W) = limit cs W :=
      (filter_eq_self_iff c _).2 ((defect_eq_zero_iff c _).1
        (limit_supported cs W c (hs c (by simp))))
    rw [← hc]
    exact filter_mono c (ih fun c' hc' => hs c' (by simp [hc']))

/-- **Theorem 7.4 (iv), chaotic iteration** (paper §7.3, [Apt]): any schedule of the filters of
`cs` that ends in a common fixpoint of all of them ends in `W*`. -/
theorem schedule_eq_limit (cs : List (Constraint V Val)) (W : Dom V Val)
    (sched : List (Constraint V Val)) (hs : ∀ c ∈ sched, c ∈ cs)
    (hfix : ∀ c ∈ cs, defect c (sched.foldl (fun W c => filter c W) W) = 0) :
    sched.foldl (fun W c => filter c W) W = limit cs W := by
  have hle : sched.foldl (fun W c => filter c W) W ≤ W := by
    clear hfix hs
    induction sched using List.reverseRecOn with
    | nil => exact le_rfl
    | append_singleton s c ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (filter_le c _).trans ih
  exact le_antisymm (limit_greatest cs W _ hle hfix) (limit_le_schedule cs W sched hs)

/-! ### Remark 7.5 -/

/-- The chain `x₁ ≠ x₂ ≠ x₃` of Remark 7.5 with `k = 3` (variables `0, 1, 2`), constraints in the
worst order (from the end of the chain). -/
def chainCs : List (Constraint (Fin 3) (Fin 4)) :=
  [⟨{1, 2}, fun α => decide (α 1 ≠ α 2)⟩, ⟨{0, 1}, fun α => decide (α 0 ≠ α 1)⟩]

/-- The domains `D(x₁) = {1}`, `D(x_i) = {i − 1, i}`. -/
def chainW : Dom (Fin 3) (Fin 4) := fun i => if i = 0 then {1} else if i = 1 then {1, 2} else {2, 3}

/-- **Remark 7.5 (a bound of [SC] that fails)** (paper §7.3), for `k = 3`: at `W₀` the only
unsupported value is one of the two values of `x₂` in the constraint `x₁ ≠ x₂` (so
`Σ_c υ(c, W₀)·d = (1/2)·2 = 1`), but in the worst order `k − 1 = 2` rounds are needed: the second
round still changes the domains, the third does not. -/
theorem chain_remark :
    (∀ c ∈ chainCs, ∀ v ∈ c.vars, (chainW v \ proj c chainW v).card ≤ 1) ∧
      ((chainW 1 \ proj (chainCs[1]) chainW 1).card = 1 ∧ (chainW 1).card = 2) ∧
      (∀ v ∈ (chainCs[0]).vars, chainW v \ proj (chainCs[0]) chainW v = ∅) ∧
      (∀ v ∈ (chainCs[1]).vars, v ≠ 1 → chainW v \ proj (chainCs[1]) chainW v = ∅) ∧
      Tcomp chainCs chainW ≠ (Tcomp chainCs)^[2] chainW ∧
      (Tcomp chainCs)^[3] chainW = (Tcomp chainCs)^[2] chainW := by
  decide

end ArcsAlgo.Propagation
