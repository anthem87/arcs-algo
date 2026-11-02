module

public import ArcsAlgo.Propagation
set_option autoImplicit false

/-!
# Constraint propagation: the structural part (paper §7.2)

Boolean variables `V`. `Par` (union-find with parity on the constraints `x = y ⊕ b`) is
represented by its result, a set of classes: every variable is `x = r ⊕ b_x` with `r = root x` the
root of its class, and there is one shared cell per class. A state is a family of cells `C`
(read at the roots); the domain of `x` is `dom C x = C(root x) ⊕ b_x`, so every state is in the
shared form `𝒮`.

`Eval` is one pass over the definitions `x := f_x(pred x)`, in the order of the list; each
definition intersects the cell of the class of `x` with the forward image of its parents.

* `Tstruct_idem` (Theorem 7.2 (a), corrected): `T_struct ∘ T_struct = T_struct` when the order of
  the definitions is topological on the parity classes (`RankedDefs`).
  `Tstruct_not_idem_counterexample`: with an order that is topological only on the variables,
  as the paper states, idempotence fails.
* `Tstruct_of_closed` (Theorem 7.2 (b)).
* `inject_dom`, `Eval_fixes` (Theorem 7.2 (c): at most one value), `Eval_nonempty`,
  `Eval_fixes_exactly` (exactly one value when the network has a solution in the initial cells).
  `Eval_blocks_counterexample`: under the paper's hypotheses alone the pass may block.
* `parity_supported`, `def_supported` (Theorem 7.2 (d)).
-/

@[expose] public section

namespace ArcsAlgo.Structural

open Finset ArcsAlgo.Propagation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The result of `Par`: a root and a parity bit for every variable (paper Definition 7.1). -/
structure Classes (V : Type*) where
  root : V → V
  bit : V → Bool
  root_root : ∀ x, root (root x) = root x
  bit_root : ∀ x, bit (root x) = false

/-- A functional definition `x := f(pred x)` (paper §7.1, family Def). `f` reads only `pred`. -/
structure Def (V : Type*) where
  x : V
  pred : Finset V
  f : (V → Bool) → Bool
  local_f : ∀ α β : V → Bool, (∀ u ∈ pred, α u = β u) → f α = f β

/-- Cells of the parity classes, read at the roots. -/
abbrev Cells (V : Type*) := V → Finset Bool

variable (K : Classes V)

/-- The domain of `x` in the shared form: `C(root x) ⊕ b_x`. -/
def dom (C : Cells V) (x : V) : Finset Bool := (C (K.root x)).image (xor (K.bit x))

/-- The forward image `f_x(∏_{u ∈ pred x} W(u))` of a definition. -/
def img (d : Def V) (C : Cells V) : Finset Bool :=
  (Fintype.piFinset fun u => if u ∈ d.pred then dom K C u else univ).image d.f

/-- One definition of `Eval`: `W(x) ← W(x) ∩ f_x(∏ W(u))`, written in the cell of the class. -/
def evalDef (d : Def V) (C : Cells V) : Cells V :=
  Function.update C (K.root d.x) (C (K.root d.x) ∩ (img K d C).image (xor (K.bit d.x)))

/-- `Eval`: one pass over the definitions, in the order of the list (paper Definition 7.1). -/
def Eval (defs : List (Def V)) (C : Cells V) : Cells V := defs.foldl (fun C d => evalDef K d C) C

/-- `Par`: the cell of a class is the intersection of the domains of its members, each brought
to the root by its parity bit (paper Definition 7.1). -/
def Par (W : V → Finset Bool) : Cells V :=
  fun r => (univ.filter fun y => K.root y = r).inf fun y => (W y).image (xor (K.bit y))

/-- `T_struct = Eval ∘ Par`, as domains (paper Definition 7.1). -/
def Tstruct (defs : List (Def V)) (W : V → Finset Bool) : V → Finset Bool :=
  dom K (Eval K defs (Par K W))

/-- The shared form `𝒮`: `W(x) = W(y) ⊕ (b_x ⊕ b_y)` on every class. -/
def Shared (W : V → Finset Bool) : Prop :=
  ∀ x y, K.root x = K.root y → W x = (W y).image (xor (K.bit x ^^ K.bit y))

/-! ### Basic facts -/

theorem image_xor_image (s : Finset Bool) (a b : Bool) :
    (s.image (xor a)).image (xor b) = s.image (xor (a ^^ b)) := by
  rw [Finset.image_image]; congr 1; funext x; cases a <;> cases b <;> cases x <;> rfl

theorem image_xor_false (s : Finset Bool) : s.image (xor false) = s := by
  have : xor false = id := funext fun b => by cases b <;> rfl
  simp [this]

theorem image_xor_self (s : Finset Bool) (a : Bool) : (s.image (xor a)).image (xor a) = s := by
  rw [image_xor_image]; simpa using image_xor_false s

omit [Fintype V] [DecidableEq V] in
theorem dom_shared (C : Cells V) : Shared K (dom K C) := by
  intro x y hxy
  simp only [dom, hxy, image_xor_image]
  congr 1; funext b; cases K.bit x <;> cases K.bit y <;> cases b <;> rfl

/-- Two families of cells agree on the roots. -/
def AgreeRoots (C C' : Cells V) : Prop := ∀ x, C (K.root x) = C' (K.root x)

omit [Fintype V] [DecidableEq V] in
theorem dom_congr {C C' : Cells V} (h : AgreeRoots K C C') : dom K C = dom K C' := by
  funext x; simp [dom, h x]

theorem img_congr (d : Def V) {C C' : Cells V} (h : AgreeRoots K C C') : img K d C = img K d C' := by
  simp [img, dom_congr K h]

theorem evalDef_congr (d : Def V) {C C' : Cells V} (h : AgreeRoots K C C') :
    AgreeRoots K (evalDef K d C) (evalDef K d C') := by
  intro x
  simp only [evalDef, Function.update_apply]
  split_ifs
  · rw [h d.x, img_congr K d h]
  · exact h x

theorem Eval_congr (defs : List (Def V)) {C C' : Cells V} (h : AgreeRoots K C C') :
    AgreeRoots K (Eval K defs C) (Eval K defs C') := by
  induction defs generalizing C C' with
  | nil => exact h
  | cons d defs ih => exact ih (evalDef_congr K d h)

theorem Par_dom (C : Cells V) : AgreeRoots K (Par K (dom K C)) C := by
  intro x
  apply le_antisymm
  · apply Finset.inf_le_of_le (b := K.root x)
    · simp [K.root_root]
    · simp [dom, K.root_root, K.bit_root, image_xor_false]
  · apply Finset.le_inf
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    simp [dom, hy, image_xor_self]

theorem Par_of_shared {W : V → Finset Bool} (hW : Shared K W) : dom K (Par K W) = W := by
  funext x
  have hcell : Par K W (K.root x) = (W x).image (xor (K.bit x)) := by
    apply le_antisymm
    · exact Finset.inf_le (by simp)
    · apply Finset.le_inf
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [hW x y hy.symm, image_xor_image]
      apply le_of_eq; congr 1; funext b
      cases K.bit x <;> cases K.bit y <;> cases b <;> rfl
  simp [dom, hcell, image_xor_self]

/-! ### Theorem 7.2 (a), corrected -/

/-- The definitions are processed in an order that is topological on the parity classes: a rank
on the roots such that every parent of a definition lies in a class of strictly smaller rank,
and the list is sorted by the rank of the class it writes. -/
def RankedDefs (defs : List (Def V)) (rank : V → ℕ) : Prop :=
  (∀ d ∈ defs, ∀ u ∈ d.pred, rank (K.root u) < rank (K.root d.x)) ∧
  defs.Pairwise fun d e => rank (K.root d.x) ≤ rank (K.root e.x)

theorem evalDef_le (d : Def V) (C : Cells V) : evalDef K d C ≤ C := by
  intro r
  simp only [evalDef, Function.update_apply]
  split_ifs with h
  · subst h; exact inter_subset_left
  · exact le_rfl

theorem Eval_le (defs : List (Def V)) (C : Cells V) : Eval K defs C ≤ C := by
  induction defs generalizing C with
  | nil => exact le_rfl
  | cons d defs ih => exact (ih _).trans (evalDef_le K d C)

/-- A definition reads only the cells of the classes of its parents. -/
theorem img_eq_of_agree (d : Def V) {C C' : Cells V}
    (h : ∀ u ∈ d.pred, C (K.root u) = C' (K.root u)) : img K d C = img K d C' := by
  unfold img
  have : (fun u => if u ∈ d.pred then dom K C u else univ) =
      (fun u => if u ∈ d.pred then dom K C' u else univ) := by
    funext u
    split_ifs with hu
    · simp [dom, h u hu]
    · rfl
  rw [this]

/-- `evalDef d` changes only the cell of the class of `d.x`. -/
theorem evalDef_apply_ne (d : Def V) (C : Cells V) {r : V} (hr : r ≠ K.root d.x) :
    evalDef K d C r = C r := by
  simp [evalDef, hr]

/-- Definitions writing classes of rank `≥ k` leave the cells of rank `< k` unchanged. -/
theorem Eval_low (rank : V → ℕ) (k : ℕ) (defs : List (Def V))
    (hk : ∀ e ∈ defs, k ≤ rank (K.root e.x)) (C : Cells V) (x : V)
    (hx : rank (K.root x) < k) : Eval K defs C (K.root x) = C (K.root x) := by
  induction defs generalizing C with
  | nil => rfl
  | cons e defs ih =>
    have h1 := ih (fun e' he' => hk e' (List.mem_cons_of_mem _ he')) (evalDef K e C)
    have hne : K.root x ≠ K.root e.x := by
      intro h; have := hk e List.mem_cons_self; rw [← h] at this; omega
    rw [show Eval K (e :: defs) C = Eval K defs (evalDef K e C) from rfl, h1,
      evalDef_apply_ne K e C hne]

/-- After one pass, every definition is satisfied: `evalDef d (Eval defs C) = Eval defs C` for
every `d ∈ defs`, when the order is topological on the parity classes. -/
theorem Eval_closed (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (C : Cells V) : ∀ d ∈ defs, evalDef K d (Eval K defs C) = Eval K defs C := by
  induction defs generalizing C with
  | nil => simp
  | cons d rest ih =>
    obtain ⟨hpar, hsort⟩ := hR
    rw [List.pairwise_cons] at hsort
    have hR' : RankedDefs K rest rank :=
      ⟨fun e he => hpar e (List.mem_cons_of_mem _ he), hsort.2⟩
    have hEval : Eval K (d :: rest) C = Eval K rest (evalDef K d C) := rfl
    intro e he
    rw [hEval]
    rcases List.mem_cons.1 he with rfl | he
    · have hlow : ∀ u ∈ e.pred, Eval K rest (evalDef K e C) (K.root u) = C (K.root u) := by
        intro u hu
        have hlt := hpar e List.mem_cons_self u hu
        rw [Eval_low K rank (rank (K.root e.x)) rest (fun e' he' => hsort.1 e' he') _ u hlt]
        apply evalDef_apply_ne
        intro h; rw [h] at hlt; omega
      have himg : img K e (Eval K rest (evalDef K e C)) = img K e C := img_eq_of_agree K e hlow
      have hsub : Eval K rest (evalDef K e C) (K.root e.x) ⊆
          (img K e C).image (xor (K.bit e.x)) := by
        have h1 := Eval_le K rest (evalDef K e C) (K.root e.x)
        simp only [evalDef, Function.update_self] at h1
        exact h1.trans inter_subset_right
      rw [evalDef, himg, Finset.inter_eq_left.2 hsub, Function.update_eq_self]
    · exact ih hR' (evalDef K d C) e he

theorem Eval_Eval (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (C : Cells V) : Eval K defs (Eval K defs C) = Eval K defs C := by
  have h := Eval_closed K rank defs hR C
  generalize hC1 : Eval K defs C = C1 at h ⊢
  clear hC1 hR
  induction defs with
  | nil => rfl
  | cons d rest ih =>
    rw [show Eval K (d :: rest) C1 = Eval K rest (evalDef K d C1) from rfl, h d List.mem_cons_self]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- **Theorem 7.2 (a)** (paper §7.2, with `Eval` in a topological order of the parity classes as
in Definition 7.1): `T_struct ∘ T_struct = T_struct` and `T_struct(W) ∈ 𝒮`, when the definitions
are processed in an order that is topological on the parity classes (`RankedDefs`). A topological
order of the variables alone is not enough (Remark 7.2′, `Tstruct_not_idem_counterexample`). -/
theorem Tstruct_idem (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (W : V → Finset Bool) :
    Tstruct K defs (Tstruct K defs W) = Tstruct K defs W ∧ Shared K (Tstruct K defs W) := by
  refine ⟨?_, dom_shared K _⟩
  unfold Tstruct
  apply dom_congr
  intro x
  rw [Eval_congr K defs (Par_dom K _) x, Eval_Eval K rank defs hR]

/-- `W` is closed under `Eval`: every value of a defined variable is an image of values of its
parents. -/
def ClosedEval (defs : List (Def V)) (W : V → Finset Bool) : Prop :=
  ∀ d ∈ defs, W d.x ⊆ (Fintype.piFinset fun u => if u ∈ d.pred then W u else univ).image d.f

/-- **Theorem 7.2 (b)** (paper §7.2): for `W ∈ 𝒮` closed under `Eval`, `T_struct(W) = W`. -/
theorem Tstruct_of_closed (defs : List (Def V)) {W : V → Finset Bool} (hW : Shared K W)
    (hc : ClosedEval defs W) : Tstruct K defs W = W := by
  have hdom : dom K (Par K W) = W := Par_of_shared K hW
  have hfix : ∀ d ∈ defs, evalDef K d (Par K W) = Par K W := by
    intro d hd
    unfold evalDef
    rw [Function.update_eq_self_iff]
    apply Finset.inter_eq_left.2
    have hcell : Par K W (K.root d.x) = (W d.x).image (xor (K.bit d.x)) := by
      have := congrFun hdom d.x
      simp only [dom] at this
      rw [← this, image_xor_self]
    rw [hcell, img, hdom]
    exact Finset.image_subset_image (hc d hd)
  unfold Tstruct
  have : Eval K defs (Par K W) = Par K W := by
    clear hc
    induction defs with
    | nil => rfl
    | cons d rest ih =>
      rw [show Eval K (d :: rest) (Par K W) = Eval K rest (evalDef K d (Par K W)) from rfl,
        hfix d List.mem_cons_self]
      exact ih fun e he => hfix e (List.mem_cons_of_mem _ he)
  rw [this, hdom]

/-! ### Theorem 7.2 (c) -/

/-- Injection of the value `a` for the variable `x`: the cell of its class is intersected with
the corresponding value of the root. -/
def inject (C : Cells V) (x : V) (a : Bool) : Cells V :=
  Function.update C (K.root x) (C (K.root x) ∩ {xor (K.bit x) a})

omit [Fintype V] in
/-- **Theorem 7.2 (c), injection** (paper §7.2): injecting `x = a` changes one cell only, that
of the class of `x`; every member `y` of the class gets the value `a ⊕ b_x ⊕ b_y` (or fails). -/
theorem inject_dom (C : Cells V) (x : V) (a : Bool) :
    (∀ r ≠ K.root x, inject K C x a r = C r) ∧
      ∀ y, K.root y = K.root x → dom K (inject K C x a) y ⊆ {xor (K.bit y) (xor (K.bit x) a)} := by
  refine ⟨fun r hr => by simp [inject, hr], fun y hy => ?_⟩
  simp only [dom, inject, hy, Function.update_self]
  intro b hb
  simp only [mem_image, mem_inter, mem_singleton] at hb
  obtain ⟨c, ⟨_, rfl⟩, rfl⟩ := hb
  simp

theorem img_card_le_one (d : Def V) (C : Cells V)
    (h : ∀ u ∈ d.pred, (dom K C u).card ≤ 1) : (img K d C).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [img, mem_image, Fintype.mem_piFinset] at ha hb
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  apply d.local_f
  intro u hu
  have h1 := hα u; have h2 := hβ u
  simp only [hu, ite_true] at h1 h2
  exact Finset.card_le_one.1 (h u hu) _ h1 _ h2

/-- **Theorem 7.2 (c), all inputs fixed** (paper §7.2): if every class either is fixed (a cell
with at most one value) or is written by a definition, then one pass of `Eval`, in an order
topological on the classes, fixes every variable: every domain has at most one value. A domain is
empty only on a conflict, for instance two inputs of one class fixed inconsistently, which is why
Theorem 7.2 (c) asks that no parity class contain two inputs. -/
theorem Eval_fixes (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (C : Cells V)
    (hC : ∀ x, (C (K.root x)).card ≤ 1 ∨ ∃ d ∈ defs, K.root d.x = K.root x) :
    ∀ x, (dom K (Eval K defs C) x).card ≤ 1 := by
  have hcell : ∀ n, ∀ x, rank (K.root x) ≤ n → (Eval K defs C (K.root x)).card ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      rcases hC x with h | ⟨d, hd, hdx⟩
      · exact (card_le_card (Eval_le K defs C _)).trans h
      · have hclosed := Eval_closed K rank defs hR C d hd
        have hsub : Eval K defs C (K.root d.x) ⊆
            (img K d (Eval K defs C)).image (xor (K.bit d.x)) := by
          have := congrFun hclosed (K.root d.x)
          simp only [evalDef, Function.update_self] at this
          rw [← this]; exact inter_subset_right
        rw [← hdx]
        refine (card_le_card hsub).trans (card_image_le.trans (img_card_le_one K d _ ?_))
        intro u hu
        have hlt := hR.1 d hd u hu
        rw [hdx] at hlt
        exact card_image_le.trans (ih (rank (K.root u)) (by omega) u le_rfl)
  intro x
  exact card_image_le.trans (hcell _ x le_rfl)

/-- An assignment `α` is a solution of the parity classes and of the definitions. -/
def IsSolution (defs : List (Def V)) (α : V → Bool) : Prop :=
  (∀ x, α x = xor (K.bit x) (α (K.root x))) ∧ ∀ d ∈ defs, α d.x = d.f α

omit [Fintype V] in
theorem mem_dom_of_root {C : Cells V} {α : V → Bool} (hpar : ∀ x, α x = xor (K.bit x) (α (K.root x)))
    (x : V) (hx : α (K.root x) ∈ C (K.root x)) : α x ∈ dom K C x := by
  rw [hpar x]; exact mem_image_of_mem _ hx

/-- `evalDef` keeps the values of a solution in every cell. -/
theorem evalDef_keeps (defs : List (Def V)) {α : V → Bool} (hα : IsSolution K defs α)
    {d : Def V} (hd : d ∈ defs) {C : Cells V} (hC : ∀ x, α (K.root x) ∈ C (K.root x)) :
    ∀ x, α (K.root x) ∈ evalDef K d C (K.root x) := by
  intro x
  simp only [evalDef, Function.update_apply]
  split_ifs with h
  · rw [h]
    refine mem_inter.2 ⟨hC d.x, ?_⟩
    have himg : d.f α ∈ img K d C := by
      unfold img
      refine mem_image.2 ⟨α, Fintype.mem_piFinset.2 fun u => ?_, rfl⟩
      split_ifs
      · exact mem_dom_of_root K hα.1 u (hC u)
      · exact mem_univ _
    have hroot : α (K.root d.x) = xor (K.bit d.x) (d.f α) := by
      rw [← hα.2 d hd, hα.1 d.x]; cases K.bit d.x <;> cases α (K.root d.x) <;> rfl
    rw [hroot]; exact mem_image_of_mem _ himg
  · exact hC x

theorem Eval_keeps (defs₀ : List (Def V)) {α : V → Bool} (hα : IsSolution K defs₀ α) :
    ∀ (defs : List (Def V)), (∀ d ∈ defs, d ∈ defs₀) → ∀ (C : Cells V),
      (∀ x, α (K.root x) ∈ C (K.root x)) → ∀ x, α (K.root x) ∈ Eval K defs C (K.root x) := by
  intro defs
  induction defs with
  | nil => intro _ C hC; exact hC
  | cons d rest ih =>
    intro hsub C hC
    exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) _
      (evalDef_keeps K defs₀ hα (hsub d List.mem_cons_self) hC)

/-- **Theorem 7.2 (c), without blocking, under a consistent initial state**: if the parity classes
and the definitions have a solution `α` whose values lie in the initial cells, then after one
pass of `Eval` every domain contains `α`; it is non-empty. -/
theorem Eval_nonempty (defs : List (Def V)) (C : Cells V) {α : V → Bool} (hα : IsSolution K defs α)
    (hC : ∀ x, α (K.root x) ∈ C (K.root x)) : ∀ x, α x ∈ dom K (Eval K defs C) x := fun x =>
  mem_dom_of_root K hα.1 x (Eval_keeps K defs hα defs (fun _ h => h) C hC x)

/-- **Theorem 7.2 (c), all inputs fixed, without blocking**: under the hypotheses of `Eval_fixes`
(definitions in an order topological on the parity classes; every class fixed or written by a
definition) and a solution `α` of the network lying in the initial cells, one pass of `Eval`
leaves exactly one value in every domain, the value of `α`. Without the solution the pass may block:
`Eval_blocks_counterexample`. -/
theorem Eval_fixes_exactly (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (C : Cells V) (hfix : ∀ x, (C (K.root x)).card ≤ 1 ∨ ∃ d ∈ defs, K.root d.x = K.root x)
    {α : V → Bool} (hα : IsSolution K defs α) (hC : ∀ x, α (K.root x) ∈ C (K.root x)) :
    ∀ x, dom K (Eval K defs C) x = {α x} := by
  intro x
  have h1 := Eval_fixes K rank defs hR C hfix x
  have h2 := Eval_nonempty K defs C hα hC x
  exact (Finset.card_le_one_iff_subset_singleton.mp h1).elim fun a ha => by
    have : α x = a := mem_singleton.1 (ha h2)
    subst this; exact Finset.Subset.antisymm ha (singleton_subset_iff.2 h2)

/-! ### Theorem 7.2 (d) -/

/-- The parity constraint `x = y ⊕ b` as a constraint of §7.1. -/
def parityConstraint (x y : V) (b : Bool) : Constraint V Bool :=
  ⟨{x, y}, fun α => α x == xor (α y) b⟩

/-- **Theorem 7.2 (d), parity constraints** (paper §7.2): in the shared form every value has a
support in every parity constraint `x = y ⊕ b` of `C_par` (`υ = 0`). -/
theorem parity_supported {W : V → Finset Bool} (hW : Shared K W) (x y : V) (b : Bool)
    (hxy : K.root x = K.root y) (hb : b = (K.bit x ^^ K.bit y)) :
    Supported (parityConstraint x y b) W := by
  have hWx : ∀ a ∈ W x, xor a b ∈ W y := by
    intro a ha
    rw [hW x y hxy] at ha
    obtain ⟨c, hc, rfl⟩ := mem_image.1 ha
    convert hc using 1
    subst hb; cases K.bit x <;> cases K.bit y <;> cases c <;> rfl
  have hWy : ∀ a ∈ W y, xor a b ∈ W x := by
    intro a ha
    rw [hW x y hxy]
    refine mem_image.2 ⟨a, ha, ?_⟩
    subst hb; cases K.bit x <;> cases K.bit y <;> cases a <;> rfl
  intro v hv
  apply Subset.antisymm (proj_subset _ _ _)
  intro a ha
  simp only [parityConstraint, mem_insert, mem_singleton] at hv
  simp only [proj, mem_filter]
  refine ⟨ha, ?_⟩
  by_cases hxy' : x = y
  · subst hxy'
    have hb0 : b = false := by rw [hb]; simp
    subst hb0
    rcases hv with rfl | rfl <;>
      exact ⟨fun _ => a, rfl, by simp [parityConstraint], by
        intro u hu; simp only [parityConstraint, mem_insert, mem_singleton, or_self] at hu
        subst hu; exact ha⟩
  · rcases hv with rfl | rfl
    · refine ⟨fun u => if u = v then a else xor a b, by simp, ?_, ?_⟩
      · simp [parityConstraint, Ne.symm hxy']
      · intro u hu
        simp only [parityConstraint, mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · simpa using ha
        · simpa [Ne.symm hxy'] using hWx a ha
    · refine ⟨fun u => if u = v then a else xor a b, by simp, ?_, ?_⟩
      · simp [parityConstraint, hxy']
      · intro u hu
        simp only [parityConstraint, mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · simpa [hxy'] using hWy a ha
        · simpa using ha

/-- A definition read forwards, as a constraint `x = f_x(pred x)` of §7.1. -/
def defConstraint (d : Def V) : Constraint V Bool := ⟨insert d.x d.pred, fun α => α d.x == d.f α⟩

/-- **Theorem 7.2 (d), definitions read forwards** (paper §7.2): for `W` closed under `Eval`,
every value of a defined variable has a support in its definition (the defect of the definition,
read from the parents to `x`, is zero). -/
theorem def_supported (d : Def V) (hx : d.x ∉ d.pred) {W : V → Finset Bool}
    (hc : W d.x ⊆ (Fintype.piFinset fun u => if u ∈ d.pred then W u else univ).image d.f) :
    proj (defConstraint d) W d.x = W d.x := by
  apply Subset.antisymm (proj_subset _ _ _)
  intro a ha
  simp only [proj, mem_filter]
  refine ⟨ha, ?_⟩
  obtain ⟨β, hβ, hfb⟩ := mem_image.1 (hc ha)
  refine ⟨Function.update β d.x a, by simp, ?_, ?_⟩
  · have : d.f (Function.update β d.x a) = d.f β :=
      d.local_f _ _ fun u hu => by simp [show u ≠ d.x from fun h => hx (h ▸ hu)]
    simp [defConstraint, this, hfb]
  · intro u hu
    simp only [defConstraint, mem_insert] at hu
    rcases hu with rfl | hu
    · simpa using ha
    · have := Fintype.mem_piFinset.1 hβ u
      simp only [hu, ite_true] at this
      simpa [Function.update_apply, show u ≠ d.x from fun h => hx (h ▸ hu)] using this

/-! ### Theorem 7.6 -/

/-- The full operator `T = T_comp ∘ T_struct` (paper §7.4): `T_struct`, then the filters of the
computational part to their fixpoint. -/
def Tfull (defs : List (Def V)) (cs : List (Constraint V Bool)) (W : V → Finset Bool) :
    V → Finset Bool :=
  limit cs (Tstruct K defs W)

/-- **Theorem 7.6 (factorization)** (paper §7.4): `T = T_comp ∘ T_struct` returns the largest
`W' ⊑ T_struct(W)` on which every constraint of the computational part has defect zero; it
does not depend on the order of the filters. (The costs of the theorem, `O(|C_par| α(n))` for
union-find and one pass for `Eval`, are not formalized.) -/
theorem Tfull_spec (defs : List (Def V)) (cs : List (Constraint V Bool)) (W : V → Finset Bool) :
    Tfull K defs cs W ≤ Tstruct K defs W ∧ (∀ c ∈ cs, defect c (Tfull K defs cs W) = 0) ∧
      (∀ W' ≤ Tstruct K defs W, (∀ c ∈ cs, defect c W' = 0) → W' ≤ Tfull K defs cs W) ∧
      ∀ cs', cs.Perm cs' → Tfull K defs cs' W = Tfull K defs cs W :=
  ⟨limit_le cs _, limit_supported cs _, fun W' h1 h2 => limit_greatest cs _ W' h1 h2,
    fun _ hp => (limit_perm hp _).symm⟩

/-! ### The counterexample to Theorem 7.2 (a) as stated -/

/-- Four Boolean variables `u = 0, x = 1, w = 2, z = 3` with the parity class `{u, z}` (`u = z`). -/
def cexClasses : Classes (Fin 4) where
  root := fun i => if i = 3 then 0 else i
  bit := fun _ => false
  root_root := by decide
  bit_root := by decide

/-- The definitions `x := u` and `z := w`, in an order topological on the variables. -/
def cexDefs : List (Def (Fin 4)) :=
  [⟨1, {0}, fun α => α 0, fun α β h => h 0 (by simp)⟩,
   ⟨3, {2}, fun α => α 2, fun α β h => h 2 (by simp)⟩]

/-- **Remark 7.2′ (the order of Eval)** (paper §7.2): with the definitions `x := u`, `z := w`,
the parity link `u = z`, the order `u < x < w < z` (every definition reads earlier nodes) and
`W(w) = {false}`, a second application of `T_struct` changes `x`: the first pass computes `x` from
the cell of `u` before `z := w` narrows that cell. -/
theorem Tstruct_not_idem_counterexample :
    (∀ d ∈ cexDefs, ∀ u ∈ d.pred, u < d.x) ∧
      Tstruct cexClasses cexDefs (Tstruct cexClasses cexDefs fun i => if i = 2 then {false} else univ) 1 ≠
        Tstruct cexClasses cexDefs (fun i => if i = 2 then {false} else univ) 1 := by
  decide

/-! ### The counterexample to Theorem 7.2 (c), "without blocking", as stated -/

/-- Three Boolean variables `u = 0, x = 1, y = 2` with the parity class `{x, y}` (`x = y`). -/
def cexBlockClasses : Classes (Fin 3) where
  root := fun i => if i = 2 then 1 else i
  bit := fun _ => false
  root_root := by decide
  bit_root := by decide

/-- The definitions `x := u` and `y := ¬u`. -/
def cexBlockDefs : List (Def (Fin 3)) :=
  [⟨1, {0}, fun α => α 0, fun α β h => h 0 (by simp)⟩,
   ⟨2, {0}, fun α => !α 0, fun α β h => by rw [h 0 (by simp)]⟩]

/-- Rank: the class `{u}` has rank 0, the class `{x, y}` rank 1. -/
def cexBlockRank : Fin 3 → ℕ := fun i => if i = 0 then 0 else 1

/-- **Theorem 7.2 (c), "without blocking", fails as stated**: the only input `u` is fixed
(`C(u) = {false}`), no parity class contains two inputs (`{u}` and `{x, y}`), and the definitions
are in an order topological on the classes; yet after one pass of `Eval` the shared cell of
`{x, y}` is empty, because the two definitions writing that class disagree. -/
theorem Eval_blocks_counterexample :
    RankedDefs cexBlockClasses cexBlockDefs cexBlockRank ∧
      dom cexBlockClasses (Eval cexBlockClasses cexBlockDefs
        (fun i => if i = 0 then {false} else univ)) 2 = ∅ := by
  refine ⟨⟨?_, ?_⟩, by decide⟩
  · intro d hd u hu
    simp only [cexBlockDefs, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp at hu <;> subst hu <;> decide
  · simp [cexBlockDefs, cexBlockClasses, cexBlockRank]

end ArcsAlgo.Structural
