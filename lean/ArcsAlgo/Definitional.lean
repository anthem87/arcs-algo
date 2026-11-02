module

public import ArcsAlgo.Structural
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false

/-!
# The information limit and definitional variables (paper §7.2 Theorem 7.3, §7.5 Theorem 7.7)

Solutions are a finite set `S` of total assignments `V → Val`.

* Theorem 7.3: `card_le_of_determines` (fixing one variable determines all: `|S| ≤ |Val|`, so
  `|S| ≤ 2` for Boolean values), `card_le_of_extension` (the same for an extension that preserves
  the projection), `card_le_of_inputs` and `determined_by_inputs` (with definitions only, the
  inputs determine the solution: `|S| ≤ |Val|^{|I|}`).
* Theorem 7.7: `functional_iff`, `extension_determines` (the definitional variable `X := g(A)`
  with the link `B = X` is conservative and fixes `B` from `A` in one pass of `T_struct`),
  `determined_imp_functional`, `parity_class_iff_bijective`.
-/

@[expose] public section

namespace ArcsAlgo.Definitional

open Finset

variable {V Val : Type*}

/-- **Theorem 7.3, first part** (paper §7.2): if fixing the variable `v` determines all the
others on the solutions `S`, then `|S| ≤ |Val|` (`≤ 2` for Boolean values). -/
theorem card_le_of_determines [Fintype V] [DecidableEq V] [Fintype Val] [DecidableEq Val] (S : Finset (V → Val)) (v : V)
    (h : ∀ s ∈ S, ∀ t ∈ S, s v = t v → s = t) : S.card ≤ Fintype.card Val := by
  have : Set.InjOn (fun s : V → Val => s v) S := fun s hs t ht hst => h s hs t ht hst
  calc S.card = (S.image fun s => s v).card := (card_image_of_injOn this).symm
    _ ≤ Fintype.card Val := card_le_univ _

/-- **Theorem 7.3, extensions** (paper §7.2): for an extension by auxiliary variables whose
solutions `S'` project onto `S` (`S = π(S')`), if fixing `v` determines all the variables of the
extension, then `|S| ≤ |S'| ≤ |Val|`. -/
theorem card_le_of_extension [Fintype V] [DecidableEq V] [Fintype Val] [DecidableEq Val]
    {V' : Type*} [Fintype V'] [DecidableEq V'] (S' : Finset (V' → Val)) (π : (V' → Val) → (V → Val))
    (v : V') (h : ∀ s ∈ S', ∀ t ∈ S', s v = t v → s = t) :
    (S'.image π).card ≤ S'.card ∧ S'.card ≤ Fintype.card Val :=
  ⟨card_image_le, card_le_of_determines S' v h⟩

/-- **Theorem 7.3, inputs** (paper §7.2): if the inputs `I` determine the solutions, then
`|S| ≤ |Val|^{|I|}` (`2^{|I|}` for Boolean values). -/
theorem card_le_of_inputs [Fintype V] [DecidableEq V] [Fintype Val] [DecidableEq Val] (S : Finset (V → Val)) (I : Finset V)
    (h : ∀ s ∈ S, ∀ t ∈ S, (∀ i ∈ I, s i = t i) → s = t) :
    S.card ≤ Fintype.card Val ^ I.card := by
  have hinj : Set.InjOn (fun s : V → Val => fun i : I => s i) S := by
    intro s hs t ht hst
    exact h s hs t ht fun i hi => congrFun hst ⟨i, hi⟩
  calc S.card = (S.image fun s : V → Val => fun i : I => s i).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (I → Val) := card_le_univ _
    _ = Fintype.card Val ^ I.card := by rw [Fintype.card_fun, Fintype.card_coe]

/-- **Theorem 7.3, definitions only** (paper §7.2): if every variable outside the inputs `I`
has a definition reading variables of strictly smaller rank, two assignments that satisfy all
the definitions and agree on the inputs are equal. Hence `card_le_of_inputs` applies. -/
theorem determined_by_inputs (I : Finset V) (rank : V → ℕ) (pred : V → Finset V)
    (f : V → (V → Val) → Val) (hrank : ∀ x ∉ I, ∀ u ∈ pred x, rank u < rank x)
    (hloc : ∀ x, ∀ α β : V → Val, (∀ u ∈ pred x, α u = β u) → f x α = f x β)
    (s t : V → Val) (hs : ∀ x ∉ I, s x = f x s) (ht : ∀ x ∉ I, t x = f x t)
    (hI : ∀ i ∈ I, s i = t i) : s = t := by
  funext x
  induction hx : rank x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hxI : x ∈ I
    · exact hI x hxI
    · rw [hs x hxI, ht x hxI]
      exact hloc x s t fun u hu => ih (rank u) (hx ▸ hrank x hxI u hu) u rfl

/-! ### Theorem 7.7 -/

/-- `R_AB = π_{A,B}(S)` is functional: `B = g(A)` on every solution. -/
def Functional (S : Finset (V → Val)) (A B : V) : Prop := ∃ g : Val → Val, ∀ s ∈ S, s B = g (s A)

theorem functional_iff (S : Finset (V → Val)) (A B : V) [Inhabited Val] :
    Functional S A B ↔ ∀ s ∈ S, ∀ t ∈ S, s A = t A → s B = t B := by
  classical
  constructor
  · rintro ⟨g, hg⟩ s hs t ht hst
    rw [hg s hs, hg t ht, hst]
  · intro h
    refine ⟨fun a => if hex : ∃ s ∈ S, s A = a then (Classical.choose hex) B else default, ?_⟩
    intro s hs
    have hex : ∃ t ∈ S, t A = s A := ⟨s, hs, rfl⟩
    simp only [hex, dite_true]
    have hspec := Classical.choose_spec hex
    exact (h _ hspec.1 s hs hspec.2).symm

/-- **Theorem 7.7 (⇒)** (paper §7.5): a definitional extension preserves the projection of the
solutions; if, in it, fixing `A` determines `B` on every solution (`B = P(A)`), then `R_AB` is
functional. -/
theorem determined_imp_functional [Fintype V] [DecidableEq V] [DecidableEq Val]
    {V' : Type*} (S' : Finset (V' → Val)) (π : (V' → Val) → (V → Val))
    (A B : V) (P : Val → Val) (hP : ∀ s ∈ S', π s B = P (π s A)) :
    Functional (S'.image π) A B := by
  refine ⟨P, ?_⟩
  intro s hs
  obtain ⟨s', hs', rfl⟩ := mem_image.1 hs
  exact hP s' hs'

/-- The extension of an assignment by the definitional variable `X := g(A)` (`none` is `X`). -/
def extend (g : Val → Val) (A : V) (s : V → Val) : Option V → Val
  | none => g (s A)
  | some v => s v

/-- **Theorem 7.7 (⇐), conservativity** (paper §7.5): if `B = g(A)` on every solution, adding
`X := g(A)` and the link `B = X` keeps exactly the solutions: the extended solutions are the
`extend g A s`, they satisfy both new constraints, and they project back onto `S`. -/
theorem extension_conservative [Fintype V] [DecidableEq V] [DecidableEq Val] (S : Finset (V → Val)) (A B : V) (g : Val → Val)
    (hg : ∀ s ∈ S, s B = g (s A)) :
    (∀ s ∈ S, extend g A s none = g (extend g A s (some A)) ∧
        extend g A s (some B) = extend g A s none) ∧
      (S.image (extend g A)).image (fun s' v => s' (some v)) = S := by
  refine ⟨fun s hs => ⟨rfl, hg s hs⟩, ?_⟩
  rw [Finset.image_image]
  have : (fun s' : Option V → Val => fun v => s' (some v)) ∘ extend g A = id := by
    funext s v; rfl
  rw [this, Finset.image_id]

open ArcsAlgo.Structural in
/-- **Theorem 7.7 (⇐), one pass** (paper §7.5): in the Boolean structural model, with the
definition `X := g(A)` and the parity link `B = X` (one class `{X, B}` with root `X`), fixing
`A = a` makes `T_struct` fix `B` to `g(a)` in one pass. -/
theorem extension_determines [Fintype V] [DecidableEq V] (A B : V) (hAB : A ≠ B) (g : Bool → Bool)
    (W : Option V → Finset Bool) (a : Bool) (hA : W (some A) = {a}) :
    let K : Classes (Option V) :=
      ⟨fun v => if v = some B then none else v, fun _ => false,
        fun v => by by_cases h : v = some B <;> simp [h],
        fun _ => rfl⟩
    let d : Structural.Def (Option V) := ⟨none, {some A}, fun α => g (α (some A)),
      fun α β h => by rw [h (some A) (mem_singleton_self _)]⟩
    Tstruct K [d] W (some B) ⊆ {g a} := by
  intro K d
  have hAB' : (some A : Option V) ≠ some B := fun h => hAB (Option.some_injective _ h)
  have hrootB : K.root (some B) = none := by simp [K]
  have hrootA : K.root (some A) = some A := by simp [K, hAB']
  have hrootN : K.root none = none := by simp [K]
  have hparA : Par K W (some A) ⊆ {a} := by
    unfold Par
    apply Finset.inf_le_of_le (b := some A) (by simp [hrootA])
    rw [hA]
    simp [K]
  have hdomA : dom K (Par K W) (some A) ⊆ {a} := by
    simp only [dom, hrootA]
    rw [show K.bit (some A) = false from rfl, Structural.image_xor_false]
    exact hparA
  have himg : img K d (Par K W) ⊆ {g a} := by
    intro b hb
    simp only [img, mem_image, Fintype.mem_piFinset] at hb
    obtain ⟨α, hα, rfl⟩ := hb
    have h1 := hα (some A)
    simp only [d, mem_singleton, ite_true] at h1
    have h2 := hdomA h1
    rw [mem_singleton] at h2
    simp [d, h2]
  intro b hb
  simp only [Tstruct, dom, Eval, List.foldl_cons, List.foldl_nil, hrootB] at hb
  rw [show K.bit (some B) = false from rfl, Structural.image_xor_false] at hb
  simp only [evalDef, show d.x = none from rfl, hrootN, Function.update_self] at hb
  have h3 := (mem_inter.1 hb).2
  rw [show K.bit none = false from rfl, Structural.image_xor_false] at h3
  exact himg h3

/-- **Theorem 7.7, same class** (paper §7.5): for Boolean values `A` and `B` lie in one class of
`Par` (`B = A ⊕ b` on the solutions) exactly when `g` is a bijection. -/
theorem parity_class_iff_bijective (g : Bool → Bool) :
    Function.Bijective g ↔ ∃ b, ∀ a, g a = xor a b := by
  constructor
  · intro hg
    refine ⟨g false, fun a => ?_⟩
    cases a
    · simp
    · have h := hg.1.ne (show (false : Bool) ≠ true by decide)
      cases h0 : g false <;> cases h1 : g true <;> simp_all
  · rintro ⟨b, hb⟩
    have : g = fun a => xor a b := funext hb
    subst this
    exact ⟨fun x y h => by simpa using h, fun y => ⟨xor y b, by simp⟩⟩

end ArcsAlgo.Definitional
