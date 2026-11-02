module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Field.ZMod
set_option autoImplicit false

/-!
# The affine case of Ext (paper §7.5, Proposition 7.9)

XOR constraints are linear equations `r ⬝ x = c` over a field (GF(2) for Boolean values). The
solutions form an affine subspace.

* `combination_holds` (soundness of Gauss, Proposition 7.8): every linear combination of the rows
  holds on every solution.
* `constant_iff_mem_span` (Proposition 7.9): on a non-empty affine solution set, a linear form
  `v ⬝ x` is constant iff `v` lies in the row space; with `v = e_x` a variable is forced iff `e_x`
  lies in the row space.
* `functional_iff_affine` (Proposition 7.9, pairs): over GF(2), `B` is a function of `A` on the
  solutions iff `e_B` or `e_A + e_B` lies in the row space.
-/

@[expose] public section

namespace ArcsAlgo.Affine

open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The solutions of the rows `R` (pairs `(r, c)` meaning `r ⬝ x = c`). -/
def Sol (R : Set ((ι → K) × K)) : Set (ι → K) := {x | ∀ p ∈ R, p.1 ⬝ᵥ x = p.2}

/-- The row space. -/
def rowSpace (R : Set ((ι → K) × K)) : Submodule K (ι → K) := Submodule.span K (Prod.fst '' R)

omit [DecidableEq ι] in
/-- **Proposition 7.8, Gauss is sound** (paper §7.5): a linear form in the row space takes the
same value on all solutions. -/
theorem combination_holds (R : Set ((ι → K) × K)) {v : ι → K} (hv : v ∈ rowSpace R) :
    ∀ x ∈ Sol R, ∀ y ∈ Sol R, v ⬝ᵥ x = v ⬝ᵥ y := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    intro x hx y hy
    rw [hx p hp, hy p hp]
  | zero => intro x _ y _; simp
  | add a b _ _ ha hb =>
    intro x hx y hy
    rw [add_dotProduct, add_dotProduct, ha x hx y hy, hb x hx y hy]
  | smul c a _ ha =>
    intro x hx y hy
    rw [smul_dotProduct, smul_dotProduct, ha x hx y hy]

omit [DecidableEq ι] in
theorem sol_add_kernel {R : Set ((ι → K) × K)} {x y : ι → K} (hx : x ∈ Sol R)
    (hy : ∀ p ∈ R, p.1 ⬝ᵥ y = 0) : x + y ∈ Sol R := by
  intro p hp
  rw [dotProduct_add, hx p hp, hy p hp, add_zero]

/-- **Proposition 7.9 (completeness in the affine case)** (paper §7.5): on a non-empty affine
set of solutions, the linear form `v ⬝ x` is constant iff `v` lies in the row space. For
`v = e_x` (`Pi.single x 1`): the variable `x` is forced iff `e_x` lies in the row space, which in
reduced form means that some row of the reduced matrix is `e_x`. -/
theorem constant_iff_mem_span (R : Set ((ι → K) × K)) {x₀ : ι → K} (hx₀ : x₀ ∈ Sol R)
    (v : ι → K) : (∃ c, ∀ x ∈ Sol R, v ⬝ᵥ x = c) ↔ v ∈ rowSpace R := by
  constructor
  · intro ⟨c, hc⟩
    by_contra hv
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    let y : ι → K := fun i => f (Pi.single i 1)
    have hfy : ∀ w, f w = w ⬝ᵥ y := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      simp only [dotProduct, y, smul_eq_mul]
      congr 1; funext i; congr 2; funext j
      by_cases h : i = j <;> simp [h, eq_comm]
    have hker : ∀ p ∈ R, p.1 ⬝ᵥ y = 0 := by
      intro p hp
      rw [← hfy]
      have : f p.1 ∈ (rowSpace R).map f := Submodule.mem_map_of_mem (Submodule.subset_span ⟨p, hp, rfl⟩)
      rw [hmap] at this
      simpa using this
    have h1 := hc x₀ hx₀
    have h2 := hc (x₀ + y) (sol_add_kernel hx₀ hker)
    rw [dotProduct_add, h1, ← hfy] at h2
    exact hf (by simpa using h2)
  · intro hv
    exact ⟨v ⬝ᵥ x₀, fun x hx => combination_holds R hv x hx x₀ hx₀⟩

/-- **Proposition 7.9, forced variables** (paper §7.5). -/
theorem forced_iff (R : Set ((ι → K) × K)) {x₀ : ι → K} (hx₀ : x₀ ∈ Sol R) (i : ι) :
    (∃ c, ∀ x ∈ Sol R, x i = c) ↔ Pi.single i 1 ∈ rowSpace R := by
  rw [← constant_iff_mem_span R hx₀]
  simp [single_dotProduct]

/-- **Proposition 7.9, pairs** (paper §7.5): over GF(2), on a non-empty affine set of solutions,
`R_AB` is functional (`B = g(A)` on every solution) iff `e_B` or `e_A + e_B` lies in the row
space, that is, iff Gauss fixes `B` from `A` (Theorem 7.7 becomes a polynomial algorithm). -/
theorem functional_iff_affine (R : Set ((ι → ZMod 2) × ZMod 2)) {x₀ : ι → ZMod 2}
    (hx₀ : x₀ ∈ Sol R) (A B : ι) :
    (∃ g : ZMod 2 → ZMod 2, ∀ x ∈ Sol R, x B = g (x A)) ↔
      Pi.single B 1 ∈ rowSpace R ∨ Pi.single A 1 + Pi.single B 1 ∈ rowSpace R := by
  have hsum : ∀ x : ι → ZMod 2, (Pi.single A 1 + Pi.single B 1) ⬝ᵥ x = x A + x B := by
    intro x; simp [add_dotProduct, single_dotProduct]
  rw [← forced_iff R hx₀, ← constant_iff_mem_span R hx₀]
  simp only [hsum]
  constructor
  · rintro ⟨g, hg⟩
    have hg' : ∀ a : ZMod 2, g a = g 0 + a * (g 1 - g 0) := by
      intro a
      fin_cases a
      · show g 0 = g 0 + 0 * _; ring
      · show g 1 = g 0 + 1 * _; ring
    by_cases h : g 1 = g 0
    · left; exact ⟨g 0, fun x hx => by rw [hg x hx, hg' (x A), h]; ring⟩
    · right
      have h1 : g 1 - g 0 = 1 := by
        have hz : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
        exact hz _ (sub_ne_zero.2 h)
      refine ⟨g 0, fun x hx => ?_⟩
      rw [hg x hx, hg' (x A), h1]
      have : x A + x A = 0 := by
        generalize x A = a; fin_cases a <;> decide
      have e : x A + (g 0 + x A * 1) = g 0 + (x A + x A) := by ring
      rw [e, this, add_zero]
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact ⟨fun _ => c, hc⟩
    · refine ⟨fun a => c - a, fun x hx => ?_⟩
      have := hc x hx
      show x B = c - x A
      rw [← this]; ring

end ArcsAlgo.Affine
