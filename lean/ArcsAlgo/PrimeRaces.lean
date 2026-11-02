module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
set_option autoImplicit false

/-!
# Prime races on the arcs: the hypotheses (paper §4)

Mathlib defines `RiemannHypothesis`. Next to it we define the generalized Riemann hypothesis for
a finite set of Dirichlet characters, in the same style: every zero of `L(s, χ)` in the critical
strip `0 < Re s < 1` lies on `Re s = 1/2`. (Restricting to the strip excludes the trivial zeros
and, for imprimitive characters, the zeros of the missing Euler factors on `Re s = 0`.)

The statements of §4 (Proposition 3, Theorem S, Proposition 3₀) are formalized in
`ArcsAlgo.Classical`: Landau's theorem is proved (`Landau`, `LandauZeros`); the directions that need
an explicit formula take a published theorem as an explicit hypothesis (`GRHPrimeBound` for
Proposition 3, `VonKoch` for Proposition 3₀, in `Prop3One`); the numerical inputs (condition (R), a
zero on the critical line) are hypotheses certified in Arb (`FunctionalEquation`, `TheoremS14`).
-/

@[expose] public section

namespace ArcsAlgo

/-- The generalized Riemann hypothesis for a finite set `X` of Dirichlet characters mod `q`:
every zero of `L(s, χ)`, `χ ∈ X`, with `0 < Re s < 1` has `Re s = 1/2`. -/
def GRHFor {q : ℕ} [NeZero q] (X : Finset (DirichletCharacter ℂ q)) : Prop :=
  ∀ χ ∈ X, ∀ s : ℂ, χ.LFunction s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Consistency of the definition: for the (only) character mod `1`, `L(s, χ) = ζ(s)`, and the
Riemann hypothesis gives `GRHFor` for it. -/
theorem grhFor_modOne_of_RH (h : RiemannHypothesis) : GRHFor (Finset.univ : Finset (DirichletCharacter ℂ 1)) := by
  intro χ _ s hs h0 h1
  rw [DirichletCharacter.LFunction_modOne_eq] at hs
  refine h s hs ?_ ?_
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    simp at h1

end ArcsAlgo
