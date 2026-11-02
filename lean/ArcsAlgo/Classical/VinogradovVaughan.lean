module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false

/-!
# Vinogradov–Vaughan (cited hypothesis)

`VinogradovVaughan`: the bound of [IK, Thm 13.6] for `Σ_{n≤x} Λ(n) e(αn)`, used by Theorem E(1).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Classical

open scoped ArithmeticFunction.vonMangoldt

/-- **Vinogradov's estimate for exponential sums over primes, in Vaughan's form**
[H. Iwaniec, E. Kowalski, *Analytic Number Theory*, Thm 13.6; H. Davenport, *Multiplicative Number
Theory*, Ch. 25, (1); R. C. Vaughan, *Sommes trigonométriques sur les nombres premiers*, C. R. Acad.
Sci. Paris 285 (1977)]: there is `C` such that for `x ≥ 2`, `α ∈ ℝ` and `b/k` with `k ≥ 1`,
`(b, k) = 1`, `|α − b/k| ≤ k^{−2}`,
`|Σ_{n≤x} Λ(n) e(αn)| ≤ C (x k^{−1/2} + x^{4/5} + x^{1/2} k^{1/2}) (log x)^4`.
Stated at the integers `x`, with `b/k` a rational in lowest terms. An explicit hypothesis, never
an axiom. -/
def VinogradovVaughan : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x → ∀ (α : ℝ) (r : ℚ), |α - r| ≤ 1 / (r.den : ℝ) ^ 2 →
    ‖∑ n ∈ Icc 1 x, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (α * n))‖ ≤
      C * (x / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √(x : ℝ) * √(r.den : ℝ)) * Real.log x ^ 4

end ArcsAlgo.Classical
