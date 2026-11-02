module

public import ArcsAlgo.Classical.LogIntegral
public import Mathlib.NumberTheory.Real.Irrational
set_option autoImplicit false

/-!
# Siegel–Walfisz (cited hypothesis)

`cntQ m q r = π(m; q, r)` and the hypothesis `SiegelWalfisz`, used by Lemmas L, W and Theorem E.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Classical

/-- `π(m; q, r) = #{p ≤ m : p ≡ r (mod q)}`. -/
def cntQ (m q r : ℕ) : ℕ := ((range (m + 1)).filter (fun n => n.Prime ∧ n % q = r % q)).card

theorem cntQ_le (m q r : ℕ) : (cntQ m q r : ℝ) ≤ m + 1 := by
  have := card_filter_le (range (m + 1)) (fun n => n.Prime ∧ n % q = r % q)
  rw [card_range] at this; unfold cntQ; exact_mod_cast this

/-! ### Siegel–Walfisz -/

/-- **Siegel–Walfisz** [A. Walfisz, *Zur additiven Zahlentheorie II*, Math. Z. 40 (1936);
H. Davenport, *Multiplicative Number Theory*, Ch. 22, (4); Iwaniec–Kowalski Cor. 5.29]: for every
`B > 0` there are `c > 0` and `C` such that for `x ≥ 2`, `1 ≤ q ≤ (log x)^B` and `(a, q) = 1`,
`|π(x; q, a) − li(x)/φ(q)| ≤ C x e^{−c√log x}`, `li(x) = ∫_2^x dt/log t`. Stated at the integers
`x = m`. The constants `c`, `C` are only asserted to exist (they are ineffective, by Siegel's
theorem). This is the form used in the paper (proofs of Lemmas L, W and Theorem E), uniformly in
`q ≤ (log x)^B`. An explicit hypothesis, never an axiom. -/
def SiegelWalfisz : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → ∀ q a : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Real.log m ^ B → a.Coprime q →
      |(cntQ m q a : ℝ) - liK 0 m / q.totient| ≤ C * m * Real.exp (-c * √(Real.log m))

end ArcsAlgo.Classical
