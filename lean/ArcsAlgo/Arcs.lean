module

public import ArcsAlgo.Blur
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
set_option autoImplicit false

/-!
# The arcs of the prime product: algebraic parts (paper §3.1, §3.4)

* Remark 3.1: `eval_F` (`F(ζ) = Σ_T r(T) ζ^T`), `amplitude_vanishing` (if `F = (1 + z^w) F*` and
  `ζ^w = −1`, then `ζ F′(ζ) = −w F*(ζ)`), `X_mul_derivative_eval` (`ζ F′(ζ) = Σ_T T r(T) ζ^T`).
* Propositions C and C′: `bernoulli_cumulants` (the cumulants `κ₁, …, κ₆` of `w·Bernoulli(p)`)
  and `uniform_cumulants` (those of the uniform law on `[0, w]`: `w/2, w²/12, 0, −w⁴/120, 0,
  w⁶/252`), both as the solutions of the moment–cumulant relations
  `m_n = Σ_{k=1}^{n} C(n−1, k−1) κ_k m_{n−k}` (a triangular system, which determines them).
* `edgeworth_terms`: the coefficients of `exp(Σ_{j=3}^{6} κ_j ε^{j−2} x^j / j!)` up to `x^{12}`,
  through the recursion `n e_n = Σ_j j u_j e_{n−j}` that characterizes the exponential; the terms
  of order `ε^r` (`s^{−r}`), `r ≤ 4`, are those of Propositions C and C′.
-/

@[expose] public section

namespace ArcsAlgo

open Polynomial Finset

/-! ### Remark 3.1 -/

theorem natDegree_F_le (W : List ℕ) : (F W).natDegree ≤ W.sum := by
  induction W with
  | nil => simp [F]
  | cons w W ih =>
    simp only [F, List.map_cons, List.prod_cons, List.sum_cons] at ih ⊢
    refine (natDegree_mul_le).trans (Nat.add_le_add ?_ ih)
    refine (natDegree_add_le _ _).trans ?_
    simp

/-- **Remark 3.1** (paper §3.1): `F_W(ζ) = Σ_{T=0}^{S} r_W(T) ζ^T` exactly, for every `ζ`. -/
theorem eval_F (W : List ℕ) (ζ : ℂ) :
    (F W).eval₂ (Int.castRingHom ℂ) ζ = ∑ T ∈ range (W.sum + 1), (count W T : ℂ) * ζ ^ T := by
  rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_F_le W))]
  simp [coeff_F]

/-- **Remark 3.1, the vanishing factor** (paper §3.1): if `F = (1 + z^w) F*` and `ζ^w = −1`, then
`ζ F′(ζ) = −w F*(ζ)`. -/
theorem amplitude_vanishing (G : ℂ[X]) (w : ℕ) (ζ : ℂ) (hζ : ζ ^ w = -1) :
    ζ * ((1 + X ^ w) * G).derivative.eval ζ = -(w : ℂ) * G.eval ζ := by
  have hw : w ≠ 0 := by rintro rfl; norm_num at hζ
  rw [derivative_mul, derivative_add, derivative_one, zero_add, derivative_X_pow]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one, hζ, add_neg_cancel, zero_mul,
    add_zero]
  have : ζ * ζ ^ (w - 1) = ζ ^ w := by
    rw [← pow_succ']; congr 1; omega
  calc ζ * ((w : ℂ) * ζ ^ (w - 1) * G.eval ζ) = (w : ℂ) * (ζ * ζ ^ (w - 1)) * G.eval ζ := by ring
    _ = -(w : ℂ) * G.eval ζ := by rw [this, hζ]; ring

/-- **Remark 3.1, the first moment** (paper §3.1): `ζ F′(ζ) = Σ_T T r(T) ζ^T`, so when a factor
vanishes the amplitude is a Fourier coefficient of `T · r(T)`. -/
theorem X_mul_derivative_eval (p : ℂ[X]) (ζ : ℂ) (n : ℕ) (hn : p.natDegree < n) :
    ζ * p.derivative.eval ζ = ∑ T ∈ range n, (T : ℂ) * p.coeff T * ζ ^ T := by
  rw [eval_eq_sum_range' (p := derivative p) (n := n) (by have := natDegree_derivative_le p; omega)]
  rw [Finset.mul_sum]
  rcases n with _ | n
  · omega
  rw [Finset.sum_range_succ' (fun T => (T : ℂ) * p.coeff T * ζ ^ T)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hlast : p.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Finset.sum_range_succ (fun T => ζ * ((derivative p).coeff T * ζ ^ T))]
  rw [coeff_derivative, hlast, zero_mul, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_derivative, pow_succ]
  push_cast
  ring

/-! ### Propositions C and C′: cumulants -/

section Cumulants

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- **Propositions C and C′, non-vanishing factor** (paper §3.4): the cumulants of `w·Bernoulli(p)`
(moments `m₀ = 1`, `m_j = w^j p`) are `κ₁ = wp`, `κ₂ = w²p(1 − p)`, `κ₃ = w³p(1 − p)(1 − 2p)`,
`κ₄ = w⁴p(1 − p)(1 − 6p + 6p²)`, `κ₅ = w⁵p(1 − p)(1 − 2p)(1 − 12p + 12p²)`,
`κ₆ = w⁶p(1 − p)(1 − 30p + 150p² − 240p³ + 120p⁴)`: they solve the moment–cumulant relations
`m_n = Σ_{k=1}^{n} C(n−1, k−1) κ_k m_{n−k}`, `n = 1, …, 6`. -/
theorem bernoulli_cumulants (w p : K) :
    let m : ℕ → K := fun j => if j = 0 then 1 else w ^ j * p
    let κ : ℕ → K := fun j =>
      match j with
      | 1 => w * p
      | 2 => w ^ 2 * p * (1 - p)
      | 3 => w ^ 3 * p * (1 - p) * (1 - 2 * p)
      | 4 => w ^ 4 * p * (1 - p) * (1 - 6 * p + 6 * p ^ 2)
      | 5 => w ^ 5 * p * (1 - p) * (1 - 2 * p) * (1 - 12 * p + 12 * p ^ 2)
      | 6 => w ^ 6 * p * (1 - p) * (1 - 30 * p + 150 * p ^ 2 - 240 * p ^ 3 + 120 * p ^ 4)
      | _ => 0
    ∀ n ∈ Icc 1 6, m n = ∑ k ∈ Icc 1 n, ((n - 1).choose (k - 1) : K) * κ k * m (n - k) := by
  intro m κ n hn
  simp only [mem_Icc] at hn
  obtain ⟨h1, h6⟩ := hn
  interval_cases n <;> simp [m, κ, Finset.sum_Icc_succ_top, Nat.choose] <;> ring

/-- **Propositions C and C′, vanishing factor** (paper §3.4): `e^{iwt/2} sinc(wt/2)` is the
characteristic function of the uniform law on `[0, w]` (moments `w^j/(j + 1)`), whose cumulants
are `w/2, w²/12, 0, −w⁴/120, 0, w⁶/252` (`w⁶ B₆/6` with `B₆ = 1/42`). -/
theorem uniform_cumulants (w : K) :
    let m : ℕ → K := fun j => w ^ j / (j + 1)
    let κ : ℕ → K := fun j =>
      match j with
      | 1 => w / 2
      | 2 => w ^ 2 / 12
      | 4 => -w ^ 4 / 120
      | 6 => w ^ 6 / 252
      | _ => 0
    ∀ n ∈ Icc 1 6, m n = ∑ k ∈ Icc 1 n, ((n - 1).choose (k - 1) : K) * κ k * m (n - k) := by
  intro m κ n hn
  simp only [mem_Icc] at hn
  obtain ⟨h1, h6⟩ := hn
  interval_cases n <;> simp [m, κ, Finset.sum_Icc_succ_top, Nat.choose] <;> ring

/-! ### The Edgeworth terms -/

/-- The scaled cumulant coefficients `u_j = κ_j ε^{j−2} / j!`, `3 ≤ j ≤ 6`. -/
def uCoef (κ₃ κ₄ κ₅ κ₆ ε : K) : ℕ → K
  | 3 => κ₃ * ε / 6
  | 4 => κ₄ * ε ^ 2 / 24
  | 5 => κ₅ * ε ^ 3 / 120
  | 6 => κ₆ * ε ^ 4 / 720
  | _ => 0

/-- The coefficients `e_n` of `x^n` in `exp(Σ_{j=3}^{6} u_j x^j)`, up to `n = 12`; the powers of
`ε` give the order `s^{−r}` of each term. -/
def eCoef (κ₃ κ₄ κ₅ κ₆ ε : K) : ℕ → K
  | 0 => 1
  | 3 => κ₃ * ε / 6
  | 4 => κ₄ * ε ^ 2 / 24
  | 5 => κ₅ * ε ^ 3 / 120
  | 6 => κ₃ ^ 2 * ε ^ 2 / 72 + κ₆ * ε ^ 4 / 720
  | 7 => κ₃ * κ₄ * ε ^ 3 / 144
  | 8 => (κ₄ ^ 2 / 1152 + κ₃ * κ₅ / 720) * ε ^ 4
  | 9 => κ₃ ^ 3 * ε ^ 3 / 1296 + (κ₃ * κ₆ / 4320 + κ₄ * κ₅ / 2880) * ε ^ 5
  | 10 => κ₃ ^ 2 * κ₄ * ε ^ 4 / 1728 + (κ₄ * κ₆ / 17280 + κ₅ ^ 2 / 28800) * ε ^ 6
  | 11 => (κ₃ ^ 2 * κ₅ / 8640 + κ₃ * κ₄ ^ 2 / 6912) * ε ^ 5 + κ₅ * κ₆ * ε ^ 7 / 86400
  | 12 => κ₃ ^ 4 * ε ^ 4 / 31104 +
      (κ₃ ^ 2 * κ₆ / 51840 + κ₃ * κ₄ * κ₅ / 17280 + κ₄ ^ 3 / 82944) * ε ^ 6 + κ₆ ^ 2 * ε ^ 8 / 1036800
  | _ => 0

/-- **Propositions C and C′, the Edgeworth terms** (paper §3.4): the coefficients `e_n` of
`exp(U)`, `U = Σ_{j=3}^{6} κ_j ε^{j−2} x^j / j!`, are the solution of the recursion
`n e_n = Σ_j j u_j e_{n−j}` (`E′ = U′E`, which characterizes `E = exp U`), for `n ≤ 12`. Reading
`x^n` as `He_n(z)` and `ε` as `s^{−1}`, the terms of order `s^{−1}`, …, `s^{−4}` are:
`κ₃/6 He₃`; `κ₄/24 He₄ + κ₃²/72 He₆`; `κ₅/120 He₅ + κ₃κ₄/144 He₇ + κ₃³/1296 He₉`;
`κ₆/720 He₆ + (κ₄²/1152 + κ₃κ₅/720) He₈ + κ₃²κ₄/1728 He₁₀ + κ₃⁴/31104 He₁₂` (the last two lines
are Proposition C′). The cumulants `κ_j` with `j ≥ 7` enter only at order `s^{−5}` and beyond. -/
theorem edgeworth_terms (κ₃ κ₄ κ₅ κ₆ ε : K) :
    ∀ n ∈ Icc (1 : ℕ) 12, (n : K) * eCoef κ₃ κ₄ κ₅ κ₆ ε n =
      ∑ j ∈ Icc (1 : ℕ) n, (j : K) * uCoef κ₃ κ₄ κ₅ κ₆ ε j * eCoef κ₃ κ₄ κ₅ κ₆ ε (n - j) := by
  intro n hn
  simp only [mem_Icc] at hn
  obtain ⟨h1, h12⟩ := hn
  interval_cases n <;> simp [eCoef, uCoef, Finset.sum_Icc_succ_top] <;> ring

end Cumulants

end ArcsAlgo
