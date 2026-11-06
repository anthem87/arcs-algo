module

public import Mathlib
public import ArcsAlgo

set_option autoImplicit false

/-!
# Main theorems

The index of the paper's main results: each is stated here and proved by the corresponding
theorem of `ArcsAlgo`. The definitions in the namespace `ARCS` are copied from the library and
agree with it by unfolding. Cited published theorems and numerical certificates enter as explicit
`Prop` hypotheses, never as `axiom`.
-/

set_option maxHeartbeats 4000000

@[expose] public section

namespace ARCS
open Finset
/-- `T` is a subset sum of `W`: some set of distinct indices into `W` has weights summing to `T`. -/
def IsSubsetSum (W : List ℕ) (T : ℕ) : Prop :=
  ∃ s : Finset (Fin W.length), ∑ i ∈ s, W.get i = T
/-- A YES certificate: `idx` has no repetitions, every index is `< W.length`, and the weights at those indices sum to `T`. -/
def checkYes (W : List ℕ) (T : ℕ) (idx : List ℕ) : Bool :=
  decide idx.Nodup && idx.all (· < W.length) && (idx.map fun i => W.getD i 0).sum == T
/-- Checker, YES: if `checkYes W T idx` passes, `T` is a subset sum of `W`. -/
theorem _root_.ARCS.checkYes_sound {W : List ℕ} {T : ℕ} {idx : List ℕ} (h : checkYes W T idx = true) :
    IsSubsetSum W T := by
  with_unfolding_all exact ArcsAlgo.checkYes_sound (W := W) (T := T) (idx := idx) h
/-- The initial table: only the residue `0` (of the empty subset) is reachable. -/
def initMod (q : ℕ) : Array Bool :=
  Array.ofFn fun c : Fin q => c.val == 0
/-- One step of the table for a weight `w`: residue `c` is reachable iff it was reachable before or `c - w (mod q)` was. -/
def stepMod (q w : ℕ) (a : Array Bool) : Array Bool :=
  Array.ofFn fun c : Fin q => a[c.val]! || a[(c.val + q - w % q) % q]!
/-- The table of residues mod `q` reachable by subset sums of `W`, built as in the Python checker. -/
def reachableMod (q : ℕ) (W : List ℕ) : Array Bool :=
  W.foldl (fun a w => stepMod q w a) (initMod q)
/-- A residue NO certificate `(q, c)`: `q > 0`, `T % q = c`, `c < q`, and `c` is not reachable mod `q`. -/
def checkNo (W : List ℕ) (T q c : ℕ) : Bool :=
  decide (0 < q) && T % q == c && decide (c < q) && !(reachableMod q W)[c]!
/-- Checker, NO by a residue class: if `checkNo W T q c` passes, `T` is not a subset sum of `W`. -/
theorem _root_.ARCS.checkNo_sound {W : List ℕ} {T q c : ℕ} (h : checkNo W T q c = true) :
    ¬ IsSubsetSum W T := by
  with_unfolding_all exact ArcsAlgo.checkNo_sound (W := W) (T := T) (q := q) (c := c) h
/-- The interval NO certificate `(q, c) = (0, 0)`: the target exceeds the total weight. -/
def checkRange (W : List ℕ) (T : ℕ) : Bool :=
  decide (W.sum < T)
/-- Checker, NO by range: if `checkRange W T` passes, `T` is not a subset sum of `W`. -/
theorem _root_.ARCS.checkRange_sound {W : List ℕ} {T : ℕ} (h : checkRange W T = true) :
    ¬ IsSubsetSum W T := by
  with_unfolding_all exact ArcsAlgo.checkRange_sound (W := W) (T := T) h
end ARCS
namespace ARCS
/-- One step of the centre rule (paper Lemma A (§6.1), doubled form; pseudocode `CENTRE-RULE`): take the weight (`E - w`) if this does not increase … -/
def centreStep (E : ℤ) (w : ℕ) : ℤ :=
  if |E - w| ≤ |E + w| then E - w else E + w
end ARCS
namespace ARCS
/-- All subset sums of `L`, with multiplicity, as an array (pseudocode `ALL-SUMS`): start from `[0]`; each weight `w` appends the sums shifted by `w`. -/
def allSums (L : List ℕ) : Array ℕ :=
  L.foldl (fun acc w => acc ++ acc.map (· + w)) #[0]
/-- Binary search for `x` in `s[lo‥hi)`; `s` is assumed sorted increasingly. -/
def bsearchGo (s : Array ℕ) (x : ℕ) (lo hi : ℕ) : Bool :=
  if lo < hi then
    if s.getD ((lo + hi) / 2) 0 < x then bsearchGo s x ((lo + hi) / 2 + 1) hi
    else if x < s.getD ((lo + hi) / 2) 0 then bsearchGo s x lo ((lo + hi) / 2)
    else true
  else false
termination_by hi - lo
decreasing_by all_goals omega
/-- Binary search for `x` in the sorted array `s`. -/
def bsearch (s : Array ℕ) (x : ℕ) : Bool := bsearchGo s x 0 s.size
/-- Exact decision of the subset-sum problem by meet-in-the-middle (paper §5.7; pseudocode `MITM`, `ALL-SUMS`, `SORTED-SUMS`, `JOIN`): all subset sums … -/
def existsSubsetSum (W : List ℕ) (T : ℕ) : Bool :=
  let h := W.length / 2
  let sb := (allSums (W.drop h)).mergeSort (fun a b => decide (a ≤ b))
  (allSums (W.take h)).any fun a => decide (a ≤ T) && bsearch sb (T - a)
/-- The exhaustive NO certificate `(-3, -3)` is valid when the exact search finds no subset with sum `T` (paper §5.7, *Parameters derived from the … -/
def checkExhaustiveNo (W : List ℕ) (T : ℕ) : Bool := !existsSubsetSum W T
/-- Checker, NO by exact meet-in-the-middle (code (−3, −3)): sound. -/
theorem _root_.ARCS.checkExhaustiveNo_sound {W : List ℕ} {T : ℕ} (h : checkExhaustiveNo W T = true) :
    ¬ IsSubsetSum W T := by
  with_unfolding_all exact ArcsAlgo.checkExhaustiveNo_sound (W := W) (T := T) h
/-- Checker (−3, −3): sound and complete, it passes iff `T` is not a subset sum. -/
theorem _root_.ARCS.checkExhaustiveNo_iff (W : List ℕ) (T : ℕ) :
    checkExhaustiveNo W T = true ↔ ¬ IsSubsetSum W T := by
  with_unfolding_all exact ArcsAlgo.checkExhaustiveNo_iff W T
end ARCS
namespace ARCS
open Polynomial Finset
section Cumulants
variable {K : Type*} [Field K] [CharZero K]
/-- Proposition C/C′: the first six cumulants of `w·Bernoulli(p)` (non-vanishing factor). -/
theorem _root_.ARCS.propC_bernoulli_cumulants (w p : K) :
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
  exact ArcsAlgo.bernoulli_cumulants w p
/-- Proposition C/C′: the cumulants of the vanishing factor (`w/2, w²/12, 0, −w⁴/120, 0, w⁶/252`). -/
theorem _root_.ARCS.propC_vanishing_cumulants (w : K) :
    let m : ℕ → K := fun j => w ^ j / (j + 1)
    let κ : ℕ → K := fun j =>
      match j with
      | 1 => w / 2
      | 2 => w ^ 2 / 12
      | 4 => -w ^ 4 / 120
      | 6 => w ^ 6 / 252
      | _ => 0
    ∀ n ∈ Icc 1 6, m n = ∑ k ∈ Icc 1 n, ((n - 1).choose (k - 1) : K) * κ k * m (n - k) := by
  exact ArcsAlgo.uniform_cumulants w
/-- The scaled cumulant coefficients `u_j = κ_j ε^{j−2} / j!`, `3 ≤ j ≤ 6`. -/
def uCoef (κ₃ κ₄ κ₅ κ₆ ε : K) : ℕ → K
  | 3 => κ₃ * ε / 6
  | 4 => κ₄ * ε ^ 2 / 24
  | 5 => κ₅ * ε ^ 3 / 120
  | 6 => κ₆ * ε ^ 4 / 720
  | _ => 0
/-- The coefficients `e_n` of `x^n` in `exp(Σ_{j=3}^{6} u_j x^j)`, up to `n = 12`; the powers of `ε` give the order `s^{−r}` of each term. -/
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
/-- Proposition C/C′: the Edgeworth bracket through order `s⁻⁴` (formal expansion). -/
theorem _root_.ARCS.propC_edgeworth_terms (κ₃ κ₄ κ₅ κ₆ ε : K) :
    ∀ n ∈ Icc (1 : ℕ) 12, (n : K) * eCoef κ₃ κ₄ κ₅ κ₆ ε n =
      ∑ j ∈ Icc (1 : ℕ) n, (j : K) * uCoef κ₃ κ₄ κ₅ κ₆ ε j * eCoef κ₃ κ₄ κ₅ κ₆ ε (n - j) := by
  with_unfolding_all exact ArcsAlgo.edgeworth_terms κ₃ κ₄ κ₅ κ₆ ε
end Cumulants
end ARCS
namespace ARCS
/-- The generalized Riemann hypothesis for a finite set `X` of Dirichlet characters mod `q`: every zero of `L(s, χ)`, `χ ∈ X`, with `0 < Re s < 1` has … -/
def GRHFor {q : ℕ} [NeZero q] (X : Finset (DirichletCharacter ℂ q)) : Prop :=
  ∀ χ ∈ X, ∀ s : ℂ, χ.LFunction s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2
end ARCS
namespace ARCS.Classical
open Complex Filter Topology Set MeasureTheory Asymptotics LSeries
/-- The weights on the primes: `c_p` at primes, `0` elsewhere. -/
noncomputable def primeCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ := if n.Prime then c n else 0
/-- The weighted prime count `H(x) = Σ_{p ≤ x} c_p` (paper §3.2, the height of an arc). -/
noncomputable def primeRace (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoeff c n
end ARCS.Classical
namespace ARCS.Classical
open Complex Filter Topology Set MeasureTheory Asymptotics LSeries
section Prop3
open ArithmeticFunction DirichletCharacter
variable {q : ℕ} [NeZero q]
/-- The weights of an arc on the primes are a combination of characters: `c_p = Σ_{χ∈X} A_χ χ(p)` for every prime `p` (paper §4.1, `A_χ = φ(q)^{−1} … -/
def IsCharCombination (X : Finset (DirichletCharacter ℂ q)) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (c p : ℂ) = ∑ χ ∈ X, A χ * χ p
/-- Condition (N) of Proposition 3 on the half-plane `Re s > σ₀`: at every zero of some `L(s, χ)`, `χ ∈ X`, the multiplicities do not cancel. -/
def ConditionN (X : Finset (DirichletCharacter ℂ q)) (A : DirichletCharacter ℂ q → ℂ) (σ₀ : ℝ) :
    Prop :=
  ∀ ρ : ℂ, σ₀ < ρ.re → (∃ χ ∈ X, LFunction χ ρ = 0) →
    ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) ≠ 0
end Prop3
end ARCS.Classical
namespace ARCS.Classical
open DirichletCharacter
variable {q : ℕ} [NeZero q]
/-- The units of `ZMod q`, as a finset. -/
noncomputable def unitsZMod (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun r => IsUnit r
/-- The character coefficients of a weight `w` on `ZMod q` (paper §4.1): `A_χ = φ(q)^{−1} Σ_{(r,q)=1} w_r χ(r^{−1})`, and `χ(r^{−1}) = χ̄(r)` on units. -/
noncomputable def charCoeff (w : ZMod q → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ r ∈ unitsZMod q, (w r : ℂ) * χ r⁻¹
/-- The weights on the integers: `w_{n mod q}` when `(n, q) = 1`, `0` otherwise (the primes `p ∣ q` are left out of `H_{a/q}`). -/
noncomputable def unitWeight (w : ZMod q → ℝ) (n : ℕ) : ℝ :=
  if IsUnit (n : ZMod q) then w n else 0
open _root_.Classical in
/-- The characters seen by the weights: `X = {χ ≠ χ₀ : A_χ ≠ 0}` (paper §4.1). -/
noncomputable def arcChars (w : ZMod q → ℝ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ => χ ≠ 1 ∧ charCoeff w χ ≠ 0
/-- `log|cos(π r a / q)|` for a residue `r` (represented by `r.val`). -/
noncomputable def logCos (q a : ℕ) (r : ZMod q) : ℝ :=
  Real.log |Real.cos (Real.pi * r.val * a / q)|
/-- The arc weights `c_r = log|cos(πra/q)| − w̄(q)`, with `w̄(q)` the mean over the units. -/
noncomputable def arcWeight (q : ℕ) [NeZero q] (a : ℕ) (r : ZMod q) : ℝ :=
  logCos q a r - (∑ r' ∈ unitsZMod q, logCos q a r') / (unitsZMod q).card
end ARCS.Classical
namespace ARCS.Classical
open Complex Filter Topology Set MeasureTheory Asymptotics
/-- The integrand `t^k / log t` on `t > 2`, extended by `0`. -/
noncomputable def liIntegrand (k : ℕ) (t : ℝ) : ℝ := if 2 < t then t ^ k / Real.log t else 0
/-- `Li_k(x) = ∫_2^x t^k dt / log t` for `x ≥ 2`, `0` for `x ≤ 2`. -/
noncomputable def liK (k : ℕ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, liIntegrand k t
end ARCS.Classical
namespace ARCS.Classical
open Complex Filter Topology Set MeasureTheory Asymptotics LSeries ArithmeticFunction
/-- The weights `p^k`. -/
noncomputable def powWeight (k : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ k
/-- `E_k(x) = M_k(x) − Li_k(x)`, with `M_k(x) = Σ_{p ≤ x} p^k` (paper §4.4; `li(x^{k+1})` replaced by `Li_k(x) = li(x^{k+1}) − li(2^{k+1})`). -/
noncomputable def momentError (k : ℕ) (x : ℝ) : ℝ := primeRace (powWeight k) x - liK k x
/-- Proposition 3₀, (2) ⇒ (1): an upper bound for `E_k` implies RH. -/
theorem _root_.ARCS.prop30_two_imp_RH (k : ℕ)
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      momentError k N ≤ C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) :
    RiemannHypothesis := by
  with_unfolding_all exact ArcsAlgo.Classical.prop30_two_imp_RH k h2
/-- Proposition 3₀, (3) ⇒ (1): a lower bound for `E_k` implies RH. -/
theorem _root_.ARCS.prop30_three_imp_RH (k : ℕ)
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ≤ momentError k N) :
    RiemannHypothesis := by
  with_unfolding_all exact ArcsAlgo.Classical.prop30_three_imp_RH k h3
end ARCS.Classical
namespace ARCS.Classical
open Complex DirichletCharacter
/-- Proposition 3, (2) ⇒ (1): an upper bound `N^{1/2+ε}` for the race of an arc implies GRH for its characters, under (R) and (N). -/
theorem _root_.ARCS.prop3_two_imp_GRH {q : ℕ} [NeZero q] (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      primeRace (unitWeight (arcWeight q a)) N ≤ C * (N : ℝ) ^ (1 / 2 + ε)) :
    ARCS.GRHFor (arcChars (arcWeight q a)) := by
  have hc : @ARCS.Classical.charCoeff = @ArcsAlgo.Classical.charCoeff := by with_unfolding_all rfl
  have hb : ∀ w : ZMod q → ℝ, ARCS.Classical.arcChars w = ArcsAlgo.Classical.arcChars w := by
    intro w; ext χ
    simp only [ARCS.Classical.arcChars, ArcsAlgo.Classical.arcChars, Finset.mem_filter, hc]
  rw [hb] at hR hN ⊢
  with_unfolding_all exact ArcsAlgo.Classical.prop3_arc_two_imp_GRH (q := q) a hR hN h2
/-- Proposition 3, (3) ⇒ (1): the lower bound version, under (R) and (N). -/
theorem _root_.ARCS.prop3_three_imp_GRH {q : ℕ} [NeZero q] (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(C * (N : ℝ) ^ (1 / 2 + ε)) ≤ primeRace (unitWeight (arcWeight q a)) N) :
    ARCS.GRHFor (arcChars (arcWeight q a)) := by
  have hc : @ARCS.Classical.charCoeff = @ArcsAlgo.Classical.charCoeff := by with_unfolding_all rfl
  have hb : ∀ w : ZMod q → ℝ, ARCS.Classical.arcChars w = ArcsAlgo.Classical.arcChars w := by
    intro w; ext χ
    simp only [ARCS.Classical.arcChars, ArcsAlgo.Classical.arcChars, Finset.mem_filter, hc]
  rw [hb] at hR hN ⊢
  with_unfolding_all exact ArcsAlgo.Classical.prop3_arc_three_imp_GRH (q := q) a hR hN h3
end ARCS.Classical
namespace ARCS.Classical
open Complex DirichletCharacter
section ThmSHalf
variable {q : ℕ} [NeZero q]
/-- Theorem S (general form): `Ω₊(N^θ)` for every `θ < 1/2`. -/
theorem _root_.ARCS.theoremS_omega_plus (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS_not_eventually_upper' X hX1 hXinv hXsq A c hc hR (ρ₀ := ρ₀) hρ₀ hN₀ (θ := θ) hθ
/-- Theorem S (general form): `Ω₋(N^θ)` for every `θ < 1/2`. -/
theorem _root_.ARCS.theoremS_omega_minus (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → -(C * (N : ℝ) ^ θ) ≤ primeRace c N := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS_not_eventually_lower' X hX1 hXinv hXsq A c hc hR (ρ₀ := ρ₀) hρ₀ hN₀ (θ := θ) hθ
/-- Theorem S (general form): the race changes sign infinitely often, under (R) on `[1/2, 1]` and a zero `ρ₀`. -/
theorem _root_.ARCS.theoremS_sign_changes (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0) :
    (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ 0 < primeRace c N) ∧
      (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ primeRace c N < 0) := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS_sign_changes' X hX1 hXinv hXsq A c hc hR (ρ₀ := ρ₀) hρ₀ hN₀
end ThmSHalf
end ARCS.Classical
section
open Finset DirichletCharacter
namespace ARCS.Classical
/-- **Condition (R) at `q = 14`** (certified in Arb, `python/certification/certify_L_real_segment.py`, for the cubic character mod 7; the cubic … -/
def R14 : Prop :=
  ∀ χ : DirichletCharacter ℂ 14, χ ^ 3 = 1 → χ ≠ 1 → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0
/-- **A zero on the critical line at `q = 14`** (certified in Arb, `python/certification/certify_zero_cubic7.py`: the Hardy function of the cubic … -/
def CubicZero14 : Prop :=
  ∃ χ : DirichletCharacter ℂ 14, χ ^ 3 = 1 ∧ χ ≠ 1 ∧
    ∃ t : ℝ, 4355 / 1000 ≤ t ∧ t ≤ 4357 / 1000 ∧ LFunction χ (1 / 2 + t * Complex.I) = 0
/-- Theorem S at `q = 14`: for `a` coprime to 14, `H_{a/14}(N)` changes sign infinitely often, under `R14` and `CubicZero14`. -/
theorem _root_.ARCS.theoremS14_sign_changes (hR : R14) (hZ : CubicZero14) {a : ℕ} (ha : a.Coprime 14) :
    (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ 0 < primeRace (unitWeight (arcWeight 14 a)) N) ∧
      (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ primeRace (unitWeight (arcWeight 14 a)) N < 0) := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS14_sign_changes hR hZ (a := a) ha
/-- Theorem S at `q = 14`: `H_{a/14}(N) = Ω₊(N^θ)` for every `θ < 1/2`. -/
theorem _root_.ARCS.theoremS14_omega_plus (hR : R14) (hZ : CubicZero14) {a : ℕ} (ha : a.Coprime 14)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N →
      primeRace (unitWeight (arcWeight 14 a)) N ≤ C * (N : ℝ) ^ θ := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS14_not_eventually_upper hR hZ (a := a) ha (θ := θ) hθ
/-- Theorem S at `q = 14`: `H_{a/14}(N) = Ω₋(N^θ)` for every `θ < 1/2`. -/
theorem _root_.ARCS.theoremS14_omega_minus (hR : R14) (hZ : CubicZero14) {a : ℕ} (ha : a.Coprime 14)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N →
      -(C * (N : ℝ) ^ θ) ≤ primeRace (unitWeight (arcWeight 14 a)) N := by
  with_unfolding_all exact ArcsAlgo.Classical.thmS14_not_eventually_lower hR hZ (a := a) ha (θ := θ) hθ
end ARCS.Classical
end
section
open Real Complex Finset MeasureTheory intervalIntegral
namespace ARCS.LLT
/-- The law of `S_k = w₁ + … + w_k` for independent uniform `w_i ∈ {1, …, M}`: `Pr(S_k = v) = #{w ∈ {1,…,M}^k : Σ w_i = v} / M^k`. -/
noncomputable def lawS (M k : ℕ) (v : ℤ) : ℝ :=
  ((univ.filter fun w : Fin k → Fin M => ∑ i, ((w i : ℤ) + 1) = v).card : ℝ) / (M : ℝ) ^ k
end ARCS.LLT
end
section
open Real Complex Finset MeasureTheory intervalIntegral
namespace ARCS.LLT
/-- The mean `μ = (M + 1)/2` of a uniform weight. -/
noncomputable def muW (M : ℕ) : ℝ := ((M : ℝ) + 1) / 2
/-- `σ² = (M² − 1)/12`, the variance of a uniform weight. -/
noncomputable def sig2 (M : ℕ) : ℝ := ((M : ℝ) ^ 2 - 1) / 12
end ARCS.LLT
end
section
open Finset Matrix
namespace ARCS.LLT
def sg (b : Bool) : ℤ := if b then 1 else -1
noncomputable def ew2 (M : ℕ) : ℝ := ((M : ℝ) + 1) * (2 * M + 1) / 6
def Sw {m M : ℕ} (w : Fin m → Fin M) : ℤ := ∑ i, ((w i : ℤ) + 1)
def Tsg {m M : ℕ} (w : Fin m → Fin M) (ε : Fin m → Bool) : ℤ := ∑ i, sg (ε i) * ((w i : ℤ) + 1)
/-- `Z(u) = #{ε ∈ {±1}^E : Σ ε_i w_i = u}`. -/
def Zc {m M : ℕ} (w : Fin m → Fin M) (u : ℤ) : ℕ := (univ.filter fun ε => Tsg w ε = u).card
end ARCS.LLT
end
section
open Finset Matrix
namespace ARCS.LLT
/-- `Q₀ = (s − mμ)²/(mσ²)`. -/
noncomputable def smQ0 (M m : ℕ) (s : ℤ) : ℝ := ((s : ℝ) - m * muW M) ^ 2 / m / sig2 M
/-- `Q₁ = u²/(m Ew²)`. -/
noncomputable def smQ1 (M m : ℕ) (u : ℤ) : ℝ := (u : ℝ) ^ 2 / m / ew2 M
/-- The Gaussian term for `X = (w, εw, ε′w)`, lattice index 4. -/
noncomputable def smA (M m : ℕ) (s u : ℤ) : ℝ :=
  4 * (Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) /
    (√(2 * Real.pi) ^ 3 * √(sig2 M * ew2 M * ew2 M))) / √(m : ℝ) ^ 3
/-- `#{w : S_E = s}`. -/
def cntS (M m : ℕ) (s : ℤ) : ℕ := (univ.filter fun w : Fin m → Fin M => Sw w = s).card
/-- `λ = E[Z(u) | S_E = s]`. -/
noncomputable def lamB (M m : ℕ) (s u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ)) / cntS M m s
/-- `E[Z(u)² | S_E = s]`. -/
noncomputable def m2B (M m : ℕ) (s u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2) / cntS M m s
/-- `Pr(Z(u) = 0 | S_E = s)`. -/
noncomputable def p0B (M m : ℕ) (s u : ℤ) : ℝ :=
  ((univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card : ℝ) / cntS M m s
/-- `c_M = 1/3 + 1/(2M) + 1/(6M²)`, so that `M² c_M = Ew²`. -/
noncomputable def cMB (M : ℕ) : ℝ := 1 / 3 + 1 / (2 * M) + 1 / (6 * (M : ℝ) ^ 2)
/-- `λ_m = 2^{m+1}/(M √(2π m c_M))`. -/
noncomputable def lamM (M m : ℕ) : ℝ := 2 ^ (m + 1) / (M * √(2 * Real.pi * m * cMB M))
end ARCS.LLT
end
section
open Finset
namespace ARCS.LLT
variable {m M : ℕ}
/-- The probability of an event for weights uniform in `{1, …, M}^m`. -/
noncomputable def prW (M m : ℕ) (E : (Fin m → Fin M) → Prop) [DecidablePred E] : ℝ :=
  (∑ w, if E w then (1 : ℝ) else 0) / (M : ℝ) ^ m
/-- `S_J = Σ_{i ∈ J} w_i`. -/
def SJ (J : Finset (Fin m)) (w : Fin m → Fin M) : ℤ := ∑ i ∈ J, ((w i : ℤ) + 1)
end ARCS.LLT
end
section
open Finset Real Filter Topology
namespace ARCS.LLT
/-- Lemma B(1), uniformly in `M ≥ 2`, with the rate: `|λ/λ_m − 1| ≤ C(g) m^{−1/5}`. -/
theorem _root_.ARCS.lemmaB1_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      |lamB M m s u / lamM M m - 1| ≤ C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
  with_unfolding_all exact ArcsAlgo.LLT.lemmaB1_rate (g := g) hg
end ARCS.LLT
end
section
open Finset Real Filter Topology
namespace ARCS.LLT
/-- Lemma B(2), uniformly in `M ≥ 2`, with the rate `C(g) m^{−1/5}`. -/
theorem _root_.ARCS.lemmaB2_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      m2B M m s u ≤ lamB M m s u + lamB M m s u * (if u = 0 then 1 else 0) +
        lamB M m s u ^ 2 * (1 + C * (m : ℝ) ^ (-(1 / 5 : ℝ))) := by
  with_unfolding_all exact ArcsAlgo.LLT.lemmaB2_rate (g := g) hg
/-- Lemma B(3), uniformly in `M ≥ 2`, with the rate `C(g) m^{−1/5}`. -/
theorem _root_.ARCS.lemmaB3_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      p0B M m s u ≤ 2 / lamB M m s u + C * (m : ℝ) ^ (-(1 / 5 : ℝ)) := by
  with_unfolding_all exact ArcsAlgo.LLT.lemmaB3_rate (g := g) hg
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.LLT
open ARCS
/-- The weights of the head `H`, as the list read by the centre rule. -/
def wsOf {h M : ℕ} (wH : Fin h → Fin M) : List ℕ := List.ofFn fun i => (wH i : ℕ) + 1
/-- The residual of the endgame after the centre rule on `H`, in doubled form: `u = 2t − S_E`, where `t` is the target left for `E` and `E₀ = 2T − S`. -/
def residR {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : ℤ :=
  (wsOf wH).foldl centreStep (2 * T - (((wsOf wH).sum : ℤ) + s))
/-- The hypothesis `|T − S/2| ≤ S_H/2` of Theorem R, in doubled form. -/
def condR {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : Prop :=
  |2 * T - (((wsOf wH).sum : ℤ) + s)| ≤ ((wsOf wH).sum : ℤ)
instance {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : Decidable (condR wH T s) := by
  unfold condR; infer_instance
/-- Theorem R: centre rule plus meet-in-the-middle fails with probability `≤ 2/λ* + ε + 2e^{−g²/6}`. -/
theorem _root_.ARCS.theoremR {g ε : ℝ} (hg : 0 ≤ g) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ lamS : ℝ, 0 < lamS → lamS ≤ lamM M m →
      ∀ T : (Fin h → Fin M) → ℤ → ℤ,
      ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 2 / lamS + ε + 2 * exp (-(g ^ 2 / 6)) := by
  with_unfolding_all exact ArcsAlgo.LLT.thmR (g := g) (ε := ε) hg hε
/-- Theorem R with the rate: failure probability `≤ 2/λ* + C(g) m^{−1/5} + 2e^{−g²/6}`. -/
theorem _root_.ARCS.theoremR_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ lamS : ℝ, 0 < lamS → lamS ≤ lamM M m →
      ∀ T : (Fin h → Fin M) → ℤ → ℤ,
      ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 2 / lamS + C * (m : ℝ) ^ (-(1 / 5 : ℝ)) + 2 * exp (-(g ^ 2 / 6)) := by
  with_unfolding_all exact ArcsAlgo.LLT.thmR_rate (g := g) hg
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.LLT
open ARCS
/-- The doubled hypothesis of Theorem R′: `|T − S/2| ≤ S_G/2 − rmM`. -/
def condRp {h M r : ℕ} (m : ℕ) (wG : Fin h → Fin M) (b : Fin r → ℤ) (T : ℤ) : Prop :=
  |2 * T - (((wsOf wG).sum : ℤ) + ∑ k, b k)| ≤ ((wsOf wG).sum : ℤ) - 2 * r * m * M
instance {h M r m : ℕ} (wG : Fin h → Fin M) (b : Fin r → ℤ) (T : ℤ) :
    Decidable (condRp m wG b T) := by unfold condRp; infer_instance
/-- The target of round `j`: the blocks of `K_j` are included entirely. -/
def targetRp {r : ℕ} (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) : ℤ := T - ∑ k ∈ K, b k
/-- The block sums. -/
def bsum {r m M : ℕ} (wB : Fin r → Fin m → Fin M) : Fin r → ℤ := fun j => Sw (wB j)
/-- The residual of round `j`. -/
def uRp {h M r : ℕ} (wG : Fin h → Fin M) (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) (j : Fin r) : ℤ :=
  residR wG (targetRp T b K) (b j)
/-- Theorem R′: with `r = ⌈log₂(2/δ)⌉` blocks the algorithm fails with probability `≤ δ`. -/
theorem _root_.ARCS.theoremR' {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → 8 ≤ lamM M m →
      ∀ (T : (Fin h → Fin M) → (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → ℤ) → ℤ)
        (K : Fin ⌈Real.logb 2 (2 / δ)⌉₊ → (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → ℤ) →
          Finset (Fin ⌈Real.logb 2 (2 / δ)⌉₊)),
      (∀ j b, j ∉ K j b) →
      ((univ.filter fun p : (Fin h → Fin M) × (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → Fin m → Fin M) =>
          condRp m p.1 (bsum p.2) (T p.1 (bsum p.2)) ∧
            ∀ j, Zc (p.2 j) (uRp p.1 (T p.1 (bsum p.2)) (bsum p.2) (K j (bsum p.2)) j) = 0).card : ℝ) /
        ((M : ℝ) ^ h * Fintype.card (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → Fin m → Fin M)) ≤ δ := by
  with_unfolding_all exact ArcsAlgo.LLT.thmRp (δ := δ) hδ0 hδ1
end ARCS.LLT
end
section
open Real intervalIntegral MeasureTheory
namespace ARCS.ArcM
/-- A real trigonometric polynomial of degree `≤ n`. -/
noncomputable def trigPoly (n : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (a k * cos (2 * π * k * x) + b k * sin (2 * π * k * x))
/-- **Jackson's theorem** [D. -/
def JacksonThm : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (L : ℝ), 0 ≤ L → Continuous f → (∀ x, f (x + 1) = f x) →
    (∀ x y, |f x - f y| ≤ L * |x - y|) → ∀ n : ℕ, 1 ≤ n →
    ∃ a b : ℕ → ℝ, a 0 = (∫ x in (0 : ℝ)..1, f x) ∧
      (∀ k, 1 ≤ k → |a k| ≤ 2 * ∫ x in (0 : ℝ)..1, |f x| ∧ |b k| ≤ 2 * ∫ x in (0 : ℝ)..1, |f x|) ∧
      ∀ x, |f x - trigPoly n a b x| ≤ C * L / n
end ARCS.ArcM
end
section
open Finset Real
namespace ARCS.PrimeK
open scoped Nat.Prime
/-- **Rosser–Schoenfeld bounds** [RoS: J. -/
def RosserSchoenfeld : Prop :=
  (∀ n : ℕ, 17 ≤ n → (n : ℝ) / log n < π n) ∧ (∀ n : ℕ, 2 ≤ n → (π n : ℝ) < 1.25506 * n / log n)
/-- The primes of `[P₀, 2P₀)`. -/
def primesIn (P₀ : ℕ) : Finset ℕ := (Ico P₀ (2 * P₀)).filter Nat.Prime
end ARCS.PrimeK
end
section
open Finset Real MeasureTheory intervalIntegral
namespace ARCS.Classical
/-- **von Koch's theorem** [H. -/
def VonKoch : Prop :=
  RiemannHypothesis → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |momentError 0 x| ≤ C * √x * log x
/-- Proposition 3₀, (1) ⇒ (2), (3): RH implies the bounds for `E_k`, with von Koch as hypothesis. -/
theorem _root_.ARCS.prop30_RH_imp_bounds (hK : VonKoch) (hRH : RiemannHypothesis) (k : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → momentError k N ≤ C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        -(C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ≤ momentError k N) := by
  with_unfolding_all exact ArcsAlgo.Classical.prop30_one_imp_two_three hK hRH k
/-- `π(x, χ) = Σ_{p ≤ x} χ(p)`. -/
noncomputable def piChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if n.Prime then χ n else 0
/-- **The prime sums of a character under GRH** [Davenport, *Multiplicative Number Theory*, Ch. -/
def GRHPrimeBound {q : ℕ} [NeZero q] (X : Finset (DirichletCharacter ℂ q)) : Prop :=
  ARCS.GRHFor X → ∀ χ ∈ X, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ‖piChi χ x‖ ≤ C * √x * Real.log x
/-- Proposition 3, (1) ⇒ (2), (3): GRH implies `|H(N)| ≤ C_ε N^{1/2+ε}`, with the GRH bound for `π(x, χ)` as hypothesis. -/
theorem _root_.ARCS.prop3_GRH_imp_bound {q : ℕ} [NeZero q] {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c)
    (hB : GRHPrimeBound X) (hGRH : ARCS.GRHFor X) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primeRace c N| ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  with_unfolding_all exact ArcsAlgo.Classical.prop3_one_imp_two_three (q := q) (X := X) (A := A) (c := c) hc hB hGRH (ε := ε) hε
end ARCS.Classical
end
section
open Finset Real
namespace ARCS.LLT
open ARCS.PrimeK
variable {m M : ℕ}
/-- The hits of the scheme `𝒫₁`: the `x ⊆ E` with `S_x = a`. -/
def hits (w : Fin m → Fin M) (a : ℤ) : Finset (Finset (Fin m)) := univ.filter fun x => SJ x w = a
/-- `S_{x ∩ A}`, as a natural number. -/
def halfS (A : Finset (Fin m)) (w : Fin m → Fin M) (x : Finset (Fin m)) : ℕ := (SJ (x ∩ A) w).toNat
/-- `Z_r = #{x : S_x = a, S_{x∩A} ≡ r (mod p)}`. -/
def Zr (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) (p r : ℕ) : ℕ :=
  ((hits w a).filter fun x => halfS A w x % p = r).card
/-- The live residues `R_p = {r < p : Z_r > 0}`. -/
def live (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) (p : ℕ) : ℕ :=
  ((range p).filter fun r => 0 < Zr A w a p r).card
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.LLT
open ARCS ARCS.PrimeK
variable {m M : ℕ}
/-- `Pr_{P, r}(round succeeds | weights)`: `P` uniform among the primes of `[P₀, 2P₀)`, `r` uniform in `ℤ/P`. -/
noncomputable def sPr (P₀ : ℕ) (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) : ℝ :=
  (∑ p ∈ primesIn P₀, (live A w a p : ℝ) / p) / (primesIn P₀).card
/-- The target of round `j`: `a_j = (S_{E_j} + u_j)/2`. -/
def aRp {h M r : ℕ} (wG : Fin h → Fin M) (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) (j : Fin r) : ℤ :=
  (b j + uRp wG T b K j) / 2
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.LLT
open ARCS ARCS.PrimeK
/-- `p_rate` of Theorem R″ (paper §6.7), `r = m^{−1/5}`, `ψ = 2^{m/2}/M`: `p_rate = [(2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C … -/
noncomputable def pRate (g C : ℝ) (M m P₀ : ℕ) : ℝ :=
  (2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) +
    6 * log (m * M) * (1 + 2 / lamM M m + C * (m : ℝ) ^ (-(1 / 5 : ℝ))))⁻¹ *
    (1 - C * (m : ℝ) ^ (-(1 / 5 : ℝ)))
/-- Theorem R″ with the rate: each round succeeds with probability `≥ p_rate`, `p_rate = [(2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C m^{−1/5})]⁻¹(1 − C m^{−1/5})`, and `Pr(every round fails) ≤ (1 − (1 − 2e^{−g²/6}) p_rate)^R`. -/
theorem _root_.ARCS.theoremR''_rate (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M h m R P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ →
      ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤
        (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m P₀) ^ R := by
  with_unfolding_all exact ArcsAlgo.LLT.thmRpp_rate hRS (g := g) hg
/-- Theorem R″ (paper §6.7): with m the least integer ≥ 1 with `2^m ≥ (σ√m)^{4/3}`, `P₀ = ⌊λ_m/2⌋` and `R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p_rate)⌉` rounds, the probability that `|T − S/2| ≤ S_G/2 − RmM` and every round fails is `≤ δ` for `M` large; and `p_rate ≥ (1 − o(1))/(6 ln(mM))` as `M → ∞`. -/
theorem _root_.ARCS.theoremR'' (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) (hge : 2 * exp (-(g ^ 2 / 6)) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M m : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        (1 - ε) / (6 * log (m * M)) ≤ pRate g C M m ⌊lamM M m / 2⌋₊) ∧
      ∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M h m R : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        R = ⌈log (1 / δ) / ((1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m ⌊lamM M m / 2⌋₊)⌉₊ →
        ∀ A : Finset (Fin m), A.card = m / 2 →
        ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
        (∀ j b, j ∉ K j b) →
        (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
            (if condRp m wG (bsum wB) (T wG (bsum wB)) then
              ∏ j, (1 - sPr ⌊lamM M m / 2⌋₊ A (wB j)
                (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
          ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤ δ := by
  with_unfolding_all exact ArcsAlgo.LLT.thmRpp_asymp hRS (g := g) hg hge
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.Core
/-- `e(x) = e^{2πix}`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)
/-- `F_W(e(θ)) = Π_{w ∈ W} (1 + e(wθ))`. -/
noncomputable def FW (W : Finset ℕ) (θ : ℝ) : ℂ := ∏ w ∈ W, (1 + ee (w * θ))
/-- The factor of `w` vanishes at `a/q`: `wa/q ≡ 1/2 (mod 1)`, i.e. -/
def vanish (q a w : ℕ) : Prop := (2 * q : ℤ) ∣ 2 * w * a - q
instance (q a : ℕ) : DecidablePred (vanish q a) := fun w => by unfold vanish; infer_instance
/-- The weights `W_N = {1} ∪ {p ≤ N}`. -/
def WN (N : ℕ) : Finset ℕ := (range (N + 1)).filter fun w => w = 1 ∨ w.Prime
end ARCS.Core
end
section
open Finset Real Polynomial ArithmeticFunction
namespace ARCS.Core
/-- `h_q(x) = log|Φ_q(−e(x))|`. -/
noncomputable def hq (q : ℕ) (x : ℝ) : ℝ := Real.log ‖(cyclotomic q ℂ).eval (-ee x)‖
/-- The neighbourhood level `A_q(X) = X⁻¹ ∫₀^X log|Φ_q(−e(x))| dx`. -/
noncomputable def Aq (q : ℕ) (X : ℝ) : ℝ := (∫ x in (0 : ℝ)..X, hq q x) / X
end ARCS.Core
end
section
open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius
namespace ARCS.Core
/-- The emerging moduli `𝔈`: `q = 1`, `q = 2^k` (`k ≥ 2`) and `q = 2p^j`. -/
def emerging (q : ℕ) : Prop := q = 1 ∨ (Even q ∧ IsPrimePow (q / 2))
/-- `ℓ_q` with lower end `X₀` (`ℓ_q` itself has `X₀ = X_q`, the first local minimum of `A_q`). -/
noncomputable def ellq (q : ℕ) (X₀ : ℝ) : ℝ := sSup ((fun X => Aq q X / q.totient) '' Set.Ici X₀)
end ARCS.Core
end
section
open Finset Real
namespace ARCS.Core
/-- `α_w = πwa/q`. -/
noncomputable def alw (q a w : ℕ) : ℝ := π * w * a / q
/-- `F(t) = Σ_{w ∉ 𝒱} log|2 cos(πwa/q + wt/2)|`. -/
noncomputable def Fw (W : Finset ℕ) (q a : ℕ) (t : ℝ) : ℝ :=
  ∑ w ∈ W.filter (fun w => ¬ vanish q a w), Real.log (2 * cos (alw q a w + w * t / 2))
/-- `F′(t) = −Σ_{w ∉ 𝒱} (w/2) tan(πwa/q + wt/2)`. -/
noncomputable def Fw' (W : Finset ℕ) (q a : ℕ) (t : ℝ) : ℝ :=
  -∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w / 2 : ℝ) * tan (alw q a w + w * t / 2)
/-- `ν_{a/q} = ½ Σ_{w ∉ 𝒱} w tan(πwa/q)`. -/
noncomputable def nuW (W : Finset ℕ) (q a : ℕ) : ℝ :=
  (1 / 2) * ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) * tan (alw q a w)
/-- `S₂ = Σ_{w ∉ 𝒱} w²`. -/
noncomputable def S2W (W : Finset ℕ) (q a : ℕ) : ℝ := ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) ^ 2
end ARCS.Core
end
section
open Finset Real
namespace ARCS.Core
variable {W : Finset ℕ} {q a N : ℕ}
/-- `G(θ) = Π_{w ∉ 𝒱} (1 + e(wθ))`, so that `G(a/q) = F*(a/q)`. -/
noncomputable def Gw (W : Finset ℕ) (q a : ℕ) (θ : ℝ) : ℂ :=
  ∏ w ∈ W.filter (fun w => ¬ vanish q a w), (1 + ee (w * θ))
end ARCS.Core
end
section
open Finset Real
namespace ARCS.Classical
/-- `π(m; q, r) = #{p ≤ m : p ≡ r (mod q)}`. -/
def cntQ (m q r : ℕ) : ℕ := ((range (m + 1)).filter (fun n => n.Prime ∧ n % q = r % q)).card
/-- **Siegel–Walfisz** [A. -/
def SiegelWalfisz : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → ∀ q a : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Real.log m ^ B → a.Coprime q →
      |(cntQ m q a : ℝ) - liK 0 m / q.totient| ≤ C * m * Real.exp (-c * √(Real.log m))
end ARCS.Classical
end
section
open Finset Real Polynomial
namespace ARCS.Core
open ARCS.Classical
/-- `𝔓 = (log N)^B`. -/
noncomputable def PP (B : ℝ) (N : ℕ) : ℝ := Real.log N ^ B
/-- `R_{a/q}(T) = ∫_{𝔐(a/q)} F_N(e(θ)) e(−Tθ) dθ`, `𝔐(a/q) = {|θ − a/q| ≤ 𝔓/(qN)}`. -/
noncomputable def Rarc (B : ℝ) (N q a : ℕ) (T : ℝ) : ℂ :=
  ∫ θ in ((a : ℝ) / q - PP B N / (q * N))..((a : ℝ) / q + PP B N / (q * N)), FW (WN N) θ * ee (-(T * θ))
end ARCS.Core
end
section
open Finset Real
namespace ARCS.Classical
open scoped ArithmeticFunction.vonMangoldt
/-- **Vinogradov's estimate for exponential sums over primes, in Vaughan's form** [H. -/
def VinogradovVaughan : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x → ∀ (α : ℝ) (r : ℚ), |α - r| ≤ 1 / (r.den : ℝ) ^ 2 →
    ‖∑ n ∈ Icc 1 x, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * (α * n))‖ ≤
      C * (x / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √(x : ℝ) * √(r.den : ℝ)) * Real.log x ^ 4
end ARCS.Classical
end
section
open Finset Real
namespace ARCS.Core
open ARCS.Classical ARCS.ArcM
open scoped ArithmeticFunction.vonMangoldt
/-- The minor arcs `𝔪`: `θ ∉ 𝔐(r)` for every rational `r` with denominator `≤ 𝔓`. -/
def minorArc (B : ℝ) (N : ℕ) (θ : ℝ) : Prop :=
  ∀ r : ℚ, (r.den : ℝ) ≤ PP B N → PP B N / (r.den * N) < |θ - r|
end ARCS.Core
end
section
open Finset Complex Polynomial Nat
namespace ARCS.Edge
/-- The Taylor coefficients `c_n = ψ^{(n)}(0)/n!`: `c₁ = p`, `c₂ = p(1−p)/2`, `c₃ = p(1−p)(1−2p)/6`, `c₄ = p(1−p)(1−6p+6p²)/24`, `c₅ = … -/
noncomputable def cB (p : ℂ) : ℕ → ℂ
  | 1 => p
  | 2 => p * (1 - p) / 2
  | 3 => p * (1 - p) * (1 - 2 * p) / 6
  | 4 => p * (1 - p) * (1 - 6 * p + 6 * p ^ 2) / 24
  | 5 => p * (1 - p) * (1 - 2 * p) * (1 - 12 * p + 12 * p ^ 2) / 120
  | _ => 0
end ARCS.Edge
end
section
open Complex MeasureTheory Real
namespace ARCS.Edge
/-- `g_ξ(v) = e^{−v²/2 − iξv}`. -/
noncomputable def gE (ξ v : ℝ) : ℂ := Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v)
/-- The probabilists' Hermite polynomials `He₀, …, He₆`. -/
noncomputable def He : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun z => z
  | 2 => fun z => z ^ 2 - 1
  | 3 => fun z => z ^ 3 - 3 * z
  | 4 => fun z => z ^ 4 - 6 * z ^ 2 + 3
  | 5 => fun z => z ^ 5 - 10 * z ^ 3 + 15 * z
  | 6 => fun z => z ^ 6 - 15 * z ^ 4 + 45 * z ^ 2 - 15
  | _ => fun _ => 0
/-- The standard normal density `φ(z) = e^{−z²/2}/√(2π)`. -/
noncomputable def phiN (z : ℝ) : ℝ := Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * π)
end ARCS.Edge
end
section
open Finset Complex MeasureTheory Nat
open scoped Real
namespace ARCS.Edge
/-- The cumulants `κ_j = Σ_w w^j j! c_j(p_w)` of `Σ_w w·Bernoulli(p_w)` (Proposition C). -/
noncomputable def kap (W : Finset ℕ) (p : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ w ∈ W, (w : ℂ) ^ j * (j ! : ℂ) * cB (p w) j
/-- The pointwise error polynomial of the core. -/
noncomputable def Eb (α3 α4 α5 ρ x : ℝ) : ℝ :=
  2 / 9 * (4 * α3 ^ 3 * x ^ 9 + 16 * α4 ^ 3 * x ^ 12 + 64 * α5 ^ 3 * x ^ 15 + 64 * ρ ^ 3 * x ^ 18) +
    α5 * x ^ 5 + ρ * x ^ 6 + α3 * α4 * x ^ 7 + α3 * α5 * x ^ 8 + α3 * ρ * x ^ 9 + α4 ^ 2 * x ^ 8 +
    2 * α5 ^ 2 * x ^ 10 + 2 * ρ ^ 2 * x ^ 12
/-- The Edgeworth integrand `e^{iκ₁σ − s²σ²/2}(1 + κ₃(iσ)³/6 + κ₄(iσ)⁴/24 + κ₃²(iσ)⁶/72)`. -/
noncomputable def edgeI (k1 s : ℝ) (κ₃ κ₄ : ℂ) (σ : ℝ) : ℂ :=
  Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) *
    (1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72)
/-- The Edgeworth arc term `φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`, `z = (T − κ₁)/s` (Proposition C, Theorem E(2)). -/
noncomputable def mainE (k1 s : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) : ℂ :=
  ((phiN ((T - k1) / s) / s : ℝ) : ℂ) *
    (1 + κ₃ * (He 3 ((T - k1) / s) : ℂ) / (6 * (s : ℂ) ^ 3) + κ₄ * (He 4 ((T - k1) / s) : ℂ) / (24 * (s : ℂ) ^ 4) +
      κ₃ ^ 2 * (He 6 ((T - k1) / s) : ℂ) / (72 * (s : ℂ) ^ 6))
end ARCS.Edge
end
section
open Finset Complex MeasureTheory
open scoped Real
namespace ARCS.Core
open ARCS.Edge ARCS.Classical
/-- `p_w = u/(1 + u)`, `u = e(wθ*)`: the parameter of the factor of `w` at `θ*`. -/
noncomputable def pStar (θs : ℝ) (w : ℕ) : ℂ := ee (w * θs) / (1 + ee (w * θs))
/-- The cumulants `κ_j*` of Proposition C at `θ*` (Lemma W(3)). -/
noncomputable def kS (N : ℕ) (θs : ℝ) (j : ℕ) : ℂ := kap (WN N) (pStar θs) j
/-- `s* = √κ₂*` (κ₂* is real and positive at the peak, Lemma W(3)). -/
noncomputable def sS (N : ℕ) (θs : ℝ) : ℝ := Real.sqrt (kS N θs 2).re
/-- `Ĥ(T) = e^{−iTt*} G(θ*) φ(z)/s*·(1 + κ₃*He₃(z)/(6s*³) + κ₄*He₄(z)/(24s*⁴) + κ₃*²He₆(z)/(72s*⁶))`. -/
noncomputable def Hhat (N : ℕ) (ts θs T : ℝ) : ℂ :=
  Complex.exp (-(I * T * ts)) * FW (WN N) θs *
    mainE (kS N θs 1).re (sS N θs) (kS N θs 3) (kS N θs 4) T
end ARCS.Core
end
section
open Finset Complex Nat Metric
open scoped Real ComplexConjugate
namespace ARCS.Edge
/-- `g(x) = (e^x − 1)/x`, `g(0) = 1`; `g(iwt) = e^{iwt/2} sinc(wt/2)`. -/
noncomputable def gS (z : ℂ) : ℂ := dslope (fun z => Complex.exp z - 1) 0 z
/-- `ψ(x) = log((e^x − 1)/x)`: the cumulant generating function of `Uniform[0, 1]`. -/
noncomputable def psiS (z : ℂ) : ℂ := Complex.log (gS z)
/-- The cumulants of the vanishing factor `e^{iwt/2} sinc(wt/2) = g(iwt)` at `t*`: `λ_n = w^n ψ^{(n)}(iwt*)`. -/
noncomputable def lamS (w : ℕ) (ts : ℝ) (n : ℕ) : ℂ := (w : ℂ) ^ n * iteratedDeriv n psiS (I * w * ts)
end ARCS.Edge
end
section
open Complex MeasureTheory Real
namespace ARCS.Edge
/-- `g_ξ(v) = e^{−v²/2 − iξv}`, complex `ξ`. -/
noncomputable def gEC (ξ : ℂ) (v : ℝ) : ℂ := Complex.exp (-(v : ℂ) ^ 2 / 2 - I * ξ * v)
/-- The Hermite polynomials `He₀, …, He₇` over `ℂ`. -/
noncomputable def HeC : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | 1 => fun z => z
  | 2 => fun z => z ^ 2 - 1
  | 3 => fun z => z ^ 3 - 3 * z
  | 4 => fun z => z ^ 4 - 6 * z ^ 2 + 3
  | 5 => fun z => z ^ 5 - 10 * z ^ 3 + 15 * z
  | 6 => fun z => z ^ 6 - 15 * z ^ 4 + 45 * z ^ 2 - 15
  | 7 => fun z => z ^ 7 - 21 * z ^ 5 + 105 * z ^ 3 - 105 * z
  | _ => fun _ => 0
/-- The normal density `φ(z) = e^{−z²/2}/√(2π)` at complex `z`. -/
noncomputable def phiC (z : ℂ) : ℂ := Complex.exp (-z ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ)
/-- The Edgeworth integrand `e^{iκ₁σ − s²σ²/2}(1 + κ₃(iσ)³/6 + κ₄(iσ)⁴/24 + κ₃²(iσ)⁶/72)`, complex `κ₁`. -/
noncomputable def edgeIC (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (σ : ℝ) : ℂ :=
  Complex.exp (I * k1 * σ - (s : ℂ) ^ 2 * σ ^ 2 / 2) *
    (1 + κ₃ * (I * σ) ^ 3 / 6 + κ₄ * (I * σ) ^ 4 / 24 + κ₃ ^ 2 * (I * σ) ^ 6 / 72)
/-- The Edgeworth arc term `φ(z)/s·(1 + κ₃He₃(z)/(6s³) + κ₄He₄(z)/(24s⁴) + κ₃²He₆(z)/(72s⁶))`, `z = (T − κ₁)/s`, complex `κ₁`. -/
noncomputable def mainEC (k1 : ℂ) (s : ℝ) (κ₃ κ₄ : ℂ) (T : ℝ) : ℂ :=
  phiC ((T - k1) / s) / s * (1 + κ₃ * HeC 3 ((T - k1) / s) / (6 * (s : ℂ) ^ 3) +
    κ₄ * HeC 4 ((T - k1) / s) / (24 * (s : ℂ) ^ 4) + κ₃ ^ 2 * HeC 6 ((T - k1) / s) / (72 * (s : ℂ) ^ 6))
end ARCS.Edge
end
section
open Finset Complex MeasureTheory
open scoped Real
namespace ARCS.Core
open ARCS.Edge ARCS.Classical
/-- The weights whose factor does not vanish at `a/q`. -/
noncomputable def Wv (N q a : ℕ) : Finset ℕ := (WN N).filter (fun w => ¬ vanish q a w)
/-- The cumulants of `G̃ = G·e^{iw₀t/2} sinc(w₀t/2)` at `t*`: those of `G` (Proposition C, weights `∉ 𝒱`) plus those of the vanishing factor, `λ_j = … -/
noncomputable def kV (N q a w₀ : ℕ) (ts : ℝ) (j : ℕ) : ℂ :=
  kap (Wv N q a) (pStar ((a : ℝ) / q + ts / (2 * π))) j + if j = 0 then 0 else lamS w₀ ts j
/-- `s̃* = √κ̃₂*` (`κ̃₂*` is real, `kV_two_real`). -/
noncomputable def sV (N q a w₀ : ℕ) (ts : ℝ) : ℝ := Real.sqrt (kV N q a w₀ ts 2).re
/-- `G̃(θ*) = G(θ*) e^{iw₀t*/2} sinc(w₀t*/2)`. -/
noncomputable def GtV (N q a w₀ : ℕ) (ts : ℝ) : ℂ :=
  Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π)) * gS (I * w₀ * ts)
/-- `Ĥ(T)` built from `G̃`: `e^{−iTt*} G̃(θ*) φ(z)/s̃*·(1 + κ̃₃He₃(z)/(6s̃*³) + κ̃₄He₄(z)/(24s̃*⁴) + κ̃₃²He₆(z)/(72s̃*⁶))`, `z = (T − κ̃₁*)/s̃*` … -/
noncomputable def HhatV (N q a w₀ : ℕ) (ts T : ℝ) : ℂ :=
  Complex.exp (-(I * T * ts)) * GtV N q a w₀ ts *
    mainEC (kV N q a w₀ ts 1) (sV N q a w₀ ts) (kV N q a w₀ ts 3) (kV N q a w₀ ts 4) T
end ARCS.Core
end
section
open Finset Complex MeasureTheory
open scoped Real
namespace ARCS.Core
open ARCS.Edge ARCS.Classical ARCS.ArcM
/-- Theorem E (arc expansion), with Siegel–Walfisz, Vinogradov–Vaughan and Jackson as hypotheses. -/
theorem _root_.ARCS.theoremE (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 40 < B)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ θ : ℝ, minorArc B N θ →
        ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 + δ) * Nat.primeCounting N)) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((∀ w ∈ WN N, ¬ vanish q a w) →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sS N ((a : ℝ) / q + ts / (2 * π)) +
                5 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))) ∧
        (∀ w₀ ∈ WN N, vanish q a w₀ →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              (w₀ * (|ts| + 1 / sV N q a w₀ ts) * ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sV N q a w₀ ts) +
                w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
                4 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)))) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q → ¬ emerging q → ∀ T : ℝ,
        ‖Rarc B N q a T‖ ≤
          2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  with_unfolding_all exact ArcsAlgo.Core.thmE hSW hVV hJ (B := B) hB (ε := ε) hε0 hε (δ := δ) hδ
end ARCS.Core
end
section
open Finset Real
open scoped ArithmeticFunction.vonMangoldt
namespace ARCS.Core
open ARCS.Edge ARCS.Classical
/-- `X_q` is a first local minimum of `A_q`: a local minimum with none in `(0, X_q)`. -/
def firstLocalMin (q : ℕ) (X : ℝ) : Prop :=
  0 < X ∧ IsLocalMin (Aq q) X ∧ ∀ y ∈ Set.Ioo 0 X, ¬ IsLocalMin (Aq q) y
/-- Theorem E(3): for `q ∉ 𝔈` and a first local minimum `X_q` of `A_q`, the exponent `ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q)` used in `theoremE` equals `ℓ_q = sup_{X ≥ X_q} A_q(X)/φ(q)`. -/
theorem _root_.ARCS.theoremE_lobe_exponent {q : ℕ} (h3 : 3 ≤ q) (hne : ¬ emerging q) {Xq : ℝ} (hX : firstLocalMin q Xq) :
    ellq q (1 / (2 * q)) = ellq q Xq := by
  with_unfolding_all exact ArcsAlgo.Core.ellE_eq_ellq (q := q) h3 hne (Xq := Xq) hX
end ARCS.Core
end
section
open Finset Real MeasureTheory Set
namespace ARCS.LLT
variable {m M : ℕ}
/-- `E cos⁴(πwθ)` for `w` uniform in `{1, …, M}`. -/
noncomputable def rhoLV (M : ℕ) (θ : ℝ) : ℝ := (∑ c : Fin M, Real.cos (π * (((c : ℕ) : ℝ) + 1) * θ) ^ 4) / M
end ARCS.LLT
end
section
open Finset Real
namespace ARCS.LLT
variable {m M : ℕ}
/-- `Pr(Z(u) = 0 | S_E = s)`. -/
noncomputable def condZ0 (M m : ℕ) (u s : ℤ) : ℝ :=
  prW M m (fun w => Zc w u = 0 ∧ Sw w = s) / lawS M m s
/-- **The certified rate of Theorem LV** (`lv_rate_certified.py`, paper §6.6): for every `M ≥ 2` and `θ ∈ 𝔅`, `E cos⁴(πwθ) ≤ 0.44495`. -/
def LVRhoCert : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ θ : ℝ, 1 / (2 * (M : ℝ)) ≤ θ → θ ≤ 1 / 2 - 1 / (4 * (M : ℝ)) → rhoLV M θ ≤ 0.44495
/-- Theorem LV: exponential tail of `Pr(Z(u) = 0 | S_E = s)`, with the certificate `LVRhoCert` as hypothesis. -/
theorem _root_.ARCS.theoremLV (hcert : LVRhoCert) {g : ℝ} (hg : 0 ≤ g) :
    ∃ m₀ : ℕ, ∃ C : ℝ, ∀ b : ℕ, 1 ≤ b → ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW (2 ^ b)| ≤ g * √(sig2 (2 ^ b)) * √(m : ℝ) → |(u : ℝ)| ≤ (2 ^ b : ℕ) →
      (∃ a, 2 * a = s + u) →
      condZ0 (2 ^ b) m u s ≤ C * ((m : ℝ) ^ ((5 : ℝ) / 2) * ((2 ^ b : ℕ) : ℝ) ^ 5 * 0.446 ^ m +
        (2 : ℝ) ^ (-(53 / 100 : ℝ) * m)) := by
  with_unfolding_all exact ArcsAlgo.LLT.thmLV hcert (g := g) hg
end ARCS.LLT
end
section
open Finset
namespace ARCS.LLT
variable {M : ℕ}
/-- The raw moments `m_k = E w^k` of `w` uniform in `{1, …, M}`. -/
noncomputable def mw (M k : ℕ) : ℝ := (∑ a : Fin M, ((a : ℝ) + 1) ^ k) / M
end ARCS.LLT
end
section
open Finset
namespace ARCS.LLT
variable {M : ℕ}
/-- `Var(w) = E w² − (E w)²`. -/
noncomputable def varW (M : ℕ) : ℝ := mw M 2 - mw M 1 ^ 2
/-- `Var(w²) = E w⁴ − (E w²)²`. -/
noncomputable def varW2 (M : ℕ) : ℝ := mw M 4 - mw M 2 ^ 2
/-- `Cov(w², w) = E w³ − E w² E w`. -/
noncomputable def covW (M : ℕ) : ℝ := mw M 3 - mw M 2 * mw M 1
/-- `κ = Var(w²)/(4(E w²)²)`. -/
noncomputable def kapB (M : ℕ) : ℝ := varW2 M / (4 * mw M 2 ^ 2)
/-- `A = Var(w²) − Cov(w², w)²/Var(w)`. -/
noncomputable def AB (M : ℕ) : ℝ := varW2 M - covW M ^ 2 / varW M
/-- `κ_c = A/(4(E w²)²)`. -/
noncomputable def kapcB (M : ℕ) : ℝ := AB M / (4 * mw M 2 ^ 2)
/-- `β = Cov(w, w²)/(Var(w) E w²)`. -/
noncomputable def betaB (M : ℕ) : ℝ := covW M / (varW M * mw M 2)
/-- `R = w² − E w² − (Cov(w², w)/Var(w))(w − μ)`. -/
noncomputable def RB (M : ℕ) (w : ℝ) : ℝ := w ^ 2 - mw M 2 - covW M / varW M * (w - mw M 1)
/-- `B = E[R²(w − μ)]/Var(w)`. -/
noncomputable def BB (M : ℕ) : ℝ :=
  (∑ a : Fin M, RB M (((a : ℕ) : ℝ) + 1) ^ 2 * (((a : ℕ) : ℝ) + 1 - mw M 1)) / M / varW M
/-- `γ_M = σ(B − 2βA)/(4(E w²)²)`. -/
noncomputable def gamB (M : ℕ) : ℝ := √(sig2 M) * (BB M - 2 * betaB M * AB M) / (4 * mw M 2 ^ 2)
end ARCS.LLT
end
section
open Finset Filter Topology
namespace ARCS.LLT
/-- Proposition B′: for `w` uniform on `{1, …, M}`, `κ_M → 1/5` as `M → ∞`. -/
theorem _root_.ARCS.propB'_kappa_limit : Tendsto kapB atTop (𝓝 (1 / 5)) := by
  with_unfolding_all exact ArcsAlgo.LLT.kapB_tendsto
/-- Proposition B′: `κ_{c,M} → 1/80` as `M → ∞`. -/
theorem _root_.ARCS.propB'_kappa_c_limit : Tendsto kapcB atTop (𝓝 (1 / 80)) := by
  with_unfolding_all exact ArcsAlgo.LLT.kapcB_tendsto
/-- Proposition B′: `γ_M → −√3/80` as `M → ∞`. -/
theorem _root_.ARCS.propB'_gamma_limit : Tendsto gamB atTop (𝓝 (-(√3 / 80))) := by
  with_unfolding_all exact ArcsAlgo.LLT.gamB_tendsto
end ARCS.LLT
end
end
