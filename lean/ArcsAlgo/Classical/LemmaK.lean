module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.BigOperators.Associated
set_option autoImplicit false

/-!
# Lemma K: a random prime (paper §6.6)

`lemmaK`: for `P` uniform among the primes of `[P₀, 2P₀)`, `P₀ ≥ 100`, and every integer `Δ ≠ 0`
with `|Δ| ≤ X`, `E[P·1[P | Δ]] ≤ 6 ln X`.

* `card_div_le`: the primes `≥ P₀` dividing `Δ` number at most `ln|Δ|/ln P₀` (their product
  divides `Δ`).
* `card_primesIn_ge`: `#primes in [P₀, 2P₀) ≥ P₀/(3 ln P₀)` for `P₀ ≥ 100`.

**Hypothesis.** The Rosser–Schoenfeld bounds `π(n) > n/ln n` (`n ≥ 17`), `π(n) < 1.25506 n/ln n`
(`RosserSchoenfeld`, cited [RoS 1962]). Mathlib's Chebyshev bounds and Bertrand's postulate are too
weak for the count of primes in `[P₀, 2P₀)`. A `Prop`, never an axiom.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.PrimeK

open scoped Nat.Prime

/-- **Rosser–Schoenfeld bounds** [RoS: J. B. Rosser, L. Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois J. Math. 6 (1962), Cor. 1, (3.2) and (3.5)], at the integers:
`π(n) > n/ln n` for `n ≥ 17` and `π(n) < 1.25506 n/ln n` for `n > 1`. Mathlib's Chebyshev bounds
(`Chebyshev.theta_ge`, `Chebyshev.theta_le_log4_mul_x`) do not separate `π(2P₀)` from `π(P₀)`. An
explicit hypothesis, never an axiom. -/
def RosserSchoenfeld : Prop :=
  (∀ n : ℕ, 17 ≤ n → (n : ℝ) / log n < π n) ∧ (∀ n : ℕ, 2 ≤ n → (π n : ℝ) < 1.25506 * n / log n)

/-- The primes of `[P₀, 2P₀)`. -/
def primesIn (P₀ : ℕ) : Finset ℕ := (Ico P₀ (2 * P₀)).filter Nat.Prime

/-- `E[P·1[P | Δ]]` for `P` uniform among the primes of `[P₀, 2P₀)`. -/
noncomputable def expPdiv (P₀ : ℕ) (Δ : ℤ) : ℝ :=
  (∑ p ∈ primesIn P₀, if (p : ℤ) ∣ Δ then (p : ℝ) else 0) / (primesIn P₀).card

theorem card_primesIn (P₀ : ℕ) : (primesIn P₀).card + π' P₀ = π' (2 * P₀) := by
  unfold primesIn Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, ← card_union_of_disjoint]
  · congr 1; ext p; simp only [mem_union, mem_filter, mem_Ico, mem_range]
    by_cases hp : p.Prime <;> simp [hp] <;> omega
  · rw [disjoint_left]; intro p; simp only [mem_filter, mem_Ico, mem_range]; omega

theorem log_100_gt : 4 < log 100 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  have h4 : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have : exp 1 ^ 4 < 2.7182818286 ^ 4 := pow_lt_pow_left₀ this (exp_pos 1).le (by norm_num)
  linarith [show (2.7182818286 : ℝ) ^ 4 < 100 by norm_num]

/-- **Many primes in `[P₀, 2P₀)`** (paper §6.6, proof of Lemma K): `#primes ≥ P₀/(3 ln P₀)` for
`P₀ ≥ 100`, from the Rosser–Schoenfeld bounds. -/
theorem card_primesIn_ge (hRS : RosserSchoenfeld) {P₀ : ℕ} (hP : 100 ≤ P₀) :
    (P₀ : ℝ) / (3 * log P₀) ≤ (primesIn P₀).card := by
  obtain ⟨h1, h2⟩ := hRS
  have hP' : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
  have hl : 4 < log P₀ := lt_of_lt_of_le log_100_gt (log_le_log (by norm_num) hP')
  have hl2 : log (2 * P₀) = log 2 + log P₀ := log_mul (by norm_num) (by positivity)
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hA := h1 (2 * P₀) (by omega)
  have hB := h2 P₀ (by omega)
  have hc := card_primesIn P₀
  -- `π'(2P₀) = π(2P₀)` since `2P₀` is not prime, and `π'(P₀) ≤ π(P₀)`
  have e1 : π' (2 * P₀) = π (2 * P₀) := by
    have : ¬ Nat.Prime (2 * P₀) := Nat.not_prime_mul (by norm_num) (by omega)
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    unfold Nat.primeCounting'
    rw [Nat.count_succ]; simp [this]
  have e2 : π' P₀ ≤ π P₀ := Nat.monotone_primeCounting' (Nat.le_succ P₀)
  have hcR : ((primesIn P₀).card : ℝ) ≥ (π (2 * P₀) : ℝ) - π P₀ := by
    have : (primesIn P₀).card + π P₀ ≥ π (2 * P₀) := by omega
    have : ((primesIn P₀).card : ℝ) + π P₀ ≥ π (2 * P₀) := by exact_mod_cast this
    linarith
  push_cast at hA
  have hlp : 0 < log P₀ := by linarith
  have hl2p : 0 < log (2 * (P₀ : ℝ)) := by rw [hl2]; linarith
  have key : (P₀ : ℝ) / (3 * log P₀) ≤ 2 * P₀ / log (2 * P₀) - 1.25506 * P₀ / log P₀ := by
    rw [hl2]
    have hP0 : (0 : ℝ) < P₀ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have e : (2 * (P₀ : ℝ) / (log 2 + log P₀) - 1.25506 * P₀ / log P₀) * (3 * log P₀) =
        P₀ * (6 * log P₀ / (log 2 + log P₀) - 3 * 1.25506) := by
      field_simp; ring
    rw [e]
    have : 1 + 3 * 1.25506 ≤ 6 * log P₀ / (log 2 + log P₀) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  linarith

/-- The primes `≥ P₀` dividing `Δ ≠ 0` are at most `ln|Δ|/ln P₀`. -/
theorem card_div_le {P₀ : ℕ} (hP : 2 ≤ P₀) {Δ : ℤ} (hΔ : Δ ≠ 0) :
    (((primesIn P₀).filter fun p : ℕ => (p : ℤ) ∣ Δ).card : ℝ) * log P₀ ≤ log |(Δ : ℝ)| := by
  set D := (primesIn P₀).filter fun p : ℕ => (p : ℤ) ∣ Δ
  have hdvd : ∏ p ∈ D, p ∣ Δ.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp; simp only [D, primesIn, mem_filter] at hp; exact hp.1.2.prime
    · intro p hp; simp only [D, mem_filter] at hp; exact Int.natCast_dvd.mp hp.2
  have hle : ∏ p ∈ D, p ≤ Δ.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hΔ) hdvd
  have hge : P₀ ^ D.card ≤ ∏ p ∈ D, p := by
    rw [← prod_const]
    exact prod_le_prod' fun p hp => by
      simp only [D, primesIn, mem_filter, mem_Ico] at hp; exact hp.1.1.1
  have h : (P₀ : ℝ) ^ D.card ≤ |(Δ : ℝ)| := by
    have : P₀ ^ D.card ≤ Δ.natAbs := hge.trans hle
    have h' : ((P₀ ^ D.card : ℕ) : ℝ) ≤ (Δ.natAbs : ℝ) := by exact_mod_cast this
    rw [Nat.cast_natAbs, Int.cast_abs] at h'
    push_cast at h'; exact h'
  have hP0 : (0 : ℝ) < P₀ := by exact_mod_cast (by omega : 0 < P₀)
  have := log_le_log (by positivity) h
  rwa [log_pow] at this

/-- **Lemma K (a random prime)** (paper §6.6), with the Rosser–Schoenfeld bounds as the only (cited)
hypothesis: for `P` uniform among the primes of `[P₀, 2P₀)`, `P₀ ≥ 100`, and every integer
`Δ ≠ 0` with `|Δ| ≤ X`, `E[P·1[P | Δ]] ≤ 6 ln X`. -/
theorem lemmaK (hRS : RosserSchoenfeld) {P₀ : ℕ} (hP : 100 ≤ P₀) {Δ : ℤ} (hΔ : Δ ≠ 0) {X : ℝ}
    (hX : |(Δ : ℝ)| ≤ X) : expPdiv P₀ Δ ≤ 6 * log X := by
  have hN := card_primesIn_ge hRS hP
  have hP' : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
  have hl : 4 < log P₀ := lt_of_lt_of_le log_100_gt (log_le_log (by norm_num) hP')
  have hNp : 0 < ((primesIn P₀).card : ℝ) := lt_of_lt_of_le (by positivity) hN
  set D := (primesIn P₀).filter fun p : ℕ => (p : ℤ) ∣ Δ
  have hD := card_div_le (P₀ := P₀) (by omega) hΔ
  have hΔ1 : 1 ≤ |(Δ : ℝ)| := by
    have : (1 : ℤ) ≤ |Δ| := Int.one_le_abs hΔ
    exact_mod_cast this
  have hlX : log |(Δ : ℝ)| ≤ log X := log_le_log (by linarith) hX
  have hsum : (∑ p ∈ primesIn P₀, if (p : ℤ) ∣ Δ then (p : ℝ) else 0) ≤ D.card * (2 * P₀) := by
    rw [← sum_filter]
    calc ∑ p ∈ D, (p : ℝ) ≤ ∑ _p ∈ D, (2 * (P₀ : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          simp only [D, primesIn, mem_filter, mem_Ico] at hp
          have : p ≤ 2 * P₀ := hp.1.1.2.le
          exact_mod_cast this
      _ = D.card * (2 * P₀) := by rw [sum_const, nsmul_eq_mul]
  unfold expPdiv
  rw [div_le_iff₀ hNp]
  have hDl : (D.card : ℝ) ≤ log X / log P₀ := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hlX0 : 0 ≤ log X := le_trans (log_nonneg hΔ1) hlX
  calc (∑ p ∈ primesIn P₀, if (p : ℤ) ∣ Δ then (p : ℝ) else 0) ≤ D.card * (2 * P₀) := hsum
    _ ≤ log X / log P₀ * (2 * P₀) := by gcongr
    _ = 6 * log X * ((P₀ : ℝ) / (3 * log P₀)) := by field_simp; ring
    _ ≤ 6 * log X * (primesIn P₀).card := by gcongr

end ArcsAlgo.PrimeK
