module

public import ArcsAlgo.Classical.Prop30
public import Mathlib.NumberTheory.AbelSummation
public import ArcsAlgo.PrimeRaces
public import ArcsAlgo.Classical.ArcProp3
set_option autoImplicit false

/-!
# Propositions 3 and 3₀, directions (1) ⇒ (2), (3) (paper §4.2, §4.4)

* `momentError_abel`: `E_k(x) = x^k E_0(x) − k∫_0^x t^{k−1} E_0(t) dt`, from Abel summation
  (`moment_abel`, Mathlib's `sum_mul_eq_sub_integral_mul`) and integration by parts of `Li_k`
  (`liK_ibp`).
* `prop30_one_imp_two_three`: under the Riemann hypothesis, `|E_k(N)| ≤ C_ε N^{k+1/2+ε}` for every
  `k ≥ 0` and `ε > 0`, given von Koch's theorem `π(x) − Li(x) = O(√x log x)` (`VonKoch`, cited).
* `prop3_one_imp_two_three`: if `c_p = Σ_{χ∈X} A_χ χ(p)` and GRH holds for `X`, then
  `|H(N)| ≤ C_ε N^{1/2+ε}`, given `π(x, χ) = O(√x log x)` under GRH (`GRHPrimeBound`, cited
  [Davenport, Ch. 20]).

The Riemann hypothesis and GRH appear only as antecedents of these cited theorems and of the
conclusions; they are never assumed or stated as facts.
-/

open Finset Real MeasureTheory intervalIntegral

@[expose] public section

namespace ArcsAlgo.Classical

/-- **von Koch's theorem** [H. von Koch, *Sur la distribution des nombres premiers*, Acta Math. 24
(1901); Davenport, *Multiplicative Number Theory*, Ch. 18], from the explicit formula: under the
Riemann hypothesis, `π(x) − ∫_2^x dt/log t = O(√x log x)`. Cited classical theorem, an explicit
hypothesis, never an axiom; the Riemann hypothesis is only its antecedent. -/
def VonKoch : Prop :=
  RiemannHypothesis → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |momentError 0 x| ≤ C * √x * log x

theorem primeRace_pow_eq (k : ℕ) (b : ℝ) :
    primeRace (powWeight k) b = ∑ n ∈ Icc 0 ⌊b⌋₊, (n : ℝ) ^ k * primeCoeff (powWeight 0) n := by
  unfold primeRace
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simp only [primeCoeff, powWeight, Nat.not_prime_zero, if_false, mul_zero, zero_add]
  rw [show Icc 1 ⌊b⌋₊ = Ioc 0 ⌊b⌋₊ by ext; simp; omega]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

theorem primeRace_zero_eq (t : ℝ) :
    primeRace (powWeight 0) t = ∑ n ∈ Icc 0 ⌊t⌋₊, primeCoeff (powWeight 0) n := by
  unfold primeRace
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simp only [primeCoeff, powWeight, Nat.not_prime_zero, if_false, zero_add]
  rw [show Icc 1 ⌊t⌋₊ = Ioc 0 ⌊t⌋₊ by ext; simp; omega]

/-- Abel summation: `M_k(b) = b^k π(b) − k∫_0^b t^{k−1} π(t) dt`. -/
theorem moment_abel (k : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    primeRace (powWeight k) b = b ^ k * primeRace (powWeight 0) b -
      ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * primeRace (powWeight 0) t := by
  have hd : ∀ t, deriv (fun t : ℝ => t ^ k) t = k * t ^ (k - 1) := fun t => by simp
  have hdf : deriv (fun t : ℝ => t ^ k) = fun t => (k : ℝ) * t ^ (k - 1) := funext hd
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ k)) (Set.Icc 0 b) := by
    rw [hdf]; exact (by fun_prop : Continuous fun t : ℝ => (k : ℝ) * t ^ (k - 1)).integrableOn_Icc
  have h := sum_mul_eq_sub_integral_mul (primeCoeff (powWeight 0)) (f := fun t : ℝ => t ^ k) hb
    (fun t _ => differentiableAt_pow k) hint
  rw [primeRace_pow_eq, h, primeRace_zero_eq, intervalIntegral.integral_of_le hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [hd, primeRace_zero_eq]

theorem liK_zero_of_le {k : ℕ} {t : ℝ} (ht : t ≤ 2) : liK k t = 0 := liK_of_le_two k ht

/-- Integration by parts: `Li_k(b) = b^k Li_0(b) − k∫_0^b t^{k−1} Li_0(t) dt`. -/
theorem liK_ibp (k : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    liK k b = b ^ k * liK 0 b - ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * liK 0 t := by
  have hc : Continuous fun t : ℝ => (k * t ^ (k - 1)) * liK 0 t := by
    have := continuous_liK 0; fun_prop
  rcases le_or_gt b 2 with h2 | h2
  · rw [liK_zero_of_le h2, liK_zero_of_le h2, mul_zero, zero_sub]
    have : ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * liK 0 t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
        rw [Set.uIcc_of_le hb] at ht
        simp only; rw [liK_zero_of_le (ht.2.trans h2), mul_zero]]
      simp
    rw [this, neg_zero]
  · -- split at `2`
    have e0 : ∫ t in (0 : ℝ)..2, (k * t ^ (k - 1)) * liK 0 t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
        rw [Set.uIcc_of_le (by norm_num)] at ht
        simp only; rw [liK_zero_of_le ht.2, mul_zero]]
      simp
    have hsplit := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 2)
      (hc.intervalIntegrable (μ := volume) 2 b)
    -- FTC on `[2, b]` for `t^k Li_0(t)`
    have hftc : ∫ t in (2 : ℝ)..b, ((k * t ^ (k - 1)) * liK 0 t + liIntegrand k t) =
        b ^ k * liK 0 b - 2 ^ k * liK 0 2 := by
      apply integral_eq_sub_of_hasDerivAt_of_le h2.le
      · exact ((continuous_pow k).mul (continuous_liK 0)).continuousOn
      · intro t ht
        have h1 := (hasDerivAt_pow k t).mul (hasDerivAt_liK 0 ht.1)
        convert h1 using 1
        unfold liIntegrand; rw [if_pos ht.1, if_pos ht.1]; push_cast; field_simp
      · exact (hc.intervalIntegrable _ _).add (intervalIntegrable_liIntegrand k _ _)
    rw [integral_add (hc.intervalIntegrable _ _) (intervalIntegrable_liIntegrand k _ _),
      liK_zero_of_le (le_refl 2), mul_zero, sub_zero] at hftc
    have hliK : liK k b = ∫ t in (2 : ℝ)..b, liIntegrand k t := by
      unfold liK
      rw [← integral_add_adjacent_intervals (intervalIntegrable_liIntegrand k 0 2)
        (intervalIntegrable_liIntegrand k 2 b)]
      have : ∫ t in (0 : ℝ)..2, liIntegrand k t = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
          rw [Set.uIcc_of_le (by norm_num)] at ht
          simp only [liIntegrand]; rw [if_neg (not_lt.mpr ht.2)]]
        simp
      rw [this, zero_add]
    rw [hliK, ← hsplit, e0, zero_add]
    linarith

/-- `E_k(b) = b^k E_0(b) − k∫_0^b t^{k−1} E_0(t) dt`. -/
theorem momentError_abel (k : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    momentError k b = b ^ k * momentError 0 b -
      ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * momentError 0 t := by
  have hmono : Monotone (primeRace (powWeight 0)) := by
    intro x y hxy
    unfold primeRace
    apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.floor_le_floor hxy))
    intro n _ _; exact primeCoeff_pow_nonneg 0 n
  have hi1 : IntervalIntegrable (fun t : ℝ => (k * t ^ (k - 1)) * primeRace (powWeight 0) t) volume 0 b :=
    (hmono.intervalIntegrable (a := 0) (b := b)).continuousOn_mul
      (by fun_prop : Continuous fun t : ℝ => (k : ℝ) * t ^ (k - 1)).continuousOn
  have hi2 : IntervalIntegrable (fun t : ℝ => (k * t ^ (k - 1)) * liK 0 t) volume 0 b := by
    have := continuous_liK 0
    exact (by fun_prop : Continuous fun t : ℝ => (k * t ^ (k - 1)) * liK 0 t).intervalIntegrable _ _
  unfold momentError
  rw [moment_abel k hb, liK_ibp k hb]
  have : ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * (primeRace (powWeight 0) t - liK 0 t) =
      (∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * primeRace (powWeight 0) t) -
        ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * liK 0 t := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  rw [this]; ring

theorem momentError_zero_small {t : ℝ} (ht : t < 2) : momentError 0 t = 0 := by
  unfold momentError
  rw [liK_zero_of_le ht.le, sub_zero]
  unfold primeRace
  apply sum_eq_zero
  intro n hn
  simp only [mem_Icc] at hn
  have : n ≤ 1 := by
    have := Nat.floor_le_floor (R := ℝ) ht.le
    have h2 : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    have h3 : ⌊t⌋₊ < 2 := by
      rw [Nat.floor_lt' (by norm_num)]; exact_mod_cast ht
    omega
  simp only [primeCoeff]
  rw [if_neg]; intro hp; have := hp.two_le; omega

/-- **Proposition 3₀, (1) ⇒ (2) and (3)** (paper §4.4), with von Koch's theorem as the only (cited)
hypothesis: under the Riemann hypothesis, for every `k ≥ 0` and `ε > 0`,
`|E_k(N)| ≤ C_ε N^{k+1/2+ε}` for `N ≥ 2`. -/
theorem prop30_one_imp_bound (hK : VonKoch) (hRH : RiemannHypothesis) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |momentError k N| ≤ C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := hK hRH
  refine ⟨(k + 1) * C / ε, fun N hN => ?_⟩
  set b : ℝ := (N : ℝ) with hbdef
  have hb2 : (2 : ℝ) ≤ b := by rw [hbdef]; exact_mod_cast hN
  have hb0 : 0 < b := by linarith
  have hlogb : 0 ≤ log b := log_nonneg (by linarith)
  -- `|E_0(t)| ≤ C√b log b` on `[0, b]`
  have hE0 : ∀ t ∈ Set.uIcc 0 b, |momentError 0 t| ≤ C * √b * log b := by
    intro t ht
    rw [Set.uIcc_of_le hb0.le] at ht
    rcases lt_or_ge t 2 with h | h
    · rw [momentError_zero_small h, abs_zero]; positivity
    · refine (hC t h).trans ?_
      have h1 : √t ≤ √b := Real.sqrt_le_sqrt ht.2
      have h2 : log t ≤ log b := log_le_log (by linarith) ht.2
      have h3 : 0 ≤ log t := log_nonneg (by linarith)
      have := mul_le_mul h1 h2 h3 (Real.sqrt_nonneg _)
      nlinarith
  have hint : |∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * momentError 0 t| ≤
      (k * b ^ (k - 1) * (C * √b * log b)) * |b - 0| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hb0.le] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k),
      abs_of_nonneg (pow_nonneg ht.1.le _)]
    have hpow : t ^ (k - 1) ≤ b ^ (k - 1) := pow_le_pow_left₀ ht.1.le ht.2 _
    have hE := hE0 t (by rw [Set.uIcc_of_le hb0.le]; exact ⟨ht.1.le, ht.2⟩)
    have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    calc (k : ℝ) * t ^ (k - 1) * |momentError 0 t| ≤ k * b ^ (k - 1) * |momentError 0 t| := by gcongr
      _ ≤ k * b ^ (k - 1) * (C * √b * log b) := by gcongr
  rw [momentError_abel k hb0.le]
  have hsb : √b * √b = b := Real.mul_self_sqrt hb0.le
  have hpowk : b ^ (k - 1) * b = b ^ k ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · right; exact h
    · left; rw [← pow_succ]; congr 1; omega
  -- `|E_k(b)| ≤ (k + 1) C b^{k+1/2} log b`
  have hmain : |b ^ k * momentError 0 b - ∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * momentError 0 t| ≤
      (k + 1) * C * (b ^ k * √b) * log b := by
    have h1 : |b ^ k * momentError 0 b| ≤ b ^ k * (C * √b * log b) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hE0 b (by rw [Set.uIcc_of_le hb0.le]; exact ⟨hb0.le, le_refl b⟩))
        (by positivity)
    have h2 : (k * b ^ (k - 1) * (C * √b * log b)) * |b - 0| = k * C * (b ^ k * √b) * log b := by
      rw [sub_zero, abs_of_pos hb0]
      rcases hpowk with h | h
      · rw [← h]; ring
      · rw [h]; simp
    calc _ ≤ |b ^ k * momentError 0 b| + |∫ t in (0 : ℝ)..b, (k * t ^ (k - 1)) * momentError 0 t| :=
          abs_sub _ _
      _ ≤ b ^ k * (C * √b * log b) + k * C * (b ^ k * √b) * log b := by rw [← h2]; exact add_le_add h1 hint
      _ = (k + 1) * C * (b ^ k * √b) * log b := by ring
  refine hmain.trans ?_
  -- `log b ≤ b^ε/ε`
  have hl : log b ≤ b ^ ε / ε := log_le_rpow_div hb0.le hε
  have hpow : b ^ k * √b * b ^ ε = b ^ ((k : ℝ) + 1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
  calc (k + 1) * C * (b ^ k * √b) * log b ≤ (k + 1) * C * (b ^ k * √b) * (b ^ ε / ε) := by
        gcongr
    _ = (k + 1) * C / ε * b ^ ((k : ℝ) + 1 / 2 + ε) := by
        rw [← hpow]; field_simp

/-- **Proposition 3₀, (1) ⇒ (2), (3)** in the paper's form. -/
theorem prop30_one_imp_two_three (hK : VonKoch) (hRH : RiemannHypothesis) (k : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → momentError k N ≤ C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        -(C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ≤ momentError k N) := by
  constructor
  · intro ε hε
    obtain ⟨C, hC⟩ := prop30_one_imp_bound hK hRH k hε
    exact ⟨C, fun N hN => (le_abs_self _).trans (hC N hN)⟩
  · intro ε hε
    obtain ⟨C, hC⟩ := prop30_one_imp_bound hK hRH k hε
    exact ⟨C, fun N hN => by have := hC N hN; rw [abs_le] at this; exact this.1⟩

end ArcsAlgo.Classical

namespace ArcsAlgo.Classical

/-- `π(x, χ) = Σ_{p ≤ x} χ(p)`. -/
noncomputable def piChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if n.Prime then χ n else 0

/-- **The prime sums of a character under GRH** [Davenport, *Multiplicative Number Theory*, Ch. 20,
with partial summation]: under the generalized Riemann hypothesis for `χ ∈ X`,
`π(x, χ) = O(√x log x)`. Cited classical theorem, an explicit hypothesis, never an axiom; GRH is
only its antecedent. -/
def GRHPrimeBound {q : ℕ} [NeZero q] (X : Finset (DirichletCharacter ℂ q)) : Prop :=
  ArcsAlgo.GRHFor X → ∀ χ ∈ X, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ‖piChi χ x‖ ≤ C * √x * Real.log x

/-- **Proposition 3, (1) ⇒ (2) and (3)** (paper §4.2), with the GRH bound for `π(x, χ)` as the only
(cited) hypothesis: if `c_p = Σ_{χ∈X} A_χ χ(p)` and GRH holds for `X`, then
`|H(N)| ≤ C_ε N^{1/2+ε}` for every `ε > 0`. -/
theorem prop3_one_imp_two_three {q : ℕ} [NeZero q] {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c)
    (hB : GRHPrimeBound X) (hGRH : ArcsAlgo.GRHFor X) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primeRace c N| ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  classical
  have hb := hB hGRH
  choose! Cχ hCχ0 hCχ using hb
  set K := ∑ χ ∈ X, ‖A χ‖ * Cχ χ
  have hK : 0 ≤ K := Finset.sum_nonneg fun χ hχ => mul_nonneg (norm_nonneg _) (hCχ0 χ hχ)
  refine ⟨K / ε, fun N hN => ?_⟩
  set b : ℝ := (N : ℝ) with hbdef
  have hb2 : (2 : ℝ) ≤ b := by rw [hbdef]; exact_mod_cast hN
  have hb0 : 0 < b := by linarith
  have hexp : ((primeRace c b : ℝ) : ℂ) = ∑ χ ∈ X, A χ * piChi χ b := by
    unfold primeRace piChi primeCoeff
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hp
    · rw [hc n hp]
    · simp
  have hle : |primeRace c b| ≤ K * (√b * Real.log b) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hexp]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun χ hχ => ?_
    rw [norm_mul]
    have := hCχ χ hχ b hb2
    calc ‖A χ‖ * ‖piChi χ b‖ ≤ ‖A χ‖ * (Cχ χ * √b * Real.log b) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖A χ‖ * Cχ χ * (√b * Real.log b) := by ring
  refine hle.trans ?_
  have hl : Real.log b ≤ b ^ ε / ε := Real.log_le_rpow_div hb0.le hε
  have hpow : √b * b ^ ε = b ^ ((1 : ℝ) / 2 + ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb0]
  calc K * (√b * Real.log b) ≤ K * (√b * (b ^ ε / ε)) := by gcongr
    _ = K / ε * b ^ ((1 : ℝ) / 2 + ε) := by rw [← hpow]; field_simp

end ArcsAlgo.Classical
