module

public import ArcsAlgo.LemmaQ
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Totient
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.Compact
set_option autoImplicit false

/-!
# Corollary Q′: the largest lobe (paper §3.3)

* `omega_le_totient`: `2^{ω(q)} q^{0.7} ≤ 16 φ(q)` for all `q ≥ 1` (local factors
  `max(1, 2p^{0.7}/(p − 1))`, equal to `1` for `p ≥ 17`, product over `p ≤ 13` at most `16`;
  the paper's `M_{0.70} ≤ 15.1372`).
* `growth_20001`, `Rq_small`: `R_q ≤ 1/10` for `q > 20000`.
* `tail_Aq`: `X A_q(X) ≤ κσ(q)`, `σ(q) = Σ_{d∣q, μ(q/d)≠0} 1/d`; `Aq_cont`: `A_q` is continuous on
  `X > 0`.
* `ArbLobes`, `Arb3`: the certificate `certify_lobes_arb.py` (Arb, 128 bits, output `lobes_arb.txt`),
  as explicit hypotheses: the finite range `4 ≤ q ≤ 20000` (either `R_q < T` or the interval method
  on `[1/(2q), X*_q]`), and for `q = 3` three point values, `A_3(29/40)/2 ≥ 0.131593` and the interval
  method on `[1/6, κσ(3)/(2·0.132469)]`. The threshold is `T = A_3(29/40)/2` itself.
* `RqArb_eq`: the certificate's `R_q` equals the right side of Lemma Q(2) at `X = 1/(2q)`.
* `corQprime`, `corQprime_ell`: every non-emerging `q ≥ 4` has `sup_{X ≥ 1/(2q)} A_q(X)/φ(q) < T`,
  while `T ≤ ℓ_3 ≤ 0.132469` and `A_3` has a local minimum in `(1/5, 21/100)`; so
  `sup_{q∉𝔈} ℓ_q = ℓ_3 ∈ [0.131593, 0.132469]`.
-/

open Finset Real ArithmeticFunction

open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

@[expose] public section

namespace ArcsAlgo.Core

/-! ### Powers `x^{k/10}` against rationals -/

theorem rpow_tenth_le {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (k : ℕ) (h : x ^ k ≤ b ^ 10) :
    x ^ ((k : ℝ) / 10) ≤ b := by
  have e : (x ^ ((k : ℝ) / 10)) ^ 10 = x ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  exact (pow_le_pow_iff_left₀ (n := 10) (by positivity) hb (by norm_num)).mp (by rw [e]; exact h)

theorem le_rpow_tenth {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (k : ℕ) (h : b ^ 10 ≤ x ^ k) :
    b ≤ x ^ ((k : ℝ) / 10) := by
  have e : (x ^ ((k : ℝ) / 10)) ^ 10 = x ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  exact (pow_le_pow_iff_left₀ (n := 10) hb (by positivity) (by norm_num)).mp (by rw [e]; exact h)

/-! ### `2^{ω(q)} q^{0.7} ≤ 16 φ(q)` -/

/-- The local factor `max(1, 2p^{0.7}/(p − 1))`. -/
noncomputable def cP (p : ℕ) : ℝ := max 1 (2 * (p : ℝ) ^ ((7 : ℝ) / 10) / ((p : ℝ) - 1))

theorem one_le_cP (p : ℕ) : 1 ≤ cP p := le_max_left _ _

theorem cP_eq_one {p : ℕ} (hp : 17 ≤ p) : cP p = 1 := by
  have hp' : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  -- `p^{0.3} ≥ 17^{0.3} ≥ 2.3`
  have h17 : (2.3 : ℝ) ≤ (17 : ℝ) ^ ((3 : ℕ) / 10 : ℝ) := le_rpow_tenth (by norm_num) (by norm_num) 3 (by norm_num)
  have h3 : (2.3 : ℝ) ≤ (p : ℝ) ^ ((3 : ℝ) / 10) := by
    refine h17.trans ?_
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 17) hp' (by norm_num : (0 : ℝ) ≤ (3 : ℕ) / 10)
    simpa using this
  have hsplit : (p : ℝ) ^ ((7 : ℝ) / 10) * (p : ℝ) ^ ((3 : ℝ) / 10) = p := by
    rw [← Real.rpow_add hp0]; norm_num
  have h7 : 2 * (p : ℝ) ^ ((7 : ℝ) / 10) ≤ p - 1 := by
    have hpos : 0 < (p : ℝ) ^ ((7 : ℝ) / 10) := by positivity
    nlinarith
  unfold cP
  refine max_eq_left ?_
  rw [div_le_one (by linarith)]; exact h7

theorem cP_small_le : cP 2 * cP 3 * cP 5 * cP 7 * cP 11 * cP 13 ≤ 16 := by
  have b : ∀ (p : ℕ) (u : ℝ), 2 ≤ p → 0 ≤ u → (p : ℝ) ^ 7 ≤ u ^ 10 → 1 ≤ 2 * u / ((p : ℝ) - 1) →
      cP p ≤ 2 * u / ((p : ℝ) - 1) := by
    intro p u hp hu h h1
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    unfold cP
    refine max_le h1 ?_
    gcongr
    · linarith
    · exact_mod_cast rpow_tenth_le (by positivity) hu 7 h
  have h2 := b 2 1.63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := b 3 2.16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := b 5 3.09 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := b 7 3.91 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := b 11 5.36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := b 13 6.03 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h2 h3 h5 h7 h11 h13
  have := one_le_cP 2; have := one_le_cP 3; have := one_le_cP 5; have := one_le_cP 7
  have := one_le_cP 11; have := one_le_cP 13
  calc cP 2 * cP 3 * cP 5 * cP 7 * cP 11 * cP 13
      ≤ (2 * 1.63) * 2.16 * (2 * 3.09 / 4) * (2 * 3.91 / 6) * (2 * 5.36 / 10) * (2 * 6.03 / 12) := by
        gcongr <;> norm_num <;> linarith
    _ ≤ 16 := by norm_num

/-- `2^{ω(q)} q^{0.7} ≤ (Π_{p∣q} c_p) φ(q)`. -/
theorem omega_rpow_le (q : ℕ) (hq : q ≠ 0) :
    (2 : ℝ) ^ ω q * (q : ℝ) ^ ((7 : ℝ) / 10) ≤ (∏ p ∈ q.primeFactors, cP p) * q.totient := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hq
  | one => simp
  | prime_pow p n hp hn =>
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    rw [cardDistinctFactors_apply_prime_pow hp hn.ne', Nat.primeFactors_prime_pow hn.ne' hp, prod_singleton,
      Nat.totient_prime_pow hp hn, pow_one]
    push_cast
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.succ_sub_one]
    have e : ((p : ℝ) ^ (m + 1)) ^ ((7 : ℝ) / 10) = (p : ℝ) ^ ((7 : ℝ) / 10) * ((p : ℝ) ^ m) ^ ((7 : ℝ) / 10) := by
      rw [pow_succ, Real.mul_rpow (by positivity) hp0.le, mul_comm]
    rw [e]
    have hm : ((p : ℝ) ^ m) ^ ((7 : ℝ) / 10) ≤ (p : ℝ) ^ m :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by linarith)) (by norm_num)
    have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hc : 2 * (p : ℝ) ^ ((7 : ℝ) / 10) ≤ cP p * ((p : ℝ) - 1) := by
      calc 2 * (p : ℝ) ^ ((7 : ℝ) / 10) = 2 * (p : ℝ) ^ ((7 : ℝ) / 10) / ((p : ℝ) - 1) * ((p : ℝ) - 1) :=
            (div_mul_cancel₀ _ hp1).symm
        _ ≤ cP p * ((p : ℝ) - 1) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    have h0 : 0 ≤ (p : ℝ) ^ ((7 : ℝ) / 10) := by positivity
    calc 2 * ((p : ℝ) ^ ((7 : ℝ) / 10) * ((p : ℝ) ^ m) ^ ((7 : ℝ) / 10))
        ≤ 2 * ((p : ℝ) ^ ((7 : ℝ) / 10) * (p : ℝ) ^ m) := by gcongr
      _ = (2 * (p : ℝ) ^ ((7 : ℝ) / 10)) * (p : ℝ) ^ m := by ring
      _ ≤ (cP p * ((p : ℝ) - 1)) * (p : ℝ) ^ m := by gcongr
      _ = cP p * ((p : ℝ) ^ m * ((p - 1 : ℕ) : ℝ)) := by rw [Nat.cast_sub hp.one_le]; push_cast; ring
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [cardDistinctFactors_mul hab, Nat.primeFactors_mul ha0 hb0,
      prod_union hab.disjoint_primeFactors, Nat.totient_mul hab, pow_add]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have h1 := iha ha0
    have h2 := ihb hb0
    have : 0 ≤ (2 : ℝ) ^ ω b * (b : ℝ) ^ ((7 : ℝ) / 10) := by positivity
    calc (2 : ℝ) ^ ω a * 2 ^ ω b * ((a : ℝ) ^ ((7 : ℝ) / 10) * (b : ℝ) ^ ((7 : ℝ) / 10))
        = ((2 : ℝ) ^ ω a * (a : ℝ) ^ ((7 : ℝ) / 10)) * ((2 : ℝ) ^ ω b * (b : ℝ) ^ ((7 : ℝ) / 10)) := by ring
      _ ≤ ((∏ p ∈ a.primeFactors, cP p) * a.totient) * ((∏ p ∈ b.primeFactors, cP p) * b.totient) :=
          mul_le_mul h1 h2 this (le_trans (by positivity) h1)
      _ = _ := by ring

theorem prod_cP_le (q : ℕ) : ∏ p ∈ q.primeFactors, cP p ≤ 16 := by
  set S : Finset ℕ := {2, 3, 5, 7, 11, 13}
  have hsplit := prod_filter_mul_prod_filter_not q.primeFactors (· ∈ S) (f := cP)
  have hrest : ∏ p ∈ q.primeFactors.filter (· ∉ S), cP p = 1 := by
    refine prod_eq_one fun p hp => ?_
    obtain ⟨hpq, hpS⟩ := mem_filter.mp hp
    have hpr := Nat.prime_of_mem_primeFactors hpq
    apply cP_eq_one
    by_contra h
    push Not at h
    apply hpS
    interval_cases p <;> simp only [S] at hpS <;> revert hpr hpS <;> decide
  have hsub : ∏ p ∈ q.primeFactors.filter (· ∈ S), cP p ≤ ∏ p ∈ S, cP p := by
    have hT : q.primeFactors.filter (· ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
    rw [← prod_sdiff hT]
    have h1 : 1 ≤ ∏ p ∈ S \ q.primeFactors.filter (· ∈ S), cP p := by
      have := Finset.prod_le_prod₀ (s := S \ q.primeFactors.filter (· ∈ S)) (f := fun _ => (1 : ℝ))
        (g := cP) (fun _ _ => zero_le_one) fun p _ => one_le_cP p
      simpa using this
    have h0 : 0 ≤ ∏ p ∈ q.primeFactors.filter (· ∈ S), cP p :=
      prod_nonneg fun p _ => le_trans zero_le_one (one_le_cP p)
    nlinarith
  have hS : ∏ p ∈ S, cP p = cP 2 * cP 3 * cP 5 * cP 7 * cP 11 * cP 13 := by
    simp only [S]; rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_singleton]; ring
  rw [← hsplit, hrest, mul_one]
  exact hsub.trans (hS ▸ cP_small_le)

/-- **`2^{ω(q)}/φ(q) ≤ 16 q^{−0.7}`** for all `q ≥ 1` (the paper's `M_{0.70} ≤ 15.1372`, here with
`16`). -/
theorem omega_le_totient (q : ℕ) (hq : q ≠ 0) :
    (2 : ℝ) ^ ω q * (q : ℝ) ^ ((7 : ℝ) / 10) ≤ 16 * q.totient :=
  (omega_rpow_le q hq).trans (mul_le_mul_of_nonneg_right (prod_cP_le q) (Nat.cast_nonneg _))

/-! ### `R_q ≤ 1/10` for `q > 20000` -/

theorem growth_20001 {q : ℝ} (hq : 20001 ≤ q) :
    80 * (1 + Real.log 2 + Real.log q) ≤ q ^ ((7 : ℝ) / 10) := by
  set q₀ : ℝ := 20001 with hq₀def
  have hq₀ : q₀ ≠ 0 := by norm_num [hq₀def]
  have hq0 : 0 < q := by linarith
  set r := q / q₀
  have hr : 1 ≤ r := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hqr : q = q₀ * r := by simp only [r]; field_simp [hq₀]
  have h0 : (1000 : ℝ) ≤ q₀ ^ ((7 : ℝ) / 10) := by
    have := le_rpow_tenth (x := q₀) (b := 1000) (by norm_num) (by norm_num) 7 (by norm_num)
    simpa using this
  have hlog0 : Real.log q₀ ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : (2.7182818283 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) he.le 10
    rw [← Real.exp_nat_mul] at this
    norm_num at this ⊢; linarith
  have hl2 := Real.log_two_lt_d9
  set s := r ^ ((7 : ℝ) / 10)
  have hs : 1 ≤ s := Real.one_le_rpow hr (by norm_num)
  -- `log r ≤ (r^{0.7} − 1)/0.7`
  have hlogr : Real.log r ≤ (s - 1) / (7 / 10) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    rw [Real.log_rpow (by linarith)] at h
    rw [le_div_iff₀ (by norm_num)]; linarith
  rw [hqr, Real.mul_rpow (by norm_num) (by linarith), Real.log_mul hq₀ (by linarith)]
  have hq7 : (1000 : ℝ) * s ≤ q₀ ^ ((7 : ℝ) / 10) * s := mul_le_mul_of_nonneg_right h0 (by linarith)
  linarith

/-- For `q > 20000`, `R_q = φ(q)⁻¹ Σ (…) ≤ 1/10`. -/
theorem Rq_small {q : ℕ} (hq : 20000 < q) :
    (∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q)))) / q.totient ≤ 1 / 10 := by
  have hq0 : q ≠ 0 := by omega
  have hq' : (20001 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 := Rq_bound (by omega : 1 < q)
  have hrad : Real.log (radQ q) ≤ Real.log q := by
    have : 0 < radQ q := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    exact Real.log_le_log (by exact_mod_cast this) (by exact_mod_cast radQ_le hq0)
  have h2 := omega_le_totient q hq0
  have h3 := growth_20001 hq'
  have hq7 : 0 < (q : ℝ) ^ ((7 : ℝ) / 10) := by positivity
  have hc : 0 ≤ 1 + Real.log 2 + Real.log q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ q by linarith); have := Real.log_two_gt_d9; linarith
  rw [div_le_iff₀ hφ]
  refine h1.trans ?_
  have hw : 0 ≤ (2 : ℝ) ^ ω q := by positivity
  calc (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q))
      ≤ (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log q) := by gcongr
    _ ≤ 1 / 10 * q.totient := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
        have : (2 : ℝ) ^ ω q * (1 + Real.log 2 + Real.log q) * (q : ℝ) ^ ((7 : ℝ) / 10) ≤
            (16 * q.totient) * (q ^ ((7 : ℝ) / 10) / 80) := by
          have h3' : 1 + Real.log 2 + Real.log q ≤ (q : ℝ) ^ ((7 : ℝ) / 10) / 80 := by
            rw [le_div_iff₀ (by norm_num)]; linarith
          calc (2 : ℝ) ^ ω q * (1 + Real.log 2 + Real.log q) * (q : ℝ) ^ ((7 : ℝ) / 10)
              = (2 : ℝ) ^ ω q * (q : ℝ) ^ ((7 : ℝ) / 10) * (1 + Real.log 2 + Real.log q) := by ring
            _ ≤ (16 * q.totient) * (q ^ ((7 : ℝ) / 10) / 80) := mul_le_mul h2 h3' hc (by positivity)
        have := le_of_mul_le_mul_right (a := (q : ℝ) ^ ((7 : ℝ) / 10))
          (by nlinarith : (2 : ℝ) ^ ω q * (1 + Real.log 2 + Real.log q) * (q : ℝ) ^ ((7 : ℝ) / 10) ≤
            (1 / 10 * q.totient * 2) * (q : ℝ) ^ ((7 : ℝ) / 10)) hq7
        linarith

/-! ### The tail and the continuity of `A_q` -/

/-- `σ(q) = Σ_{d∣q, μ(q/d)≠0} 1/d`. -/
noncomputable def sigQ (q : ℕ) : ℝ :=
  ∑ y ∈ q.divisorsAntidiagonal, if μ y.1 ≠ 0 then 1 / (y.2 : ℝ) else 0

theorem sigQ_nonneg (q : ℕ) : 0 ≤ sigQ q :=
  sum_nonneg fun y _ => by split_ifs <;> positivity

/-- **The tail**: `|X A_q(X)| ≤ κ σ(q)` for `X > 0`. -/
theorem tail_Aq {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 0 < X) : X * Aq q X ≤ kappa * sigQ q := by
  rw [Aq_moebius hq0, mul_sum, sigQ, mul_sum]
  refine sum_le_sum fun y hy => ?_
  have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  have hb : (0 : ℝ) < y.2 := by exact_mod_cast hy2
  have habs := abs_avg_Gs_le hb hX ((y.2 : ℝ) / 2)
  set a := (∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X
  have hXa : X * |a| ≤ kappa / y.2 := by
    calc X * |a| ≤ X * (kappa / (y.2 * X)) := mul_le_mul_of_nonneg_left habs hX.le
      _ = kappa / y.2 := by field_simp
  rcases moebius_cases y.1 with h | h | h
  · rw [h, if_pos (by norm_num)]; push_cast
    have := neg_abs_le a
    have : X * -a ≤ X * |a| := mul_le_mul_of_nonneg_left (by linarith) hX.le
    have e : kappa * (1 / (y.2 : ℝ)) = kappa / y.2 := by ring
    rw [e]; nlinarith
  · rw [h]; simp
  · rw [h, if_pos (by norm_num)]; push_cast
    have : X * a ≤ X * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) hX.le
    have e : kappa * (1 / (y.2 : ℝ)) = kappa / y.2 := by ring
    rw [e]; nlinarith

theorem Aq_cont {q : ℕ} (hq0 : 0 < q) : ContinuousOn (Aq q) (Set.Ioi 0) := by
  have e : Set.EqOn (Aq q) (fun X => ∑ y ∈ q.divisorsAntidiagonal,
      (μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X)) (Set.Ioi 0) :=
    fun X _ => Aq_moebius hq0 X
  refine ContinuousOn.congr ?_ e
  refine continuousOn_finsetSum _ fun y hy => continuousOn_const.mul ?_
  have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  have hc := intervalIntegral.continuous_primitive
    (fun a b => Gs_aff_int (by exact_mod_cast hy2.ne' : (y.2 : ℝ) ≠ 0) ((y.2 : ℝ) / 2) a b) 0
  exact hc.continuousOn.div continuousOn_id fun X hX => (ne_of_gt hX)

/-! ### Corollary Q′ -/

/-- The emerging moduli `𝔈`: `q = 1`, `q = 2^k` (`k ≥ 2`) and `q = 2p^j`. -/
def emerging (q : ℕ) : Prop := q = 1 ∨ (Even q ∧ IsPrimePow (q / 2))

/-- `ℓ_q` with lower end `X₀` (`ℓ_q` itself has `X₀ = X_q`, the first local minimum of `A_q`). -/
noncomputable def ellq (q : ℕ) (X₀ : ℝ) : ℝ := sSup ((fun X => Aq q X / q.totient) '' Set.Ici X₀)

/-- The threshold `T = A_3(29/40)/φ(3)`, the certified lower bound of `ℓ_3`. -/
noncomputable def T3 : ℝ := Aq 3 (29 / 40) / 2

/-- `R_q` in the form computed by the certificate (`certify_lobes_arb.py`, `R_q`). -/
noncomputable def RqArb (q : ℕ) : ℝ :=
  (∑ y ∈ q.divisorsAntidiagonal,
    (if μ y.1 = 1 then min (Real.log 2) (kappa / (y.2 / (2 * q)))
     else if μ y.1 = -1 then min (kappa / (y.2 / (2 * q))) (1 - Real.log (2 * (y.2 / (2 * q)))) else 0)) /
    q.totient

/-- The end of the interval method: beyond it the tail gives `A_q/φ(q) ≤ (100/101)T`. -/
noncomputable def Xstar (q : ℕ) : ℝ := 101 / 100 * kappa * sigQ q / (q.totient * T3)

/-- **Arb certificate, part 1** (`certify_lobes_arb.py`, items (b), (c), 128-bit ball arithmetic,
output `lobes_arb.txt`): for every non-emerging `4 ≤ q ≤ 20000`, either `R_q < T`, or the interval
method bounds `A_q(X)/φ(q)` on `[1/(2q), X*_q]` by some `U < T`. An explicit hypothesis. -/
def ArbLobes : Prop :=
  ∀ q : ℕ, 4 ≤ q → q ≤ 20000 → ¬ emerging q →
    RqArb q < T3 ∨ ∃ U < T3, ∀ X ∈ Set.Icc (1 / (2 * (q : ℝ))) (Xstar q), Aq q X / q.totient ≤ U

/-- **Arb certificate, part 2** (item (a)): the point values of `A_3` at `1/5, 41/200, 21/100`
(a local minimum in between), `A_3(29/40)/2 ≥ 0.131593`, and `A_3(X)/2 ≤ 0.132469` on
`[1/6, κσ(3)/(2·0.132469)]` by the interval method. An explicit hypothesis. -/
def Arb3 : Prop :=
  Aq 3 (41 / 200) < Aq 3 (1 / 5) ∧ Aq 3 (41 / 200) < Aq 3 (21 / 100) ∧ 0.131593 ≤ T3 ∧
    ∀ X ∈ Set.Icc (1 / 6 : ℝ) (kappa * sigQ 3 / (2 * 0.132469)), Aq 3 X / 2 ≤ 0.132469

theorem totient_three : Nat.totient 3 = 2 := by
  rw [Nat.totient_prime Nat.prime_three]

/-- The certificate's `R_q` is the right side of Lemma Q(2) at `X = 1/(2q)`, divided by `φ(q)`. -/
theorem RqArb_eq {q : ℕ} (hq0 : 0 < q) :
    RqArb q = (∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q)))) / q.totient := by
  unfold RqArb
  congr 1
  refine sum_congr rfl fun y hy => ?_
  have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  have hyq : y.2 ≤ q := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hb : (0 : ℝ) < y.2 := by exact_mod_cast hy2
  have hL : (y.2 : ℝ) * (1 / (2 * q)) = y.2 / (2 * q) := by ring
  have hL0 : 0 < (y.2 : ℝ) / (2 * q) := by positivity
  have hLh : (y.2 : ℝ) / (2 * q) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; have : (y.2 : ℝ) ≤ q := by exact_mod_cast hyq
    linarith
  rw [hL]
  unfold termQ
  split_ifs with h1 h2
  · rfl
  · unfold betaQ
    rw [if_pos (by linarith), log_e_div hL0]
    refine (max_eq_right (le_min ?_ ?_)).symm
    · have hk := kappa_nonneg
      rw [le_div_iff₀ hL0]; nlinarith
    · have : Real.log (2 * (y.2 / (2 * q))) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
      linarith [kappa_le_half]
  · rfl

/-- **Corollary Q′ (the largest lobe)** (paper §3.3). With the Arb certificates `ArbLobes`, `Arb3`
(explicit hypotheses) and `T = A_3(29/40)/2`:
1. for every non-emerging `q ≥ 4` there is `U < T` with `A_q(X)/φ(q) ≤ U` for all `X ≥ 1/(2q)`;
2. `A_3(X)/2 ≤ 0.132469` for all `X ≥ 1/6`;
3. `A_3` has a local minimum in `(1/5, 21/100)`;
4. `0.131593 ≤ T`.
Proved here: the tail beyond `X*_q` (from `|Cl₂| ≤ Cl₂(π/3)`), `q > 20000` entirely (`Rq_small`:
`2^{ω(q)}/φ(q) ≤ 16 q^{−0.7}`), the identification of the certificate's `R_q` (`RqArb_eq`), and the
local minimum from the point values by continuity. -/
theorem corQprime (hL : ArbLobes) (h3 : Arb3) :
    (∀ q : ℕ, 4 ≤ q → ¬ emerging q → ∃ U < T3, ∀ X : ℝ, 1 / (2 * (q : ℝ)) ≤ X → Aq q X / q.totient ≤ U) ∧
    (∀ X : ℝ, 1 / 6 ≤ X → Aq 3 X / 2 ≤ 0.132469) ∧
    (∃ X₀ ∈ Set.Ioo (1 / 5 : ℝ) (21 / 100), IsLocalMin (Aq 3) X₀) ∧ 0.131593 ≤ T3 := by
  obtain ⟨hm1, hm2, hT, h3u⟩ := h3
  have hT0 : 0 < T3 := lt_of_lt_of_le (by norm_num) hT
  refine ⟨fun q hq4 hne => ?_, fun X hX => ?_, ?_, hT⟩
  · have hq0 : 0 < q := by omega
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hRq : ∀ X : ℝ, 1 / (2 * (q : ℝ)) ≤ X →
        Aq q X / q.totient ≤ (∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q)))) / q.totient :=
      fun X hX => div_le_div_of_nonneg_right (lemmaQ2_Rq hq0 hX) hφ.le
    rcases le_or_gt q 20000 with hq | hq
    · rcases hL q hq4 hq hne with hR | ⟨U, hU, hUX⟩
      · exact ⟨RqArb q, hR, fun X hX => (RqArb_eq hq0).symm ▸ hRq X hX⟩
      · refine ⟨max U (100 / 101 * T3), max_lt hU (by linarith), fun X hX => ?_⟩
        rcases le_or_gt X (Xstar q) with hX' | hX'
        · exact (hUX X ⟨hX, hX'⟩).trans (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
          have ht := tail_Aq hq0 hX0
          have hs := sigQ_nonneg q
          have hk := kappa_nonneg
          -- `A_q(X)/φ ≤ κσ/(Xφ) < κσ/(X*φ) = (100/101) T`
          rw [div_le_iff₀ hφ]
          have hXs : Xstar q * (q.totient * T3) = 101 / 100 * kappa * sigQ q := by
            unfold Xstar; field_simp
          have : X * Aq q X ≤ X * (100 / 101 * T3 * q.totient) := by
            have : kappa * sigQ q ≤ X * (100 / 101 * T3 * q.totient) := by
              have hpos : 0 < (q.totient : ℝ) * T3 := mul_pos hφ hT0
              have := mul_lt_mul_of_pos_right hX' hpos
              nlinarith
            linarith
          exact le_of_mul_le_mul_left (by linarith) hX0
    · exact ⟨1 / 10, by linarith, fun X hX => (hRq X hX).trans (Rq_small hq)⟩
  · rcases le_or_gt X (kappa * sigQ 3 / (2 * 0.132469)) with hX' | hX'
    · exact h3u X ⟨hX, hX'⟩
    · have hX0 : 0 < X := by linarith
      have ht := tail_Aq (by norm_num : 0 < 3) hX0
      have hs := sigQ_nonneg 3
      have hk := kappa_nonneg
      rw [div_le_iff₀ (by norm_num)]
      have : kappa * sigQ 3 < X * (2 * 0.132469) := by
        rw [div_lt_iff₀ (by norm_num)] at hX'; linarith
      nlinarith
  · -- the minimum of `A_3` on `[1/5, 21/100]` is interior
    have hc : ContinuousOn (Aq 3) (Set.Icc (1 / 5 : ℝ) (21 / 100)) :=
      (Aq_cont (by norm_num)).mono fun X hX => by simp only [Set.mem_Ioi]; linarith [hX.1]
    obtain ⟨X₀, hX₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨41 / 200, by norm_num, by norm_num⟩ hc
    have h41 : Aq 3 X₀ ≤ Aq 3 (41 / 200) := hmin ⟨by norm_num, by norm_num⟩
    have hne1 : X₀ ≠ 1 / 5 := by rintro rfl; linarith
    have hne2 : X₀ ≠ 21 / 100 := by rintro rfl; linarith
    have hX₀' : X₀ ∈ Set.Ioo (1 / 5 : ℝ) (21 / 100) :=
      ⟨lt_of_le_of_ne hX₀.1 (Ne.symm hne1), lt_of_le_of_ne hX₀.2 hne2⟩
    exact ⟨X₀, hX₀', hmin.isLocalMin (Icc_mem_nhds hX₀'.1 hX₀'.2)⟩

/-- In terms of `ℓ_q`: for non-emerging `q ≥ 4` and any `X₀ ≥ 1/(2q)` (in particular `X_q`),
`ℓ_q < T ≤ ℓ_3 ≤ 0.132469` whenever `1/6 ≤ X₃ ≤ 29/40`; so `sup_{q∉𝔈} ℓ_q = ℓ_3 ∈ [0.131593, 0.132469]`. -/
theorem corQprime_ell (hL : ArbLobes) (h3 : Arb3) :
    (∀ q : ℕ, 4 ≤ q → ¬ emerging q → ∀ X₀ : ℝ, 1 / (2 * (q : ℝ)) ≤ X₀ → ellq q X₀ < T3) ∧
    (∀ X₀ : ℝ, 1 / 6 ≤ X₀ → X₀ ≤ 29 / 40 → 0.131593 ≤ ellq 3 X₀ ∧ ellq 3 X₀ ≤ 0.132469) := by
  obtain ⟨h1, h2, -, h4⟩ := corQprime hL h3
  refine ⟨fun q hq4 hne X₀ hX₀ => ?_, fun X₀ hX1 hX2 => ?_⟩
  · obtain ⟨U, hU, hUX⟩ := h1 q hq4 hne
    refine lt_of_le_of_lt (csSup_le (Set.Nonempty.image _ ⟨X₀, Set.mem_Ici.mpr le_rfl⟩) ?_) hU
    rintro _ ⟨X, hX, rfl⟩
    exact hUX X (le_trans hX₀ hX)
  · have hbdd : BddAbove ((fun X => Aq 3 X / (Nat.totient 3 : ℝ)) '' Set.Ici X₀) := by
      refine ⟨0.132469, ?_⟩
      rintro _ ⟨X, hX, rfl⟩
      rw [totient_three]; push_cast; exact h2 X (le_trans hX1 hX)
    refine ⟨le_trans h4 ?_, csSup_le (Set.Nonempty.image _ ⟨X₀, Set.mem_Ici.mpr le_rfl⟩) ?_⟩
    · refine le_csSup hbdd ⟨29 / 40, hX2, ?_⟩
      rw [totient_three]; rfl
    · rintro _ ⟨X, hX, rfl⟩
      rw [totient_three]; push_cast; exact h2 X (le_trans hX1 hX)

end ArcsAlgo.Core
