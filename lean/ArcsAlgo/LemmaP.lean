module

public import ArcsAlgo.ArcCore
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false

/-!
# Lemma P: maximum principle for emerging arcs (paper §3.3)

`h_q(x) = log|Φ_q(−e(x))|` (`hq`) and `A_q(X) = X⁻¹∫₀^X h_q` (`Aq`).

* `norm_cyc_neg_odd`, `norm_cyc_neg_even`: `|Φ_{2n}(−y)| = |Φ_n(y)|` (`n` odd), `= |Φ_{2n}(y)|`
  (`n` even), through `μ ↦ −μ` on the primitive roots; `eval_cyc_prime_pow`:
  `Φ_{p^{k+1}}(y) = Φ_p(y^{p^k})`.
* `emerging_reduce`: for even `q ≥ 4` with `q/2 = p^j`, `|Φ_q(−e(x))| = |Φ_p(e(mx))|` with `m = 2^j`
  (`p = 2`) or `p^{j−1}`, and `Λ(q/2) = log p` (the Dirichlet kernel of the paper).
* `norm_cyc_prime_le`: `|Φ_p(e(t))| ≤ p − 2 + 2|cos πt|`.
* `umaj`: the continuous 1-periodic majorant `log max(p − 2 + 2|cos πmx|, 1) ≥ h_q`, `< log p`
  near `0`; `integral_umaj_lt`, `integral_umaj_nat`.
* `lemmaP`: `|Φ_q(−e(x))| ≤ e^{Λ(q/2)} = |Φ_q(−1)|`, with equality on a finite subset of `[0, 1)`;
  `A_q(X) < Λ(q/2)` for `X > 0`; for every `X₀ > 0`, `sup_{X ≥ X₀} A_q(X) < Λ(q/2)`, hence
  `ℓ_q < c_q`.

No hypothesis. The paper's Jensen step (`A_q(X) → 0`) is not needed: the bound for `X ≥ 1` comes from
whole periods of the majorant, whose mean is `< log p`.
-/

open Finset Real Polynomial ArithmeticFunction

@[expose] public section

namespace ArcsAlgo.Core

/-- `h_q(x) = log|Φ_q(−e(x))|`. -/
noncomputable def hq (q : ℕ) (x : ℝ) : ℝ := Real.log ‖(cyclotomic q ℂ).eval (-ee x)‖

/-- The neighbourhood level `A_q(X) = X⁻¹ ∫₀^X log|Φ_q(−e(x))| dx`. -/
noncomputable def Aq (q : ℕ) (X : ℝ) : ℝ := (∫ x in (0 : ℝ)..X, hq q x) / X

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [show (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem ee_pow (t : ℝ) (m : ℕ) : ee t ^ m = ee (m * t) := by
  unfold ee; rw [← Complex.exp_nat_mul]; push_cast; ring_nf

/-! ### `|Φ_q(−y)|` for the emerging `q` -/

theorem eval_cyclotomic_prod (n : ℕ) (hn : n ≠ 0) (y : ℂ) :
    (cyclotomic n ℂ).eval y = ∏ μ ∈ primitiveRoots n ℂ, (y - μ) := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn), eval_prod]
  simp

/-- `|Φ_{2n}(−y)| = |Φ_n(y)|` for odd `n`. -/
theorem norm_cyc_neg_odd {n : ℕ} (hn : Odd n) (y : ℂ) :
    ‖(cyclotomic (2 * n) ℂ).eval (-y)‖ = ‖(cyclotomic n ℂ).eval y‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hg : ∀ x ∈ primitiveRoots (2 * n) ℂ, -x ∈ primitiveRoots n ℂ := by
    intro x hx
    rw [mem_primitiveRoots (by omega)] at hx
    rw [mem_primitiveRoots (by omega)]
    exact neg_primitive_odd hn hx
  have hcard : (primitiveRoots n ℂ).card ≤ (primitiveRoots (2 * n) ℂ).card := by
    rw [Complex.card_primitiveRoots, Complex.card_primitiveRoots, Nat.totient_two_mul_of_odd hn]
  rw [eval_cyclotomic_prod _ (by omega), eval_cyclotomic_prod _ hn0,
    prod_eq_prod_of_inj (s := primitiveRoots (2 * n) ℂ) (t := primitiveRoots n ℂ) (fun x => -x)
      hg (neg_injOn _) hcard (fun ν => y - ν), norm_prod, norm_prod]
  refine prod_congr rfl fun μ _ => ?_
  rw [show -y - μ = -(y - -μ) by ring, norm_neg]

/-- `|Φ_{2n}(−y)| = |Φ_{2n}(y)|` for even `n > 0`. -/
theorem norm_cyc_neg_even {n : ℕ} (hn : Even n) (hn0 : 0 < n) (y : ℂ) :
    ‖(cyclotomic (2 * n) ℂ).eval (-y)‖ = ‖(cyclotomic (2 * n) ℂ).eval y‖ := by
  have hg : ∀ x ∈ primitiveRoots (2 * n) ℂ, -x ∈ primitiveRoots (2 * n) ℂ := by
    intro x hx
    rw [mem_primitiveRoots (by omega)] at hx ⊢
    exact neg_primitive_even hn hn0 hx
  rw [eval_cyclotomic_prod _ (by omega), eval_cyclotomic_prod _ (by omega),
    prod_eq_prod_of_inj (s := primitiveRoots (2 * n) ℂ) (t := primitiveRoots (2 * n) ℂ) (fun x => -x)
      hg (neg_injOn _) le_rfl (fun ν => y - ν), norm_prod, norm_prod]
  refine prod_congr rfl fun μ _ => ?_
  rw [show -y - μ = -(y - -μ) by ring, norm_neg]

/-- `Φ_{p^{k+1}}(y) = Φ_p(y^{p^k})`. -/
theorem eval_cyc_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (y : ℂ) :
    (cyclotomic (p ^ (k + 1)) ℂ).eval y = (cyclotomic p ℂ).eval (y ^ p ^ k) := by
  have := Fact.mk hp
  rw [cyclotomic_prime_pow_eq_geom_sum hp, cyclotomic_prime, eval_finsetSum, eval_finsetSum]
  simp

/-- **The emerging moduli** (paper §3.3): for even `q ≥ 4` with `q/2` a prime power `p^j`, there is
`m ≥ 1` with `|Φ_q(−e(x))| = |Φ_p(e(mx))|` for all `x`, and `Λ(q/2) = Real.log p`
(`m = 2^j` if `p = 2`, `m = p^{j−1}` if `p` is odd). -/
theorem emerging_reduce {q : ℕ} (hqe : Even q) (hq4 : 4 ≤ q) (hpp : IsPrimePow (q / 2)) :
    ∃ p m : ℕ, p.Prime ∧ 1 ≤ m ∧ Λ (q / 2) = Real.log p ∧
      ∀ x, ‖(cyclotomic q ℂ).eval (-ee x)‖ = ‖(cyclotomic p ℂ).eval (ee (m * x))‖ := by
  obtain ⟨n, hn⟩ := hqe
  have hq2 : q = 2 * n := by omega
  have hqn : q / 2 = n := by omega
  rw [hqn] at hpp ⊢
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
  have hΛ : Λ (p ^ j) = Real.log p := by
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `q = 2^{k+2}`
    refine ⟨2, 2 ^ (k + 1), Nat.prime_two, Nat.one_le_two_pow, hΛ, fun x => ?_⟩
    have hev : Even (2 ^ (k + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [hq2, norm_cyc_neg_even hev (by positivity), show 2 * 2 ^ (k + 1) = 2 ^ (k + 1 + 1) by ring,
      eval_cyc_prime_pow Nat.prime_two, ee_pow]
  · -- `q = 2p^{k+1}`, `p` odd
    refine ⟨p, p ^ k, hp, Nat.one_le_pow _ _ hp.pos, hΛ, fun x => ?_⟩
    rw [hq2, norm_cyc_neg_odd (hodd.pow) , eval_cyc_prime_pow hp, ee_pow]

/-! ### `|Φ_p(e(t))| ≤ p − 2 + 2|cos πt|` -/

theorem norm_cyc_prime_le {p : ℕ} (hp : p.Prime) (t : ℝ) :
    ‖(cyclotomic p ℂ).eval (ee t)‖ ≤ (p - 2 : ℝ) + 2 * |cos (π * t)| := by
  have := Fact.mk hp
  have hp2 := hp.two_le
  rw [cyclotomic_prime, eval_finsetSum, ← sum_range_add_sum_Ico _ hp2]
  simp only [eval_pow, eval_X]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ i ∈ range 2, ee t ^ i‖ = 2 * |cos (π * t)| := by
    rw [sum_range_succ, sum_range_one, pow_zero, pow_one]; exact norm_one_add_ee t
  have h2 : ‖∑ i ∈ Ico 2 p, ee t ^ i‖ ≤ (p - 2 : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_pow, norm_ee, one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp2]; norm_num
  linarith

theorem norm_cyc_prime_one {p : ℕ} (hp : p.Prime) : ‖(cyclotomic p ℂ).eval (ee 0)‖ = p := by
  have := Fact.mk hp
  rw [show ee 0 = 1 by simp [ee], eval_one_cyclotomic_prime]; simp

/-! ### The continuous majorant -/

/-- `u(x) = Real.log max(p − 2 + 2|cos πmx|, 1)`: continuous, `≤ Real.log p`, `= Real.log p` only where `mx ∈ ℤ`. -/
noncomputable def umaj (p m : ℕ) (x : ℝ) : ℝ := Real.log (max ((p - 2 : ℝ) + 2 * |cos (π * (m * x))|) 1)

theorem umaj_cont (p m : ℕ) : Continuous (umaj p m) := by
  unfold umaj
  refine Continuous.log (by fun_prop) fun x => ?_
  have := le_max_right ((p - 2 : ℝ) + 2 * |cos (π * (m * x))|) 1
  linarith

theorem umaj_nonneg (p m : ℕ) (x : ℝ) : 0 ≤ umaj p m x := Real.log_nonneg (le_max_right _ _)

theorem umaj_le {p : ℕ} (hp : p.Prime) (m : ℕ) (x : ℝ) : umaj p m x ≤ Real.log p := by
  unfold umaj
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le ?_ (by linarith))
  nlinarith [abs_cos_le_one (π * (m * x))]

theorem hq_le_umaj {q p m : ℕ} (hp : p.Prime)
    (hred : ∀ x, ‖(cyclotomic q ℂ).eval (-ee x)‖ = ‖(cyclotomic p ℂ).eval (ee (m * x))‖) (x : ℝ) :
    hq q x ≤ umaj p m x := by
  unfold hq
  rw [hred]
  rcases (norm_nonneg ((cyclotomic p ℂ).eval (ee (m * x)))).eq_or_lt with h | h
  · rw [← h, Real.log_zero]; exact umaj_nonneg p m x
  · unfold umaj
    exact Real.log_le_log h ((norm_cyc_prime_le hp _).trans (le_max_left _ _))

theorem umaj_periodic (p m : ℕ) : Function.Periodic (umaj p m) 1 := by
  intro x
  unfold umaj
  rw [show π * (m * (x + 1)) = π * (m * x) + m * π by ring, Real.cos_add_nat_mul_pi, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul]

/-- `∫₀^X u < X Real.log p` for `X > 0`. -/
theorem integral_umaj_lt {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) :
    ∫ x in (0 : ℝ)..X, umaj p m x < X * Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hX
    (umaj_cont p m).continuousOn continuousOn_const (fun x _ => umaj_le hp m x)
    ⟨min X (1 / (2 * m)), ⟨le_min hX.le (by positivity), min_le_left _ _⟩, ?_⟩
  · simpa [intervalIntegral.integral_const, mul_comm] using h
  set c := min X (1 / (2 * m))
  have hc0 : 0 < c := lt_min hX (by positivity)
  have hc1 : c ≤ 1 / (2 * m) := min_le_right _ _
  have hθ0 : 0 < π * (m * c) := by positivity
  have hθ1 : π * (m * c) ≤ π / 2 := by
    have : m * c ≤ 1 / 2 := by
      calc (m : ℝ) * c ≤ m * (1 / (2 * m)) := by gcongr
        _ = 1 / 2 := by field_simp
    nlinarith [Real.pi_pos]
  have hcos0 : 0 ≤ cos (π * (m * c)) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ1⟩
  have hcos1 : cos (π * (m * c)) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hθ1 hθ0
    rwa [Real.cos_zero] at this
  unfold umaj
  apply Real.log_lt_log (lt_of_lt_of_le one_pos (le_max_right _ _))
  rw [abs_of_nonneg hcos0]
  exact max_lt (by linarith) (by linarith)

/-- `∫₀^n u = n ∫₀^1 u`. -/
theorem integral_umaj_nat (p m n : ℕ) :
    ∫ x in (0 : ℝ)..n, umaj p m x = n * ∫ x in (0 : ℝ)..1, umaj p m x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : ∀ a b : ℝ, IntervalIntegrable (umaj p m) MeasureTheory.volume a b :=
      fun a b => (umaj_cont p m).intervalIntegrable a b
    have := (umaj_periodic p m).intervalIntegral_add_eq (n : ℝ) 0
    rw [zero_add] at this
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 n) (hi n (n + 1)), ih, this]; ring

/-- **Lemma P (maximum principle for emerging arcs)** (paper §3.3). Let `q ≥ 4` be emerging:
`q` even and `q/2` a prime power. Then
1. `|Φ_q(−e(x))| ≤ e^{Λ(q/2)}`, with equality at `x = 0`;
2. equality holds only on a finite set of `x ∈ [0, 1)`;
3. `A_q(X) < Λ(q/2)` for every `X > 0`;
4. for every `X₀ > 0` there is `c < Λ(q/2)` with `A_q(X) ≤ c` for all `X ≥ X₀`; so
   `ℓ_q = sup_{X ≥ X_q} A_q(X)/φ(q) < Λ(q/2)/φ(q) = c_q` since `X_q > 0`.
No hypothesis. Jensen's formula is not needed: a continuous periodic majorant gives (3), (4). -/
theorem lemmaP {q : ℕ} (hqe : Even q) (hq4 : 4 ≤ q) (hpp : IsPrimePow (q / 2)) :
    (∀ x, ‖(cyclotomic q ℂ).eval (-ee x)‖ ≤ exp (Λ (q / 2))) ∧
    ‖(cyclotomic q ℂ).eval (-ee 0)‖ = exp (Λ (q / 2)) ∧
    {x ∈ Set.Ico (0 : ℝ) 1 | ‖(cyclotomic q ℂ).eval (-ee x)‖ = exp (Λ (q / 2))}.Finite ∧
    (∀ X > 0, Aq q X < Λ (q / 2)) ∧
    (∀ X₀ > 0, ∃ c < Λ (q / 2), ∀ X ≥ X₀, Aq q X ≤ c) := by
  obtain ⟨p, m, hp, hm, hΛ, hred⟩ := emerging_reduce hqe hq4 hpp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hΛ, Real.exp_log hp0]
  -- the integral of `h_q` against that of `u`
  have hcmp : ∀ X > 0, Aq q X ≤ max 0 ((∫ x in (0 : ℝ)..X, umaj p m x) / X) := by
    intro X hX
    unfold Aq
    by_cases hi : IntervalIntegrable (hq q) MeasureTheory.volume 0 X
    · refine le_trans ?_ (le_max_right _ _)
      apply div_le_div_of_nonneg_right _ hX.le
      exact intervalIntegral.integral_mono_on hX.le hi ((umaj_cont p m).intervalIntegrable 0 X)
        fun x _ => hq_le_umaj hp hred x
    · rw [intervalIntegral.integral_undef hi, zero_div]; exact le_max_left _ _
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hred]
    have := norm_cyc_prime_le hp (m * x)
    nlinarith [abs_cos_le_one (π * (m * x))]
  · rw [hred, mul_zero]; exact norm_cyc_prime_one hp
  · -- equality forces `|cos(πmx)| = 1`, i.e. `mx ∈ ℤ`
    refine Set.Finite.subset ((range m).image fun k : ℕ => (k : ℝ) / m).finite_toSet ?_
    intro x hx
    obtain ⟨⟨hx0, hx1⟩, heq⟩ := hx
    rw [hred] at heq
    have h1 := norm_cyc_prime_le hp (m * x)
    have hc : |cos (π * (m * x))| = 1 := le_antisymm (abs_cos_le_one _) (by linarith)
    have hs : sin (π * (m * x)) = 0 := by
      have := Real.sin_sq_add_cos_sq (π * (m * x))
      rw [← sq_abs (cos _), hc] at this
      have : sin (π * (m * x)) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hk' : (k : ℝ) = m * x := by
      have := Real.pi_pos
      field_simp at hk; linarith
    have hk0 : 0 ≤ k := by
      have : (0 : ℝ) ≤ k := by rw [hk']; positivity
      exact_mod_cast this
    have hkm : k < m := by
      have : (k : ℝ) < m := by rw [hk']; nlinarith
      exact_mod_cast this
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨k.toNat, by omega, ?_⟩
    rw [show ((k.toNat : ℕ) : ℝ) = (k : ℝ) by exact_mod_cast Int.toNat_of_nonneg hk0, hk']
    field_simp
  · intro X hX
    refine (hcmp X hX).trans_lt (max_lt hlogp ?_)
    rw [div_lt_iff₀ hX, mul_comm]; exact integral_umaj_lt hp hm hX
  · intro X₀ hX₀
    set X₁ := min X₀ 1
    have hX₁ : 0 < X₁ := lt_min hX₀ one_pos
    set I := ∫ x in (0 : ℝ)..1, umaj p m x
    have hI : I < Real.log p := by have := integral_umaj_lt hp hm one_pos; simpa using this
    set δ₀ := X₁ * Real.log p - ∫ x in (0 : ℝ)..X₁, umaj p m x
    have hδ₀ : 0 < δ₀ := by have := integral_umaj_lt hp hm hX₁; simp only [δ₀]; linarith
    set c := max 0 (Real.log p - min δ₀ ((Real.log p - I) / 2))
    refine ⟨c, max_lt hlogp (by have := lt_min hδ₀ (by linarith : 0 < (Real.log p - I) / 2); linarith),
      fun X hX => ?_⟩
    have hX0 : 0 < X := lt_of_lt_of_le hX₀ hX
    refine (hcmp X hX0).trans (max_le_max le_rfl ?_)
    have hi : ∀ a b : ℝ, IntervalIntegrable (umaj p m) MeasureTheory.volume a b :=
      fun a b => (umaj_cont p m).intervalIntegrable a b
    have hconst : ∀ a b : ℝ, a ≤ b → ∫ x in a..b, umaj p m x ≤ (b - a) * Real.log p := by
      intro a b hab
      have := intervalIntegral.integral_mono_on hab (hi a b) intervalIntegrable_const
        fun x _ => umaj_le hp m x
      simpa [intervalIntegral.integral_const, mul_comm] using this
    rw [div_le_iff₀ hX0]
    rcases le_or_gt X 1 with hX1 | hX1
    · -- `X₁ ≤ X ≤ 1`
      have hX₁X : X₁ ≤ X := le_trans (min_le_left _ _) hX
      have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 X₁) (hi X₁ X)
      have h2 := hconst X₁ X hX₁X
      have : ∫ x in (0 : ℝ)..X, umaj p m x ≤ X * Real.log p - δ₀ := by simp only [δ₀]; linarith
      have hmin : min δ₀ ((Real.log p - I) / 2) ≤ δ₀ := min_le_left _ _
      have : (Real.log p - min δ₀ ((Real.log p - I) / 2)) * X ≥ X * Real.log p - δ₀ := by nlinarith
      linarith
    · -- `X > 1`: whole periods
      set n := ⌊X⌋₊
      have hn1 : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
      have hnX : (n : ℝ) ≤ X := Nat.floor_le (by linarith)
      have hXn : X < n + 1 := Nat.lt_floor_add_one X
      have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 n) (hi n X)
      rw [integral_umaj_nat] at e
      have h2 := hconst n X hnX
      have hn2 : X ≤ 2 * n := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
                                 linarith
      have hmin : min δ₀ ((Real.log p - I) / 2) ≤ (Real.log p - I) / 2 := min_le_right _ _
      have hgap : 0 ≤ Real.log p - I := by linarith
      have : (Real.log p - min δ₀ ((Real.log p - I) / 2)) * X ≥ n * I + (X - n) * Real.log p := by nlinarith
      linarith

end ArcsAlgo.Core
