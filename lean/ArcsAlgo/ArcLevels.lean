module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
set_option autoImplicit false

/-!
# Which arcs emerge (paper §3.2, Lemma 1)

* `prod_one_add_primitiveRoots`: `|Π_{μ primitive q-th} (1 + μ)| = |Φ_q(−1)|` equals `exp Λ(q/2)` for
  even `q ≥ 3` and `1` for odd `q ≥ 3` ([BHM, Lemma 7]); it is computed through `μ ↦ −μ`, which
  turns it into `Φ_{2q}(1)` for odd `q`, `Φ_{q/2}(1)` for `q ≡ 2 (mod 4)` and `Φ_q(1)` for `4 ∣ q`.
* `lemma_one` (Lemma 1): for `q ≥ 3` and `(a, q) = 1`,
  `Σ_{(r,q)=1} log|cos(πra/q)| = −φ(q) log 2 + Λ(q/2)` (even `q`) or `−φ(q) log 2` (odd `q`);
  in particular `w̄(q)` does not depend on `a`.
* `arc_emerges_iff`: `w̄(q) > −log 2` iff `q` is even and `q/2` is a prime power, and
  `half_isPrimePow_iff`: this means `q = 2^k` with `k ≥ 2` or `q = 2p^j` with `p` an odd prime.
-/

@[expose] public section

namespace ArcsAlgo

open Polynomial Complex Finset ArithmeticFunction
open scoped Real

/-! ### Cyclotomic values at `1` -/

theorem cyclotomic_eval_one_eq_exp (n : ℕ) (hn : 2 ≤ n) :
    (cyclotomic n ℂ).eval 1 = (Real.exp (Λ n) : ℂ) := by
  by_cases hp : IsPrimePow n
  · obtain ⟨p, k, hpp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hp
    have := Fact.mk hpp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [eval_one_cyclotomic_prime_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero _),
      vonMangoldt_apply_prime hpp, Real.exp_log (by exact_mod_cast hpp.pos)]
    simp
  · rw [eval_one_cyclotomic_not_prime_pow, vonMangoldt_eq_zero_iff.2 hp, Real.exp_zero]
    · simp
    · intro p hpp k hk
      apply hp
      rcases k with _ | k
      · simp at hk; omega
      · exact (isPrimePow_nat_iff n).2 ⟨p, k + 1, hpp, by omega, hk⟩

theorem prod_one_sub_primitiveRoots (n : ℕ) (hn : n ≠ 0) :
    ∏ μ ∈ primitiveRoots n ℂ, (1 - μ) = (cyclotomic n ℂ).eval 1 := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn), eval_prod]
  simp

/-! ### The map `μ ↦ −μ` on primitive roots -/

theorem coprime_succ_self' (n : ℕ) : Nat.Coprime (n + 1) n := by
  rw [add_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left n

theorem neg_eq_pow {μ : ℂ} {n : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot μ (2 * n)) :
    -μ = μ ^ (n + 1) := by
  have h2 : IsPrimitiveRoot (μ ^ n) 2 := h.pow (by omega) (by ring)
  rw [pow_succ, h2.eq_neg_one_of_two_right]
  ring

/-- If `μ` is a primitive `2m`-th root of unity with `m` odd, `−μ` is a primitive `m`-th root. -/
theorem neg_primitive_odd {μ : ℂ} {m : ℕ} (hm : Odd m) (h : IsPrimitiveRoot μ (2 * m)) :
    IsPrimitiveRoot (-μ) m := by
  obtain ⟨k, rfl⟩ := hm
  have hsq : IsPrimitiveRoot (μ ^ 2) (2 * k + 1) := h.pow (by omega) (by ring)
  have hcop : Nat.Coprime (k + 1) (2 * k + 1) := by
    have : 2 * k + 1 = (k + 1) + k := by ring
    rw [this, Nat.coprime_self_add_right]
    exact coprime_succ_self' k
  rw [neg_eq_pow (by omega) h, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
  exact hsq.pow_of_coprime _ hcop

/-- If `μ` is a primitive `2n`-th root of unity with `n` even, `−μ` is again a primitive `2n`-th
root. -/
theorem neg_primitive_even {μ : ℂ} {n : ℕ} (hn : Even n) (hn0 : 0 < n) (h : IsPrimitiveRoot μ (2 * n)) :
    IsPrimitiveRoot (-μ) (2 * n) := by
  rw [neg_eq_pow hn0 h]
  apply h.pow_of_coprime
  apply Nat.Coprime.mul_right
  · rw [Nat.coprime_two_right]
    exact hn.add_one
  · exact coprime_succ_self' n

/-- A product over `t` equals the product over `s` through an injection `g : s → t` with
`|s| = |t|`. -/
theorem prod_eq_prod_of_inj {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β} (g : α → β) (hg : ∀ x ∈ s, g x ∈ t)
    (hinj : Set.InjOn g s) (hcard : t.card ≤ s.card) (f : β → ℂ) :
    ∏ y ∈ t, f y = ∏ x ∈ s, f (g x) := by
  have himg : s.image g = t := Finset.eq_of_subset_of_card_le
    (fun y hy => by obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hg x hx)
    (by rw [card_image_of_injOn hinj]; exact hcard)
  rw [← himg, prod_image hinj]

theorem neg_injOn (s : Finset ℂ) : Set.InjOn (fun x : ℂ => -x) s := fun _ _ _ _ h => neg_injective h

/-! ### `|Φ_q(−1)|` -/

theorem two_of_prime_dvd_two_mul {p k n : ℕ} (hp : p.Prime) (_hk : 0 < k) (h : p ^ k = 2 * n) : p = 2 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow (h ▸ dvd_mul_right 2 n : 2 ∣ p ^ k))).symm

theorem not_isPrimePow_two_mul_odd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) : ¬ IsPrimePow (2 * q) := by
  intro h
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).1 h
  have hp2 := two_of_prime_dvd_two_mul hp hk hpk
  subst hp2
  obtain ⟨j, rfl⟩ := hq
  rcases k with _ | _ | k
  · omega
  · simp at hpk; omega
  · rw [pow_succ, pow_succ] at hpk; omega

theorem isPrimePow_two_mul_iff {n : ℕ} (hn : Even n) (h2 : 2 ≤ n) :
    IsPrimePow (2 * n) ↔ IsPrimePow n := by
  constructor
  · intro h
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).1 h
    have hp2 := two_of_prime_dvd_two_mul hp hk hpk
    subst hp2
    rcases k with _ | _ | k
    · omega
    · simp at hpk; omega
    · refine (isPrimePow_nat_iff _).2 ⟨2, k + 1, Nat.prime_two, by omega, ?_⟩
      rw [pow_succ] at hpk; omega
  · intro h
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).1 h
    have hp2 : p = 2 := by
      obtain ⟨m, hm⟩ := hn
      exact two_of_prime_dvd_two_mul (n := m) hp hk (by rw [hpk]; omega)
    subst hp2
    exact (isPrimePow_nat_iff _).2 ⟨2, k + 1, Nat.prime_two, by omega, by rw [pow_succ, hpk]; ring⟩

theorem vonMangoldt_two_mul {n : ℕ} (hn : Even n) (h2 : 2 ≤ n) : Λ (2 * n) = Λ n := by
  rw [vonMangoldt_apply, vonMangoldt_apply, (Nat.minFac_eq_two_iff _).2 (dvd_mul_right 2 n),
    (Nat.minFac_eq_two_iff _).2 (even_iff_two_dvd.1 hn)]
  by_cases h : IsPrimePow n
  · simp [h, (isPrimePow_two_mul_iff hn h2).2 h]
  · simp [h, mt (isPrimePow_two_mul_iff hn h2).1 h]

theorem norm_exp_real (x : ℝ) : ‖((Real.exp x : ℝ) : ℂ)‖ = Real.exp x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]

/-- **[BHM, Lemma 7]** in the form used by Lemma 1 (paper §3.2): for `q ≥ 3`,
`|Π_{μ primitive q-th} (1 + μ)| = |Φ_q(−1)|` is `exp Λ(q/2)` for even `q` and `1` for odd `q`. -/
theorem prod_one_add_primitiveRoots (q : ℕ) (hq : 3 ≤ q) :
    ‖∏ μ ∈ primitiveRoots q ℂ, (1 + μ)‖ = Real.exp (if Even q then Λ (q / 2) else 0) := by
  rcases Nat.even_or_odd q with ⟨n, hn⟩ | hodd
  · have hq2 : q = 2 * n := by omega
    have hqn : q / 2 = n := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨n, hn⟩), hqn]
    rcases Nat.even_or_odd n with hne | hno
    · have h0 : 0 < n := by omega
      have hg : ∀ x ∈ primitiveRoots q ℂ, -x ∈ primitiveRoots q ℂ := by
        intro x hx
        rw [mem_primitiveRoots (by omega)] at hx ⊢
        rw [hq2] at hx ⊢
        exact neg_primitive_even hne h0 hx
      have e : ∏ μ ∈ primitiveRoots q ℂ, (1 + μ) = ∏ ν ∈ primitiveRoots q ℂ, (1 - ν) := by
        rw [prod_eq_prod_of_inj (s := primitiveRoots q ℂ) (t := primitiveRoots q ℂ) (fun x => -x)
          hg (neg_injOn _) le_rfl (fun ν => 1 - ν)]
        simp
      rw [e, prod_one_sub_primitiveRoots q (by omega), cyclotomic_eval_one_eq_exp q (by omega),
        norm_exp_real, hq2, vonMangoldt_two_mul hne (by omega)]
    · have hg : ∀ x ∈ primitiveRoots q ℂ, -x ∈ primitiveRoots n ℂ := by
        intro x hx
        rw [mem_primitiveRoots (by omega)] at hx
        rw [mem_primitiveRoots (by omega)]
        rw [hq2] at hx
        exact neg_primitive_odd hno hx
      have hcard : (primitiveRoots n ℂ).card ≤ (primitiveRoots q ℂ).card := by
        rw [Complex.card_primitiveRoots, Complex.card_primitiveRoots, hq2,
          Nat.totient_two_mul_of_odd hno]
      have e : ∏ μ ∈ primitiveRoots q ℂ, (1 + μ) = ∏ ν ∈ primitiveRoots n ℂ, (1 - ν) := by
        rw [prod_eq_prod_of_inj (s := primitiveRoots q ℂ) (t := primitiveRoots n ℂ) (fun x => -x)
          hg (neg_injOn _) hcard (fun ν => 1 - ν)]
        simp
      rw [e, prod_one_sub_primitiveRoots n (by omega), cyclotomic_eval_one_eq_exp n (by omega),
        norm_exp_real]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_even_iff_odd.2 hodd))]
    have hg : ∀ x ∈ primitiveRoots (2 * q) ℂ, -x ∈ primitiveRoots q ℂ := by
      intro x hx
      rw [mem_primitiveRoots (by omega)] at hx
      rw [mem_primitiveRoots (by omega)]
      exact neg_primitive_odd hodd hx
    have hcard : (primitiveRoots q ℂ).card ≤ (primitiveRoots (2 * q) ℂ).card := by
      rw [Complex.card_primitiveRoots, Complex.card_primitiveRoots, Nat.totient_two_mul_of_odd hodd]
    have e : ∏ μ ∈ primitiveRoots q ℂ, (1 + μ) = ∏ ν ∈ primitiveRoots (2 * q) ℂ, (1 - ν) := by
      rw [prod_eq_prod_of_inj (s := primitiveRoots (2 * q) ℂ) (t := primitiveRoots q ℂ) (fun x => -x)
        hg (neg_injOn _) hcard (fun μ => 1 + μ)]
      simp [sub_eq_add_neg]
    rw [e, prod_one_sub_primitiveRoots (2 * q) (by omega), cyclotomic_eval_one_eq_exp (2 * q) (by omega),
      norm_exp_real, vonMangoldt_eq_zero_iff.2 (not_isPrimePow_two_mul_odd hodd hq)]

/-! ### Lemma 1 -/

theorem norm_one_add_exp (t : ℝ) : ‖1 + Complex.exp (2 * π * I * t)‖ = 2 * |Real.cos (π * t)| := by
  have h : (1 : ℂ) + Complex.exp (2 * π * I * t) =
      Complex.exp (π * t * I) * (2 * Complex.cos (π * t)) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have e1 : (↑π * ↑t * I + ↑π * ↑t * I) = 2 * ↑π * I * ↑t := by ring
    have e2 : (↑π * ↑t * I + -(↑π * ↑t) * I) = 0 := by ring
    rw [e1, e2, Complex.exp_zero, add_comm]
  rw [h, norm_mul, show (↑π * ↑t * I : ℂ) = ((π * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, show (π : ℂ) * t = ((π * t : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- **Lemma 1** (paper §3.2): for `q ≥ 3` and `(a, q) = 1`,
`Σ_{(r,q)=1} log|cos(πra/q)| = −φ(q) log 2 + Λ(q/2)` for even `q`, and `−φ(q) log 2` for odd `q`.
So `w̄(q) = φ(q)^{−1} Σ log|cos(πra/q)|` does not depend on `a`, and equals `−log 2` (odd `q`) or
`−log 2 + Λ(q/2)/φ(q)` (even `q`). -/
theorem lemma_one (q a : ℕ) (hq : 3 ≤ q) (ha : a.Coprime q) :
    ∑ r ∈ (range q).filter (q.Coprime ·), Real.log |Real.cos (π * r * a / q)| =
      -(q.totient : ℝ) * Real.log 2 + (if Even q then Λ (q / 2) else 0) := by
  have hq0 : q ≠ 0 := by omega
  set ζ := Complex.exp (2 * π * I * (a / q))
  have hζ : IsPrimitiveRoot ζ q := by
    have := Complex.isPrimitiveRoot_exp_of_coprime a q hq0 ha
    convert this using 2
  have hpow : ∀ r : ℕ, ζ ^ r = Complex.exp (2 * π * I * ((r * a / q : ℝ) : ℂ)) := by
    intro r
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hcos : ∀ r : ℕ, |Real.cos (π * r * a / q)| = ‖1 + ζ ^ r‖ / 2 := by
    intro r
    rw [hpow, norm_one_add_exp, show π * ((r : ℝ) * a / q) = π * r * a / q by ring]
    ring
  have hne : ∀ r ∈ (range q).filter (q.Coprime ·), ‖1 + ζ ^ r‖ ≠ 0 := by
    intro r hr
    simp only [mem_filter] at hr
    have hpr : IsPrimitiveRoot (ζ ^ r) q := hζ.pow_of_coprime r hr.2.symm
    intro h0
    rw [norm_eq_zero] at h0
    have h1 : ζ ^ r = -1 := (neg_eq_of_add_eq_zero_right h0).symm
    have h2 : (ζ ^ r) ^ 2 = 1 := by rw [h1]; norm_num
    have := hpr.dvd_of_pow_eq_one 2 h2
    have := Nat.le_of_dvd (by omega) this
    omega
  have himg : ∏ r ∈ (range q).filter (q.Coprime ·), (1 + ζ ^ r) = ∏ μ ∈ primitiveRoots q ℂ, (1 + μ) := by
    rw [prod_eq_prod_of_inj (fun r => ζ ^ r) (s := (range q).filter (q.Coprime ·))]
    · intro r hr
      simp only [mem_filter, mem_range] at hr
      rw [mem_primitiveRoots (by omega)]
      exact hζ.pow_of_coprime r hr.2.symm
    · intro r hr r' hr' h
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
      exact hζ.pow_inj hr.1 hr'.1 h
    · rw [Complex.card_primitiveRoots, Nat.totient_eq_card_coprime]
  calc ∑ r ∈ (range q).filter (q.Coprime ·), Real.log |Real.cos (π * r * a / q)|
      = ∑ r ∈ (range q).filter (q.Coprime ·), (Real.log ‖1 + ζ ^ r‖ - Real.log 2) := by
        apply sum_congr rfl
        intro r hr
        rw [hcos, Real.log_div (hne r hr) two_ne_zero]
    _ = Real.log ‖∏ r ∈ (range q).filter (q.Coprime ·), (1 + ζ ^ r)‖ -
          (q.totient : ℝ) * Real.log 2 := by
        rw [sum_sub_distrib, norm_prod, Real.log_prod hne, sum_const, Nat.totient_eq_card_coprime,
          nsmul_eq_mul]
    _ = _ := by
        rw [himg, prod_one_add_primitiveRoots q hq, Real.log_exp]
        ring

/-- **Which arcs emerge** (paper §3.2): the centre of the arc `a/q` rises above the sea,
`w̄(q) > −log 2`, iff `q` is even and `Λ(q/2) > 0`, that is iff `q/2` is a prime power. -/
theorem arc_emerges_iff (q a : ℕ) (hq : 3 ≤ q) (ha : a.Coprime q) :
    -Real.log 2 < (∑ r ∈ (range q).filter (q.Coprime ·), Real.log |Real.cos (π * r * a / q)|) /
        q.totient ↔ Even q ∧ IsPrimePow (q / 2) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [lemma_one q a hq ha, lt_div_iff₀ hφ]
  split_ifs with he
  · simp only [he, true_and, ← vonMangoldt_pos_iff]
    constructor <;> intro h <;> linarith
  · simp only [he, false_and, iff_false, not_lt]
    linarith

/-- The emerging moduli (paper §3.2): for even `q ≥ 4`, `q/2` is a prime power iff `q = 2^k` with
`k ≥ 2` or `q = 2p^j` with `p` an odd prime and `j ≥ 1`. -/
theorem half_isPrimePow_iff (q : ℕ) (hq : Even q) (h4 : 4 ≤ q) :
    IsPrimePow (q / 2) ↔ (∃ k, 2 ≤ k ∧ q = 2 ^ k) ∨ ∃ p j, p.Prime ∧ p ≠ 2 ∧ 1 ≤ j ∧ q = 2 * p ^ j := by
  obtain ⟨n, rfl⟩ := hq
  have hn : (n + n) / 2 = n := by omega
  rw [hn, isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    by_cases hp2 : p = 2
    · subst hp2; left; exact ⟨k + 1, by omega, by rw [pow_succ]; ring⟩
    · right; exact ⟨p, k, hp, hp2, hk, by ring⟩
  · rintro (⟨k, hk, hq⟩ | ⟨p, j, hp, _, hj, hq⟩)
    · refine ⟨2, k - 1, Nat.prime_two, by omega, ?_⟩
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    · exact ⟨p, j, hp, hj, by omega⟩

end ArcsAlgo
