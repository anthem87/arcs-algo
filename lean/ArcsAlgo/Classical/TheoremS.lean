module

public import ArcsAlgo.Classical.Prop30
public import Mathlib.NumberTheory.EulerProduct.Basic
set_option autoImplicit false

/-!
# Theorem S: no last sign change (paper §4.3)

* `summable_primePow_tail`, `ppTail ψ r s = Σ_{p, k} ψ(p^{k+r}) Λ(p^{k+r}) p^{−(k+r)s}`,
  `differentiableOn_ppTail`: the part `j ≥ r` of `−L′/L(s, ψ)` is holomorphic on `Re s > 1/r`.
* `LSeries_twist_vonMangoldt_split`, `ppTail_two_split`: `−L′/L(w, ψ) = P₁ + P₂ + R₃` (primes,
  squares of primes, the rest), via Mathlib's reindexing over prime powers.
* `thmS_orders_of_upper_bound`: from `H(N) ≤ C N^θ` (`θ ≥ 1/3`) and the real-segment conditions,
  `Σ_χ A_χ m_χ(ρ) = Σ_χ (A_χ/2) m′_χ(ρ)` at every `ρ` with `Re ρ > θ`, where `m′` is the order of
  `L(2s, χ²)`. The terms `k = 2` of the paper's `D = Σ_k μ(k)k^{−1} Σ_χ A_χ log L(ks, χ^k)` are a second
  family in `landau_zero_engine`; `k ≥ 3` is the tail `R₃`, absolutely convergent on `Re s > 1/3`.
  This needs `χ² ≠ χ₀` (for `q = 14`, `χ² = χ̄`); for `q = 8, 10` the pole of `L(2s, χ₀)` at
  `s = 1/2` is the Chebyshev bias, as in the paper.
* `thmS_not_eventually_upper`, `thmS_not_eventually_lower` (`H = Ω±(N^θ)` for every `θ < 1/2`),
  `thmS_sign_changes`.
* `pair_comb_ne_zero`: for `X = {χ, χ̄}`, `A_χ̄ = conj A_χ` and `Re A_χ ≠ 0`, the multiplicities at a
  zero never cancel.

Explicit hypotheses, as in the paper's proof: (R) on `(1/3, 1]` for `χ` and on `(2/3, 1]` for `χ²`
(the paper obtains `[1/3, 1/2]` from the functional equation and `(1/2, 1]` from the Arb
certificate); a zero `ρ₀` of some `L(s, χ)` with `Re ρ₀ ≥ 1/2`; the non-cancellation
`Σ_χ A_χ m_χ(ρ₀) ≠ 0` at `ρ₀` (from `pair_comb_ne_zero` and the numerical value of `A_χ`).
-/

@[expose] public section

namespace ArcsAlgo.Classical

open Complex Filter Topology Set LSeries ArithmeticFunction

/-- `Σ_{p, k} log p · (p^{−σ})^{k+r} < ∞` for `σ > 1/r` (the prime powers `p^j`, `j ≥ r`). -/
theorem summable_primePow_tail (r : ℕ) {σ : ℝ} (hσ : 1 < r * σ) :
    Summable fun pk : Nat.Primes × ℕ =>
      Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ (pk.2 + r) := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact absurd hσ (by simp [h])
    · exact h
  have hσ0 : 0 < σ := by
    by_contra h; push Not at h
    have : (r : ℝ) * σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) h
    linarith
  have hp0 : ∀ p : Nat.Primes, 0 < (p : ℝ) ^ (-σ) := fun p =>
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hp1 : ∀ p : Nat.Primes, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := fun p =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlt1 : ∀ p : Nat.Primes, (p : ℝ) ^ (-σ) < 1 := fun p => (hp1 p).trans_lt h2
  have hlog0 : ∀ p : Nat.Primes, 0 ≤ Real.log p := fun p =>
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hval : ∀ pk : Nat.Primes × ℕ, Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ (pk.2 + r) =
      Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ r * ((pk.1 : ℝ) ^ (-σ)) ^ pk.2 := fun pk => by ring
  rw [show (fun pk : Nat.Primes × ℕ => Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ (pk.2 + r)) = _ from
    funext hval]
  have hnn : ∀ pk : Nat.Primes × ℕ,
      0 ≤ Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ r * ((pk.1 : ℝ) ^ (-σ)) ^ pk.2 :=
    fun pk => mul_nonneg (mul_nonneg (hlog0 pk.1) (pow_nonneg (hp0 pk.1).le _))
      (pow_nonneg (hp0 pk.1).le _)
  refine (summable_prod_of_nonneg hnn).2 ⟨fun p => ?_, ?_⟩
  · show Summable fun k : ℕ => Real.log p * ((p : ℝ) ^ (-σ)) ^ r * ((p : ℝ) ^ (-σ)) ^ k
    exact (summable_geometric_of_lt_one (hp0 p).le (hlt1 p)).mul_left _
  show Summable fun p : Nat.Primes =>
    ∑' k : ℕ, Real.log p * ((p : ℝ) ^ (-σ)) ^ r * ((p : ℝ) ^ (-σ)) ^ k
  have hts : ∀ p : Nat.Primes,
      ∑' k : ℕ, Real.log p * ((p : ℝ) ^ (-σ)) ^ r * ((p : ℝ) ^ (-σ)) ^ k =
        Real.log p * ((p : ℝ) ^ (-σ)) ^ r * (1 - (p : ℝ) ^ (-σ))⁻¹ := fun p => by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (hp0 p).le (hlt1 p)]
  refine (summable_congr hts).2 ?_
  set δ : ℝ := (r * σ - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  set K : ℝ := (δ * (1 - (2 : ℝ) ^ (-σ)))⁻¹
  refine ((Nat.Primes.summable_rpow.2 (show δ - r * σ < -1 by simp only [δ]; linarith)).mul_left K
    |>.of_nonneg_of_le (fun p => ?_) (fun p => ?_))
  · have := hp0 p; have := hlog0 p; have := hlt1 p
    have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
    positivity
  · have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hlog : Real.log p ≤ (p : ℝ) ^ δ / δ := Real.log_le_rpow_div hp.le hδ
    have hden0 : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
    have hden1 : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith [hlt1 p]
    have hsq : ((p : ℝ) ^ (-σ)) ^ r = (p : ℝ) ^ (-(r * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; congr 1; ring
    rw [hsq]
    have hpow : (p : ℝ) ^ δ * (p : ℝ) ^ (-(r * σ)) = (p : ℝ) ^ (δ - r * σ) := by
      rw [← Real.rpow_add hp]; ring_nf
    have h3 : 0 < (p : ℝ) ^ (-(r * σ)) := Real.rpow_pos_of_pos hp _
    calc Real.log p * (p : ℝ) ^ (-(r * σ)) * (1 - (p : ℝ) ^ (-σ))⁻¹
        ≤ ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-(r * σ)) * (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
          have hinv : (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ :=
            inv_anti₀ hden0 (by linarith [hp1 p])
          have hlogpos := hlog0 p
          calc Real.log p * (p : ℝ) ^ (-(r * σ)) * (1 - (p : ℝ) ^ (-σ))⁻¹
              ≤ ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-(r * σ)) * (1 - (p : ℝ) ^ (-σ))⁻¹ := by
                gcongr
            _ ≤ ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-(r * σ)) * (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
                gcongr
      _ = K * (p : ℝ) ^ (δ - r * σ) := by
          rw [← hpow]; simp only [K]; field_simp

/-- The term `ψ(p^{k+r}) Λ(p^{k+r}) p^{−(k+r)s}` of `−L′/L(s, ψ)` at a prime power. -/
noncomputable def ppTerm {q : ℕ} (ψ : DirichletCharacter ℂ q) (r : ℕ) (s : ℂ)
    (pk : Nat.Primes × ℕ) : ℂ :=
  term ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s ((pk.1 : ℕ) ^ (pk.2 + r))

/-- `R_r(ψ, s) = Σ_{p, k} ψ(p^{k+r}) Λ(p^{k+r}) p^{−(k+r)s}`: the part `j ≥ r` of `−L′/L`. -/
noncomputable def ppTail {q : ℕ} (ψ : DirichletCharacter ℂ q) (r : ℕ) (s : ℂ) : ℂ :=
  ∑' pk, ppTerm ψ r s pk

theorem norm_ppTerm_le {q : ℕ} (ψ : DirichletCharacter ℂ q) (r : ℕ) (s : ℂ)
    (pk : Nat.Primes × ℕ) (hr : 0 < pk.2 + r) :
    ‖ppTerm ψ r s pk‖ ≤ Real.log pk.1 * ((pk.1 : ℝ) ^ (-s.re)) ^ (pk.2 + r) := by
  have hp : (0 : ℝ) < pk.1 := by exact_mod_cast pk.1.prop.pos
  have hn : (pk.1 : ℕ) ^ (pk.2 + r) ≠ 0 := pow_ne_zero _ pk.1.prop.ne_zero
  rw [ppTerm, term_of_ne_zero hn, Pi.mul_apply, norm_div, norm_mul, Complex.norm_real,
    vonMangoldt_apply_pow hr.ne', vonMangoldt_apply_prime pk.1.prop,
    norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  rw [Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast pk.1.prop.one_lt.le))]
  have hψ : ‖(ψ ((pk.1 : ℕ) ^ (pk.2 + r) : ℕ) : ℂ)‖ ≤ 1 := ψ.norm_le_one _
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
    div_eq_mul_inv, ← Real.rpow_neg hp.le]
  calc _ ≤ 1 * Real.log pk.1 * (pk.1 : ℝ) ^ (-(((pk.2 + r : ℕ) : ℝ) * s.re)) := by
        gcongr; exact ψ.norm_le_one _
    _ = _ := by ring_nf

/-- `R_r(ψ, ·)` is holomorphic on `Re s > 1/r`. -/
theorem differentiableOn_ppTail {q : ℕ} (ψ : DirichletCharacter ℂ q) {r : ℕ} (hr : 0 < r) :
    DifferentiableOn ℂ (ppTail ψ r) {s | 1 < r * s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < r * s₀.re := hs₀
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set σ₀ : ℝ := (s₀.re + 1 / r) / 2
  have hσ₀ : 1 < r * σ₀ := by
    simp only [σ₀]; field_simp; nlinarith
  have hσ₀s : σ₀ < s₀.re := by
    have : 1 / (r : ℝ) < s₀.re := by rw [div_lt_iff₀ hr']; linarith
    simp only [σ₀]; linarith
  set U : Set ℂ := {s | σ₀ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (ppTail ψ r) U := by
    refine differentiableOn_tsum_of_summable_norm (summable_primePow_tail r hσ₀)
      (fun pk => fun s _ => ?_) hU fun pk w hw => ?_
    · have hn : (pk.1 : ℕ) ^ (pk.2 + r) ≠ 0 := pow_ne_zero _ pk.1.prop.ne_zero
      have hn' : (((pk.1 : ℕ) ^ (pk.2 + r) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
      refine DifferentiableAt.differentiableWithinAt ?_
      simp only [ppTerm, term_of_ne_zero hn]
      refine DifferentiableAt.div (differentiableAt_const _)
        (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hn')) ?_
      rw [Complex.cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _
    · have hw' : σ₀ < w.re := hw
      refine (norm_ppTerm_le ψ r w pk (by omega)).trans ?_
      have hp : (0 : ℝ) < pk.1 := by exact_mod_cast pk.1.prop.pos
      have hp1 : (1 : ℝ) ≤ pk.1 := by exact_mod_cast pk.1.prop.one_lt.le
      gcongr
  exact (hd s₀ hσ₀s).differentiableAt (hU.mem_nhds hσ₀s) |>.differentiableWithinAt

theorem summable_ppTerm {q : ℕ} (ψ : DirichletCharacter ℂ q) {r : ℕ} {s : ℂ} (hs : 1 < r * s.re) :
    Summable (ppTerm ψ r s) := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact absurd hs (by simp [h])
    · exact h
  exact Summable.of_norm_bounded (summable_primePow_tail r hs) fun pk =>
    norm_ppTerm_le ψ r s pk (by omega)

/-- **Splitting off the primes**: `−L′/L(w, ψ) = Σ_p ψ(p) log p p^{−w} + R₂(ψ, w)` on `Re w > 1`. -/
theorem LSeries_twist_vonMangoldt_split {q : ℕ} (ψ : DirichletCharacter ℂ q) {w : ℂ}
    (hw : 1 < w.re) :
    LSeries ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w =
      (∑' p : Nat.Primes, term ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w p) +
        ppTail ψ 2 w := by
  set F := term ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w
  have hF : Summable F := DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ hw
  have hsupp : Function.support F ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    apply hn
    simp only [F]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [term_of_ne_zero hn0, Pi.mul_apply, vonMangoldt_eq_zero_iff.2 h]; simp
  rw [LSeries, tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hF hsupp, ppTail,
    (summable_ppTerm ψ (r := 2) (by simp; linarith)).tsum_prod]
  rfl

/-- `R₂(ψ, w) = Σ_p ψ(p²) log p p^{−2w} + R₃(ψ, w)` on `Re w > 1/2`. -/
theorem ppTail_two_split {q : ℕ} (ψ : DirichletCharacter ℂ q) {w : ℂ} (hw : 1 < 2 * w.re) :
    ppTail ψ 2 w = (∑' p : Nat.Primes,
      term ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w ((p : ℕ) ^ 2)) + ppTail ψ 3 w := by
  have h2 := summable_ppTerm ψ (r := 2) (s := w) (by exact_mod_cast hw)
  have h3 := summable_ppTerm ψ (r := 3) (s := w) (by push_cast; linarith)
  rw [ppTail, ppTail, h2.tsum_prod, h3.tsum_prod]
  have hk : ∀ p : Nat.Primes, ∑' k, ppTerm ψ 2 w (p, k) =
      term ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w ((p : ℕ) ^ 2) +
        ∑' k, ppTerm ψ 3 w (p, k) := by
    intro p
    rw [(h2.prod_factor p).tsum_eq_zero_add]
    rfl
  rw [tsum_congr hk]
  refine Summable.tsum_add ?_ h3.prod
  have hinj : Function.Injective fun p : Nat.Primes => (p, 0) := fun a b h =>
    by simpa using congrArg Prod.fst h
  exact (h2.comp_injective hinj).congr fun p => rfl

section ThmS

open DirichletCharacter

variable {q : ℕ} [NeZero q]

theorem logDeriv_LFunction_eq (ψ : DirichletCharacter ℂ q) {w : ℂ} (hw : 1 < w.re) :
    logDeriv (LFunction ψ) w =
      -LSeries ((fun n : ℕ => (ψ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) w := by
  rw [logDeriv_apply, deriv_LFunction_eq_deriv_LSeries ψ hw, LFunction_eq_LSeries ψ hw]
  have := LSeries_twist_vonMangoldt_eq ψ hw
  rw [this, neg_div, neg_neg]

/-- The term of `χ²` at `2s` and `p` is the term of `χ` at `s` and `p²`. -/
theorem term_sq_eq (χ : DirichletCharacter ℂ q) (p : Nat.Primes) (s : ℂ) :
    term ((fun n : ℕ => ((χ ^ 2) n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) (2 * s) (p : ℕ) =
      term ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s ((p : ℕ) ^ 2) := by
  have hp := p.prop.ne_zero
  have hp2 : (p : ℕ) ^ 2 ≠ 0 := pow_ne_zero _ hp
  rw [term_of_ne_zero hp, term_of_ne_zero hp2, Pi.mul_apply, Pi.mul_apply,
    MulChar.pow_apply' χ two_ne_zero, vonMangoldt_apply_pow two_ne_zero, Nat.cast_pow, map_pow,
    show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, Complex.natCast_cpow_natCast_mul]
  push_cast; rfl

theorem LSeries_logMul_primeCoeff_eq {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (logMul fun n => (primeCoeff c n : ℂ)) s = ∑ χ ∈ X, A χ *
      ∑' p : Nat.Primes, term ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s p := by
  set f := term (logMul fun n => (primeCoeff c n : ℂ)) s
  have hsupp : Function.support f ⊆ {n | n.Prime} := by
    intro n hn
    by_contra h
    apply hn
    simp only [f]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [term_of_ne_zero hn0]; simp [logMul, primeCoeff, show ¬ n.Prime from h]
  rw [LSeries, ← tsum_subtype_eq_of_support_subset hsupp]
  have hp : ∀ p : Nat.Primes, f p = ∑ χ ∈ X, A χ *
      term ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s p := by
    intro p
    have hp0 := p.prop.ne_zero
    simp only [f, term_of_ne_zero hp0, logMul, primeCoeff, if_pos p.prop, Pi.mul_apply,
      vonMangoldt_apply_prime p.prop]
    rw [hc p p.prop, Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun χ _ => by ring
  have hsum : ∀ χ ∈ X, Summable fun p : Nat.Primes => A χ *
      term ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s p := fun χ _ =>
    ((LSeriesSummable_twist_vonMangoldt χ hs).comp_injective Subtype.val_injective).mul_left _
  rw [show (∑' x : {n : ℕ | n.Prime}, f x) = ∑' p : Nat.Primes, f p from rfl, tsum_congr hp,
    Summable.tsum_finsetSum hsum]
  exact Finset.sum_congr rfl fun χ _ => tsum_mul_left

/-- **Theorem S, the orders** (paper §4.3): with `c_p = Σ_{χ∈X} A_χ χ(p)`, `χ ≠ χ₀` and
`χ² ≠ χ₀` for `χ ∈ X`, the one-sided bound `H(N) ≤ C N^θ` with `θ ≥ 1/3`, and `L(σ, χ) ≠ 0` on
`(θ, 1]`, `L(σ, χ²) ≠ 0` on `(2θ, 1]`: at every `ρ` with `Re ρ > θ`,
`Σ_χ A_χ m_χ(ρ) = Σ_χ (A_χ/2) m′_χ(ρ)`, `m′` the order of `L(2s, χ²)`. The terms `k = 2` of
`D = Σ_k μ(k)k^{−1} Σ_χ A_χ log L(ks, χ^k)` enter as the second family; `k ≥ 3` is the
absolutely convergent tail on `Re s > 1/3`. -/
theorem thmS_orders_of_upper_bound (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hX2 : ∀ χ ∈ X, χ ^ 2 ≠ 1) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) (hc : IsCharCombination X A c) {θ C : ℝ} (hθ : 1 / 3 ≤ θ)
    (hbound : ∀ N : ℕ, 2 ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ)
    (hR1 : ∀ χ ∈ X, ∀ σ : ℝ, θ < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hR2 : ∀ χ ∈ X, ∀ σ : ℝ, 2 * θ < σ → σ ≤ 1 → LFunction (χ ^ 2) σ ≠ 0)
    {ρ : ℂ} (hρ : θ < ρ.re) :
    ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) -
      ∑ χ ∈ X, A χ / 2 * (analyticOrderNatAt (fun s => LFunction (χ ^ 2) (2 * s)) ρ : ℂ) = 0 := by
  classical
  have hK := abs_primeCoeff_le hc
  have hθ0 : 0 ≤ θ := by linarith
  set C' := max C 0
  set g := raceGap C' θ c
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    simp only [g, raceGap]
    split_ifs with ht
    · have hC' : 0 ≤ C' := le_max_right _ _
      have htθ : 0 ≤ t ^ θ := Real.rpow_nonneg (by linarith) _
      rcases lt_or_ge t 2 with h2 | h2
      · rw [primeRace_of_lt_two c h2, sub_zero]; positivity
      · set N := ⌊t⌋₊
        have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast h2)
        have hHN : primeRace c t = primeRace c N := by simp [primeRace, N]
        rw [hHN]
        have h1 := hbound N hN
        have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h2' : (N : ℝ) ^ θ ≤ t ^ θ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hθ0
        have h3 : C * (N : ℝ) ^ θ ≤ C' * (N : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ
        have h4 : C' * (N : ℝ) ^ θ ≤ C' * t ^ θ := mul_le_mul_of_nonneg_left h2' hC'
        linarith
    · exact le_rfl
  have hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0 := fun t ht => by
    simp only [g, raceGap, if_neg (not_lt.2 ht.2.le)]
  -- the two families
  set f : Bool × DirichletCharacter ℂ q → ℂ → ℂ := fun i =>
    if i.1 then (fun s => LFunction (i.2 ^ 2) (2 * s)) else LFunction i.2
  set Ai : Bool × DirichletCharacter ℂ q → ℂ := fun i => if i.1 then -(A i.2 / 2) else A i.2
  set S : Finset (Bool × DirichletCharacter ℂ q) := Finset.univ ×ˢ X
  have hsplit : ∀ F : Bool × DirichletCharacter ℂ q → ℂ,
      ∑ i ∈ S, F i = ∑ χ ∈ X, F (true, χ) + ∑ χ ∈ X, F (false, χ) := by
    intro F; rw [Finset.sum_product, Fintype.sum_bool]
  set h : ℂ → ℂ := fun s => ∑ χ ∈ X, A χ * (ppTail χ 3 s - ppTail (χ ^ 2) 2 (2 * s))
  have hfan : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) univ := by
    rintro ⟨b, χ⟩ hi _ _
    have hχ : χ ∈ X := (Finset.mem_product.1 hi).2
    cases b
    · exact (differentiable_LFunction (hX1 χ hχ)).analyticAt _
    · exact ((differentiable_LFunction (hX2 χ hχ)).comp
        (differentiable_const (2 : ℂ) |>.mul differentiable_id)).analyticAt _
  have hreal : ∀ i ∈ S, ∀ σ : ℝ, θ < σ → f i σ ≠ 0 := by
    rintro ⟨b, χ⟩ hi σ hσ
    have hχ : χ ∈ X := (Finset.mem_product.1 hi).2
    cases b
    · show LFunction χ σ ≠ 0
      rcases le_or_gt σ 1 with h' | h'
      · exact hR1 χ hχ σ hσ h'
      · exact LFunction_ne_zero_of_one_le_re χ (Or.inl (hX1 χ hχ)) (by simp; linarith)
    · show LFunction (χ ^ 2) (2 * σ) ≠ 0
      rw [show (2 : ℂ) * σ = ((2 * σ : ℝ) : ℂ) by push_cast; ring]
      rcases le_or_gt (2 * σ) 1 with h' | h'
      · exact hR2 χ hχ (2 * σ) (by linarith) h'
      · exact LFunction_ne_zero_of_one_le_re (χ ^ 2) (Or.inl (hX2 χ hχ)) (by simp; linarith)
  have hh : AnalyticOnNhd ℂ h {s | θ < s.re} := by
    have hU : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU
    have hs' : θ < s.re := hs
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.fun_sum fun χ _ => ?_)
    refine (differentiableAt_const _).mul (DifferentiableAt.sub ?_ ?_)
    · have h3 : s ∈ {s : ℂ | 1 < (3 : ℕ) * s.re} := by show 1 < ((3 : ℕ) : ℝ) * s.re; push_cast; linarith
      exact (differentiableOn_ppTail χ (by norm_num : 0 < 3) s h3).differentiableAt
        ((isOpen_lt continuous_const (continuous_const.mul Complex.continuous_re)).mem_nhds h3)
    · have h2 : 2 * s ∈ {s : ℂ | 1 < (2 : ℕ) * s.re} := by
        show 1 < ((2 : ℕ) : ℝ) * (2 * s).re; simp; linarith
      have := (differentiableOn_ppTail (χ ^ 2) (by norm_num : 0 < 2) (2 * s) h2).differentiableAt
        ((isOpen_lt continuous_const (continuous_const.mul Complex.continuous_re)).mem_nhds h2)
      exact this.comp s ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
  have hD : ∀ s : ℂ, θ + 1 < s.re →
      deriv (LSeries fun n => (primeCoeff c n : ℂ)) s = ∑ i ∈ S, Ai i * logDeriv (f i) s + h s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    have hs2 : 1 < (2 * s).re := by simp; linarith
    set b : ℕ → ℂ := fun n => (primeCoeff c n : ℂ)
    have hb1 : abscissaOfAbsConv b ≤ 1 := by
      refine abscissaOfAbsConv_le_one_of_isBigO_one (Asymptotics.IsBigO.of_bound
        (∑ χ ∈ X, ‖A χ‖) (Eventually.of_forall fun n => ?_))
      simp only [b, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
      exact abs_primeCoeff_le hc n
    rw [LSeries_deriv (hb1.trans_lt (by exact_mod_cast hs1)), LSeries_logMul_primeCoeff_eq hc hs1,
      hsplit]
    have hf2 : ∀ χ : DirichletCharacter ℂ q, logDeriv (fun s => LFunction (χ ^ 2) (2 * s)) s =
        -LSeries ((fun n : ℕ => ((χ ^ 2) n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) (2 * s) * 2 := by
      intro χ
      have hc' : (fun s => LFunction (χ ^ 2) (2 * s)) = LFunction (χ ^ 2) ∘ fun s => 2 * s := rfl
      have hg : DifferentiableAt ℂ (fun s : ℂ => 2 * s) s := by fun_prop
      have hd2 : deriv (fun s : ℂ => 2 * s) s = 2 := by
        simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).deriv
      rw [hc', logDeriv_comp (differentiableAt_LFunction _ _ (Or.inl (by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith))) hg, hd2,
        logDeriv_LFunction_eq _ hs2]
    simp only [f, Ai, h, if_true, if_false, Bool.false_eq_true, hf2,
      logDeriv_LFunction_eq _ hs1]
    have hfam : ∀ χ ∈ X,
        -(A χ / 2) * (-LSeries ((fun n : ℕ => ((χ ^ 2) n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) (2 * s) * 2)
          + A χ * -LSeries ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s
          + A χ * (ppTail χ 3 s - ppTail (χ ^ 2) 2 (2 * s)) =
        -(A χ * ∑' p : Nat.Primes, term ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s p) := by
      intro χ _
      rw [LSeries_twist_vonMangoldt_split _ hs2, LSeries_twist_vonMangoldt_split _ hs1,
        ppTail_two_split χ (by linarith)]
      simp_rw [term_sq_eq]
      ring
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl hfam,
      Finset.sum_neg_distrib]
  have hfin : ∀ i ∈ S, analyticOrderAt (f i) ρ ≠ ⊤ := by
    intro i hi
    refine (hfan i hi).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := ((θ + 1 : ℝ) : ℂ)) trivial trivial ?_
    rw [analyticOrderAt_eq_zero.2 (Or.inr (hreal i hi _ (by linarith)))]
    exact ENat.zero_ne_top
  have hmain := landau_zero_engine S Ai f h θ (θ + 1) hθ0 (by linarith) g hg0 hg1
    (locallyIntegrableOn_raceGap C' θ c hK hθ0) (-(max θ 1)) (raceGap_isBigO C' θ c hK hθ0) C'
    (LSeries fun n => (primeCoeff c n : ℂ))
    (fun σ hσ => (raceGap_mellin C' θ c hK (s := σ) (by simp; linarith) (by simp; linarith)).1)
    (fun s hs => (raceGap_mellin C' θ c hK (by linarith) (by linarith)).2)
    (fun i hi => (hfan i hi).mono (subset_univ _)) hreal hh hD hρ
    (fun i => analyticOrderNatAt (f i) ρ) (fun i hi => (Nat.cast_analyticOrderNatAt (hfin i hi)).symm)
  rw [hsplit] at hmain
  simp only [f, Ai, if_true, if_false, Bool.false_eq_true] at hmain
  rw [← hmain]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- The bound needed only eventually: `H(N) ≤ C N^θ` for `N ≥ x₀` gives `H(N) ≤ C′ N^{θ′}` for all
`N ≥ 2`, with `θ′ = max(θ, 1/3)`. -/
theorem primeRace_bound_of_eventually {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c) {θ C : ℝ}
    {x₀ : ℕ} (hb : ∀ N : ℕ, x₀ ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ) :
    ∀ N : ℕ, 2 ≤ N → primeRace c N ≤
      (max C 0 + (∑ χ ∈ X, ‖A χ‖) * x₀) * (N : ℝ) ^ (max θ (1 / 3)) := by
  intro N hN
  set K := ∑ χ ∈ X, ‖A χ‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow1 : 1 ≤ (N : ℝ) ^ (max θ (1 / 3)) :=
    Real.one_le_rpow hN1 (le_trans (by norm_num) (le_max_right _ _))
  have hθθ : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (max θ (1 / 3)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hpos : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hextra : 0 ≤ K * x₀ * (N : ℝ) ^ (max θ (1 / 3)) := by positivity
  rcases le_or_gt x₀ N with h | h
  · have h1 := hb N h
    have h2 : C * (N : ℝ) ^ θ ≤ max C 0 * (N : ℝ) ^ (max θ (1 / 3)) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos).trans
        (mul_le_mul_of_nonneg_left hθθ (le_max_right _ _))
    nlinarith
  · have h1 := (le_abs_self _).trans (abs_primeRace_le c (abs_primeCoeff_le hc)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
    have h2 : K * (N : ℝ) ≤ K * x₀ := by gcongr
    have h3 : K * (x₀ : ℝ) ≤ K * x₀ * (N : ℝ) ^ (max θ (1 / 3)) :=
      le_mul_of_one_le_right (by positivity) hpow1
    have h4 : 0 ≤ max C 0 * (N : ℝ) ^ (max θ (1 / 3)) := by
      have := le_max_right C 0; positivity
    nlinarith

/-- **Theorem S, `Ω₊`** (paper §4.3): under the hypotheses of `thmS_orders_of_upper_bound` on
`(1/3, 1]`, if some `L(s, χ)`, `χ ∈ X`, has a zero `ρ₀` with `Re ρ₀ ≥ 1/2` at which the
multiplicities do not cancel (`Σ_χ A_χ m_χ(ρ₀) ≠ 0`), then for every `θ < 1/2` there is no `C, x₀`
with `H(N) ≤ C N^θ` for all `N ≥ x₀`. -/
theorem thmS_not_eventually_upper (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hX2 : ∀ χ ∈ X, χ ^ 2 ≠ 1) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR1 : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 3 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hR2 : ∀ χ ∈ X, ∀ σ : ℝ, 2 / 3 < σ → σ ≤ 1 → LFunction (χ ^ 2) σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ := by
  rintro ⟨C, x₀, hb⟩
  set θ' := max θ (1 / 3)
  have hθ'1 : 1 / 3 ≤ θ' := le_max_right _ _
  have hθ'2 : θ' < 1 / 2 := max_lt hθ (by norm_num)
  have h := thmS_orders_of_upper_bound X hX1 hX2 A c hc hθ'1 (primeRace_bound_of_eventually hc hb)
    (fun χ hχ σ hσ h1 => hR1 χ hχ σ (by linarith) h1)
    (fun χ hχ σ hσ h1 => hR2 χ hχ σ (by linarith) h1) (ρ := ρ₀) (by linarith)
  have h0 : ∀ χ ∈ X, analyticOrderNatAt (fun s => LFunction (χ ^ 2) (2 * s)) ρ₀ = 0 := by
    intro χ hχ
    have hre : 1 ≤ (2 * ρ₀).re := by
      have : (2 * ρ₀).re = 2 * ρ₀.re := by simp
      rw [this]; linarith
    have hne : (fun s => LFunction (χ ^ 2) (2 * s)) ρ₀ ≠ 0 :=
      LFunction_ne_zero_of_one_le_re (χ ^ 2) (Or.inl (hX2 χ hχ)) hre
    have h0' : analyticOrderAt (fun s => LFunction (χ ^ 2) (2 * s)) ρ₀ = 0 :=
      analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [analyticOrderNatAt, h0']
    rfl
  have h2 : ∑ χ ∈ X, A χ / 2 *
      (analyticOrderNatAt (fun s => LFunction (χ ^ 2) (2 * s)) ρ₀ : ℂ) = 0 :=
    Finset.sum_eq_zero fun χ hχ => by rw [h0 χ hχ]; simp
  rw [h2, sub_zero] at h
  exact hN₀ h

/-- **Theorem S, `Ω₋`**: the same for the lower bound `H(N) ≥ −C N^θ`. -/
theorem thmS_not_eventually_lower (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hX2 : ∀ χ ∈ X, χ ^ 2 ≠ 1) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR1 : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 3 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hR2 : ∀ χ ∈ X, ∀ σ : ℝ, 2 / 3 < σ → σ ≤ 1 → LFunction (χ ^ 2) σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → -(C * (N : ℝ) ^ θ) ≤ primeRace c N := by
  rintro ⟨C, x₀, hb⟩
  refine thmS_not_eventually_upper X hX1 hX2 (fun χ => -A χ) (fun n => -c n) ?_ hR1 hR2 hρ₀ ?_ hθ
    ⟨C, x₀, fun N hN => by rw [primeRace_neg]; linarith [hb N hN]⟩
  · intro p hp
    push_cast
    rw [hc p hp, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  · intro h
    apply hN₀
    have : ∑ χ ∈ X, -A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) =
        -∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun χ _ => by ring
    rw [this] at h
    exact neg_eq_zero.1 h

/-- **Theorem S, sign changes**: under the same hypotheses, `H(N) > 0` and `H(N) < 0` for
arbitrarily large `N`. -/
theorem thmS_sign_changes (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hX2 : ∀ χ ∈ X, χ ^ 2 ≠ 1) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR1 : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 3 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hR2 : ∀ χ ∈ X, ∀ σ : ℝ, 2 / 3 < σ → σ ≤ 1 → LFunction (χ ^ 2) σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0) :
    (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ 0 < primeRace c N) ∧
      (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ primeRace c N < 0) := by
  constructor
  · intro x₀
    by_contra h
    push Not at h
    exact thmS_not_eventually_upper X hX1 hX2 A c hc hR1 hR2 hρ₀ hN₀ (θ := 0) (by norm_num)
      ⟨0, x₀, fun N hN => by simpa using h N hN⟩
  · intro x₀
    by_contra h
    push Not at h
    exact thmS_not_eventually_lower X hX1 hX2 A c hc hR1 hR2 hρ₀ hN₀ (θ := 0) (by norm_num)
      ⟨0, x₀, fun N hN => by simpa using h N hN⟩

/-- The non-cancellation of Theorem S for a pair `X = {χ, χ̄}` with `A_χ̄ = conj A_χ`: if
`Re A_χ ≠ 0` (equivalently `A_χ/Ā_χ` is not a negative real; for `q = 14`,
`A_χ = 0.1717 − 0.1700i`), then `A_χ m + Ā_χ m′ ≠ 0` unless `m = m′ = 0`. -/
theorem pair_comb_ne_zero {a : ℂ} (ha : a.re ≠ 0) {m₁ m₂ : ℕ} (h : m₁ ≠ 0 ∨ m₂ ≠ 0) :
    a * m₁ + (starRingEnd ℂ) a * m₂ ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
    sub_zero, Complex.conj_re, Complex.zero_re] at h1
  have h2 : a.re * ((m₁ : ℝ) + m₂) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact ha h3
  · have : m₁ + m₂ = 0 := by exact_mod_cast h3
    omega

end ThmS

end ArcsAlgo.Classical
