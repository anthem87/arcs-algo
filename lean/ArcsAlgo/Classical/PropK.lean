module

public import ArcsAlgo.Classical.LemmaK
public import ArcsAlgo.RandomWeights
set_option autoImplicit false

/-!
# Proposition K′ (paper §6.7)

* `sum_sq_classes`: `Y_P = Σ_r Z_r² = #{(τ, τ′) : S_τ ≡ S_{τ′} (mod P)}`.
* `kprime_det`: for fixed weights, `E_P[P·Y_P] ≤ 2P₀·#{(τ, τ′) : S_τ = S_{τ′}} + 6 ln X·N²`:
  pairs with equal sums (the diagonal and `D_eq`) give at most `2P₀` each, the others at most
  `6 ln X` each by Lemma K.
* `kprime`: the same after averaging over a finitely supported law of the weights, `P` independent
  of the weights.

The only hypothesis is that of Lemma K (the Rosser–Schoenfeld bounds, cited). The multidimensional
Edgeworth expansion is not used.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.PrimeK

variable {α : Type*} [DecidableEq α]

/-- `Y_P = Σ_r Z_r² = #{(τ, τ′) : S_τ ≡ S_{τ′} (mod P)}` for the hits `H` and the half-sums `f`. -/
theorem sum_sq_classes (H : Finset α) (f : α → ℕ) {P : ℕ} (hP : 0 < P) :
    ∑ r ∈ range P, (((H.filter fun τ => f τ % P = r).card : ℝ)) ^ 2 =
      (((H ×ˢ H).filter fun x => f x.1 % P = f x.2 % P).card : ℝ) := by
  have h1 : ∀ r, (((H.filter fun τ => f τ % P = r).card : ℝ)) ^ 2 =
      ∑ τ ∈ H, ∑ τ' ∈ H, if f τ % P = r ∧ f τ' % P = r then (1 : ℝ) else 0 := by
    intro r
    rw [sq, card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_mul_sum]
    refine sum_congr rfl fun τ _ => sum_congr rfl fun τ' _ => ?_
    by_cases h1 : f τ % P = r <;> by_cases h2 : f τ' % P = r <;> simp [h1, h2]
  simp only [h1]
  rw [sum_comm]
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_product]
  refine sum_congr rfl fun τ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun τ' _ => ?_
  rw [← sum_filter]
  by_cases h : f τ % P = f τ' % P
  · rw [if_pos h]
    have : (range P).filter (fun r => f τ % P = r ∧ f τ' % P = r) = {f τ % P} := by
      ext r; simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨-, h1, -⟩; exact h1.symm
      · rintro rfl; exact ⟨Nat.mod_lt _ hP, rfl, h.symm⟩
    rw [this]; simp
  · rw [if_neg h]
    have : (range P).filter (fun r => f τ % P = r ∧ f τ' % P = r) = ∅ := by
      rw [filter_eq_empty_iff]; rintro r - ⟨h1, h2⟩; exact h (h1.trans h2.symm)
    rw [this]; simp

theorem primesIn_lt {P₀ p : ℕ} (hp : p ∈ primesIn P₀) : p < 2 * P₀ := by
  simp only [primesIn, mem_filter, mem_Ico] at hp; exact hp.1.2

theorem primesIn_pos {P₀ p : ℕ} (hp : p ∈ primesIn P₀) : 0 < p := by
  simp only [primesIn, mem_filter] at hp; exact hp.2.pos

/-- **Proposition K′, for fixed weights** (paper §6.7): with `P` uniform among the primes of
`[P₀, 2P₀)`, `E_P[P·Y_P] ≤ 2P₀·#{(τ, τ′) : S_τ = S_{τ′}} + 6 ln X · N²`, where `N = #H` and
`|S_τ − S_{τ′}| ≤ X`. The pairs with equal sums (the diagonal included, `N + D_eq` of them) give at
most `2P₀` each; the others are handled by Lemma K. -/
theorem kprime_det (hRS : RosserSchoenfeld) {P₀ : ℕ} (hP : 100 ≤ P₀) (H : Finset α) (f : α → ℕ)
    {X : ℝ} (hX1 : 1 ≤ X) (hX : ∀ τ ∈ H, ∀ τ' ∈ H, |((f τ : ℤ) - f τ' : ℝ)| ≤ X) :
    (∑ p ∈ primesIn P₀, (p : ℝ) * ∑ r ∈ range p, (((H.filter fun τ => f τ % p = r).card : ℝ)) ^ 2) /
        (primesIn P₀).card ≤
      2 * P₀ * (((H ×ˢ H).filter fun x => f x.1 = f x.2).card : ℝ) + 6 * log X * (H.card : ℝ) ^ 2 := by
  have hN := card_primesIn_ge hRS hP
  have hP' : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
  have hl : 4 < log P₀ := lt_of_lt_of_le log_100_gt (log_le_log (by norm_num) hP')
  have hNp : 0 < ((primesIn P₀).card : ℝ) := lt_of_lt_of_le (by positivity) hN
  -- rewrite `Y_P` as a sum over pairs
  have e1 : ∀ p ∈ primesIn P₀, (p : ℝ) * ∑ r ∈ range p, (((H.filter fun τ => f τ % p = r).card : ℝ)) ^ 2 =
      ∑ x ∈ H ×ˢ H, if ((p : ℤ) ∣ (f x.1 : ℤ) - f x.2) then (p : ℝ) else 0 := by
    intro p hp
    rw [sum_sq_classes H f (primesIn_pos hp), card_eq_sum_ones, Nat.cast_sum, sum_filter, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    have : f x.1 % p = f x.2 % p ↔ (p : ℤ) ∣ (f x.1 : ℤ) - f x.2 := by
      rw [← Nat.ModEq, Nat.modEq_iff_dvd, ← dvd_neg, neg_sub]
    by_cases h : f x.1 % p = f x.2 % p
    · rw [if_pos h, if_pos (this.mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; ring
  rw [sum_congr rfl e1, sum_comm, sum_div]
  -- each pair
  have hpair : ∀ x ∈ H ×ˢ H, (∑ p ∈ primesIn P₀, if ((p : ℤ) ∣ (f x.1 : ℤ) - f x.2) then (p : ℝ) else 0) /
      (primesIn P₀).card ≤ (if f x.1 = f x.2 then 2 * (P₀ : ℝ) else 0) + 6 * log X := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx
    have hXx := hX x.1 h1 x.2 h2
    by_cases heq : f x.1 = f x.2
    · rw [if_pos heq]
      have hlog : 0 ≤ log X := log_nonneg hX1
      have : (∑ p ∈ primesIn P₀, if ((p : ℤ) ∣ (f x.1 : ℤ) - f x.2) then (p : ℝ) else 0) ≤
          (primesIn P₀).card * (2 * P₀) := by
        calc _ ≤ ∑ _p ∈ primesIn P₀, (2 * (P₀ : ℝ)) := sum_le_sum fun p hp => by
              split_ifs
              · have := primesIn_lt hp; exact_mod_cast this.le
              · positivity
          _ = _ := by rw [sum_const, nsmul_eq_mul]
      rw [div_le_iff₀ hNp]; nlinarith
    · rw [if_neg heq, zero_add]
      have hΔ : ((f x.1 : ℤ) - f x.2) ≠ 0 := fun h => heq (by omega)
      have := lemmaK hRS hP hΔ (X := X) (by push_cast; exact hXx)
      unfold expPdiv at this; exact this
  calc ∑ x ∈ H ×ˢ H, (∑ p ∈ primesIn P₀, if ((p : ℤ) ∣ (f x.1 : ℤ) - f x.2) then (p : ℝ) else 0) /
        (primesIn P₀).card
      ≤ ∑ x ∈ H ×ˢ H, ((if f x.1 = f x.2 then 2 * (P₀ : ℝ) else 0) + 6 * log X) := sum_le_sum hpair
    _ = 2 * P₀ * (((H ×ˢ H).filter fun x => f x.1 = f x.2).card : ℝ) + 6 * log X * (H.card : ℝ) ^ 2 := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_product, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast; ring

/-- **Proposition K′** (paper §6.7), for a finitely supported law of the weights (outcomes `w ∈ s_W`
with probabilities `q w`) and `P` uniform among the primes of `[P₀, 2P₀)`, independent of the
weights: `E[P·Y_P] ≤ 2P₀·E#{(τ, τ′) : S_τ = S_{τ′}} + 6 ln X·E N²`, where the pairs with equal sums
are the diagonal (`E N`) and `D_eq`. With Lemma J (`roundSuccess_ge`), whose denominator is this
`E[P·Y_P]`, it gives `Pr(round succeeds) ≥ (E N)²/(2P₀(E N + D_eq) + 6 ln X·E N²)`. -/
theorem kprime (hRS : RosserSchoenfeld) {P₀ : ℕ} (hP : 100 ≤ P₀) {W : Type*} (sW : Finset W)
    (q : W → ℝ) (hq : ∀ w ∈ sW, 0 ≤ q w) (H : W → Finset α) (f : W → α → ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hX : ∀ w ∈ sW, ∀ τ ∈ H w, ∀ τ' ∈ H w, |((f w τ : ℤ) - f w τ' : ℝ)| ≤ X) :
    ∑ w ∈ sW, q w * ((∑ p ∈ primesIn P₀, (p : ℝ) *
        ∑ r ∈ range p, (((H w).filter fun τ => f w τ % p = r).card : ℝ) ^ 2) / (primesIn P₀).card) ≤
      2 * P₀ * ∑ w ∈ sW, q w * ((((H w) ×ˢ (H w)).filter fun x => f w x.1 = f w x.2).card : ℝ) +
        6 * log X * ∑ w ∈ sW, q w * ((H w).card : ℝ) ^ 2 := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun w hw => ?_
  have := kprime_det hRS hP (H w) (f w) hX1 (hX w hw)
  have hqw := hq w hw
  nlinarith

end ArcsAlgo.PrimeK
