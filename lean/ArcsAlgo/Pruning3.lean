module

public import ArcsAlgo.LemmaC
public import ArcsAlgo.Pruning
set_option autoImplicit false

/-!
# Lemma 5.3 (3) (paper §5.7)

`lemma53_3`: by Lemma C(1), applied to the suffix, `δ_q ≤ Σ_{d′|q, d′>1} φ(d′) e^{−π²κ(d′)/(2d′²)}`;
if `κ(d′) > (2d′²/π²) ln((q − 1)/ε)` for every divisor `d′ > 1` of `q`, every term is below
`φ(d′)ε/(q − 1)` and, since `Σ_{d′|q, d′>1} φ(d′) = q − 1` (`sum_totient_gt_one`), the sum is below `ε`.
`lemma53_3_model`: in the model of `Pruning`, `q ∉ Q(ε)`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LemC

/-- `Σ_{d′ | q, d′ > 1} φ(d′) = q − 1`. -/
theorem sum_totient_gt_one {q : ℕ} (hq : 1 ≤ q) :
    ∑ d' ∈ q.divisors.filter (1 < ·), (d'.totient : ℝ) = q - 1 := by
  have h := Nat.sum_totient q
  have hsplit := sum_filter_add_sum_filter_not q.divisors (1 < ·) Nat.totient
  have h1 : q.divisors.filter (fun d' => ¬ 1 < d') = {1} := by
    ext d'; simp only [mem_filter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, h⟩
      have : d' ≠ 0 := by rintro rfl; simp at hd; omega
      omega
    · rintro rfl; exact ⟨⟨one_dvd q, by omega⟩, by omega⟩
  rw [h1, sum_singleton, Nat.totient_one] at hsplit
  have hh : ∑ x ∈ q.divisors, x.totient = q := h
  have : ∑ d' ∈ q.divisors.filter (1 < ·), d'.totient = q - 1 := by
    have h3 : ∑ d' ∈ q.divisors.filter (1 < ·), d'.totient + 1 = q := hsplit.trans hh
    omega
  rw [← Nat.cast_sum, this, Nat.cast_sub hq]; simp

/-- **Lemma 5.3 (3)** (paper §5.7), from Lemma C(1): if `k(d′) > (2d′²/π²) ln((q − 1)/ε)` for every
divisor `d′ > 1` of `q`, then every class deviates by less than `ε`:
`|q·r(c)/2^n − 1| < ε` for all `c`, so `δ_q < ε`. -/
theorem lemma53_3 {n : ℕ} (w : Fin n → ℕ) {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ d' ∈ q.divisors, 1 < d' → 2 * (d' : ℝ) ^ 2 / π ^ 2 * log ((q - 1) / ε) < kC w d') :
    ∑ d' ∈ q.divisors.filter (1 < ·), (d'.totient : ℝ) * exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) < ε ∧
      ∀ c : ℤ, |(q : ℝ) * rC w q c / 2 ^ n - 1| < ε := by
  have hq1 : (0 : ℝ) < q - 1 := by have : (2 : ℝ) ≤ q := by exact_mod_cast hq
                                   linarith
  have hterm : ∀ d' ∈ q.divisors.filter (1 < ·),
      (d'.totient : ℝ) * exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) ≤ (d'.totient : ℝ) * (ε / (q - 1)) := by
    intro d' hd'
    obtain ⟨hd, h1⟩ := mem_filter.mp hd'
    have hd0 : (0 : ℝ) < d' := by exact_mod_cast (by omega : 0 < d')
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hk := h d' hd h1
    have : -(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2)) ≤ log (ε / (q - 1)) := by
      rw [log_div hε.ne' hq1.ne', show log ε - log (q - 1) = -log ((q - 1) / ε) by
        rw [log_div hq1.ne' hε.ne']; ring, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hk
      linarith
    calc exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) ≤ exp (log (ε / (q - 1))) := exp_le_exp.mpr this
      _ = ε / (q - 1) := exp_log (by positivity)
  have hlt : ∑ d' ∈ q.divisors.filter (1 < ·), (d'.totient : ℝ) *
      exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) < ε := by
    have hne : (q.divisors.filter (1 < ·)).Nonempty :=
      ⟨q, mem_filter.mpr ⟨Nat.mem_divisors_self q (by omega), by omega⟩⟩
    have hstrict : ∃ d' ∈ q.divisors.filter (1 < ·),
        (d'.totient : ℝ) * exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) < (d'.totient : ℝ) * (ε / (q - 1)) := by
      refine ⟨q, mem_filter.mpr ⟨Nat.mem_divisors_self q (by omega), by omega⟩, ?_⟩
      apply mul_lt_mul_of_pos_left _ (by exact_mod_cast Nat.totient_pos.mpr (by omega))
      have hk := h q (Nat.mem_divisors_self q (by omega)) (by omega)
      have hd0 : (0 : ℝ) < q := by positivity
      have : -(π ^ 2 * kC w q / (2 * (q : ℝ) ^ 2)) < log (ε / (q - 1)) := by
        rw [log_div hε.ne' hq1.ne', show log ε - log (q - 1) = -log ((q - 1) / ε) by
          rw [log_div hq1.ne' hε.ne']; ring, neg_lt_neg_iff, lt_div_iff₀ (by positivity)]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hk
        linarith
      calc exp (-(π ^ 2 * kC w q / (2 * (q : ℝ) ^ 2))) < exp (log (ε / (q - 1))) := exp_lt_exp.mpr this
        _ = ε / (q - 1) := exp_log (by positivity)
    calc _ < ∑ d' ∈ q.divisors.filter (1 < ·), (d'.totient : ℝ) * (ε / (q - 1)) :=
          sum_lt_sum hterm hstrict
      _ = ε := by rw [← sum_mul, sum_totient_gt_one (by omega)]; field_simp
  refine ⟨hlt, fun c => ?_⟩
  obtain ⟨h1, h2⟩ := lemmaC1 w hq c
  linarith

/-- **Lemma 5.3 (3)** in the model of `Pruning`: if the deviation `δ_q` of the model is the
deviation of the suffix bounded by Lemma C(1), the hypothesis on `k(d′)` keeps `q` out of `Q(ε)`. -/
theorem lemma53_3_model {τ : Type*} (D : ArcsAlgo.PruningModel τ) {n : ℕ} (w : Fin n → ℕ) {q : ℕ}
    (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (hδ : D.δ q ≤ ∑ d' ∈ q.divisors.filter (1 < ·), (d'.totient : ℝ) *
      exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))))
    (h : ∀ d' ∈ q.divisors, 1 < d' → 2 * (d' : ℝ) ^ 2 / π ^ 2 * log ((q - 1) / ε) < kC w d') :
    q ∉ D.Q ε := by
  intro hQ
  have := (D.mem_Q.mp hQ).2
  have := (lemma53_3 w hq hε h).1
  linarith

end ArcsAlgo.LemC
