module

public import ArcsAlgo.Uniform.LemmaB2
set_option autoImplicit false

/-!
# Hoeffding's inequality for sums of uniform weights (paper §6.4, proof of Theorem R)

* `unif_mgf`: `Σ_{j=1}^M e^{θ(j − μ)} ≤ M e^{θ²(M−1)²/8}` (the terms `j`, `M + 1 − j` pair into
  `cosh`, and `cosh x ≤ e^{x²/2}`);
* `sum_mgf`: the generating function of `S_m` factorizes;
* `unif_tail`: `#{t ≤ ±(S_m − mμ)} ≤ M^m e^{−2t²/(m(M−1)²)}`;
* `window_compl`: `Pr(|S_m − mμ| > gσ√m) ≤ 2e^{−g²/6}`, since `2g²σ²/(M − 1)² = g²(M+1)/(6(M−1))`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- **Hoeffding's lemma for one uniform weight**: `Σ_{j=1}^M e^{θ(j − μ)} ≤ M e^{θ²(M−1)²/8}`.
The terms `j` and `M + 1 − j` pair into `cosh`, and `cosh x ≤ e^{x²/2}`. -/
theorem unif_mgf (M : ℕ) (θ : ℝ) :
    ∑ j : Fin M, exp (θ * ((j : ℝ) + 1 - muW M)) ≤ M * exp (θ ^ 2 * ((M : ℝ) - 1) ^ 2 / 8) := by
  set a : Fin M → ℝ := fun j => (j : ℝ) + 1 - muW M
  have hrev : ∀ j : Fin M, a (Fin.rev j) = -a j := by
    intro j; simp only [a, Fin.val_rev, muW]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hs : ∑ j : Fin M, exp (θ * a j) = ∑ j : Fin M, exp (-(θ * a j)) := by
    rw [← Equiv.sum_comp Fin.revPerm (fun j => exp (θ * a j))]
    refine sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, hrev]; ring_nf
  have hc : ∑ j : Fin M, exp (θ * a j) = ∑ j : Fin M, cosh (θ * a j) := by
    have : ∑ j : Fin M, cosh (θ * a j) = (∑ j : Fin M, exp (θ * a j) + ∑ j : Fin M, exp (-(θ * a j))) / 2 := by
      rw [← sum_add_distrib, sum_div]; refine sum_congr rfl fun j _ => ?_; rw [cosh_eq]
    rw [this, ← hs]; ring
  have ha : ∀ j : Fin M, a j ^ 2 ≤ ((M : ℝ) - 1) ^ 2 / 4 := by
    intro j
    have h1 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have h2 : (j : ℝ) + 1 ≤ M := by exact_mod_cast j.isLt
    simp only [a, muW]
    nlinarith
  show ∑ j : Fin M, exp (θ * a j) ≤ _
  rw [hc]
  calc ∑ j : Fin M, cosh (θ * a j) ≤ ∑ _j : Fin M, exp (θ ^ 2 * ((M : ℝ) - 1) ^ 2 / 8) := by
        refine sum_le_sum fun j _ => (cosh_le_exp_half_sq _).trans (exp_le_exp.mpr ?_)
        have := ha j
        rw [mul_pow]
        nlinarith [sq_nonneg θ]
    _ = M * exp (θ ^ 2 * ((M : ℝ) - 1) ^ 2 / 8) := by simp

/-- The moment generating function of `S_m` factorizes. -/
theorem sum_mgf (M m : ℕ) (θ : ℝ) :
    ∑ w : Fin m → Fin M, exp (θ * ((Sw w : ℝ) - m * muW M)) =
      (∑ j : Fin M, exp (θ * ((j : ℝ) + 1 - muW M))) ^ m := by
  rw [← Fin.prod_const m (∑ j : Fin M, exp (θ * ((j : ℝ) + 1 - muW M))), Fintype.prod_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [← exp_sum]; congr 1
  unfold Sw; push_cast
  rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Hoeffding, one tail**: `#{w : t ≤ ±(S_m − mμ)} ≤ M^m e^{−2t²/(m(M−1)²)}`. -/
theorem unif_tail {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    ((univ.filter fun w : Fin m → Fin M => t ≤ σ * ((Sw w : ℝ) - m * muW M)).card : ℝ) ≤
      (M : ℝ) ^ m * exp (-(2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  set θ := 4 * t / (m * ((M : ℝ) - 1) ^ 2)
  have hθ : 0 ≤ θ := by positivity
  have hmgf := unif_mgf M (σ * θ)
  have hsum := sum_mgf M m (σ * θ)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  calc ((univ.filter fun w : Fin m → Fin M => t ≤ σ * ((Sw w : ℝ) - m * muW M)).card : ℝ)
      = ∑ w ∈ univ.filter (fun w : Fin m → Fin M => t ≤ σ * ((Sw w : ℝ) - m * muW M)), (1 : ℝ) := by
        simp
    _ ≤ ∑ w ∈ univ.filter (fun w : Fin m → Fin M => t ≤ σ * ((Sw w : ℝ) - m * muW M)),
          exp (σ * θ * ((Sw w : ℝ) - m * muW M) - θ * t) := by
        refine sum_le_sum fun w hw => ?_
        have := (mem_filter.mp hw).2
        apply one_le_exp
        have : θ * t ≤ θ * (σ * ((Sw w : ℝ) - m * muW M)) := mul_le_mul_of_nonneg_left this hθ
        linarith
    _ ≤ ∑ w : Fin m → Fin M, exp (σ * θ * ((Sw w : ℝ) - m * muW M) - θ * t) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (exp_pos _).le
    _ = exp (-(θ * t)) * ∑ w : Fin m → Fin M, exp (σ * θ * ((Sw w : ℝ) - m * muW M)) := by
        rw [mul_sum]; refine sum_congr rfl fun w _ => ?_
        rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (-(θ * t)) * ((M : ℝ) * exp ((σ * θ) ^ 2 * ((M : ℝ) - 1) ^ 2 / 8)) ^ m := by
        rw [hsum]; gcongr
    _ = (M : ℝ) ^ m * exp (-(2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2))) := by
        rw [mul_pow, ← exp_nat_mul, mul_left_comm, ← exp_add]
        congr 2
        simp only [θ]
        rw [mul_pow, hσ]
        field_simp; ring

/-- **Hoeffding for the window**: `Pr(|S_m − mμ| > gσ√m) ≤ 2e^{−g²/6}`. -/
theorem window_compl {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} (hg : 0 ≤ g) :
    ((univ.filter fun w : Fin m → Fin M =>
      g * √(sig2 M) * √(m : ℝ) < |(Sw w : ℝ) - m * muW M|).card : ℝ) / (M : ℝ) ^ m ≤
      2 * exp (-(g ^ 2 / 6)) := by
  have hσ := sig2_pos hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMm : (0 : ℝ) < (M : ℝ) ^ m := by positivity
  set t := g * √(sig2 M) * √(m : ℝ)
  have ht : 0 ≤ t := by positivity
  have h1 := unif_tail hM hm ht 1 (by norm_num)
  have h2 := unif_tail hM hm ht (-1) (by norm_num)
  have hsub : (univ.filter fun w : Fin m → Fin M => t < |(Sw w : ℝ) - m * muW M|) ⊆
      (univ.filter fun w : Fin m → Fin M => t ≤ 1 * ((Sw w : ℝ) - m * muW M)) ∪
      (univ.filter fun w : Fin m → Fin M => t ≤ -1 * ((Sw w : ℝ) - m * muW M)) := by
    intro w hw
    have := (mem_filter.mp hw).2
    rw [mem_union, mem_filter, mem_filter]
    rcases le_or_gt 0 ((Sw w : ℝ) - m * muW M) with h | h
    · left; rw [abs_of_nonneg h] at this; exact ⟨mem_univ _, by linarith⟩
    · right; rw [abs_of_neg h] at this; exact ⟨mem_univ _, by linarith⟩
  have hc := card_le_card hsub
  have hc2 := card_union_le (univ.filter fun w : Fin m → Fin M => t ≤ 1 * ((Sw w : ℝ) - m * muW M))
    (univ.filter fun w : Fin m → Fin M => t ≤ -1 * ((Sw w : ℝ) - m * muW M))
  have hcR : ((univ.filter fun w : Fin m → Fin M => t < |(Sw w : ℝ) - m * muW M|).card : ℝ) ≤
      2 * ((M : ℝ) ^ m * exp (-(2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2)))) := by
    have : ((univ.filter fun w : Fin m → Fin M => t < |(Sw w : ℝ) - m * muW M|).card : ℝ) ≤
        ((univ.filter fun w : Fin m → Fin M => t ≤ 1 * ((Sw w : ℝ) - m * muW M)).card : ℝ) +
        ((univ.filter fun w : Fin m → Fin M => t ≤ -1 * ((Sw w : ℝ) - m * muW M)).card : ℝ) := by
      exact_mod_cast hc.trans hc2
    linarith
  have hexp : exp (-(2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2))) ≤ exp (-(g ^ 2 / 6)) := by
    apply exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have e : 2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2) = g ^ 2 * ((M : ℝ) + 1) / (6 * ((M : ℝ) - 1)) := by
      simp only [t]
      rw [mul_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hm0.le]
      unfold sig2
      field_simp; ring
    rw [e, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg g]
  rw [div_le_iff₀ hMm]
  calc ((univ.filter fun w : Fin m → Fin M => t < |(Sw w : ℝ) - m * muW M|).card : ℝ)
      ≤ 2 * ((M : ℝ) ^ m * exp (-(2 * t ^ 2 / (m * ((M : ℝ) - 1) ^ 2)))) := hcR
    _ ≤ 2 * ((M : ℝ) ^ m * exp (-(g ^ 2 / 6))) := by gcongr
    _ = 2 * exp (-(g ^ 2 / 6)) * (M : ℝ) ^ m := by ring

end ArcsAlgo.LLT
