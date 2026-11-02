module

public import ArcsAlgo.Uniform.LemV1
public import ArcsAlgo.Uniform.LemmaB2
public import ArcsAlgo.Uniform.B2fix
set_option autoImplicit false

/-!
# Lemma V: equal half-sums (paper §6.7)

For `𝒫₁` with a half `A` of size `⌊m/2⌋` and complement `B`, `D_eq` (`DeqA`) sums `pairPA` over
ordered pairs `x ≠ x′`.

* `count_sameA`, `count_sameB`, `count_compl`: the numbers of `x′` with `x′ ∩ A = x ∩ A`,
  `x′ ∖ A = x ∖ A`, `x′ = E ∖ x` are `2^{|B|}`, `2^{|A|}`, `1`.
* `sum_pairPA`: from `pairPA_bound`, `D_eq ≤ 2^m(2^{|B|} + 2^{|A|} + 1)/M³ + 4^m/M⁴`.
* `three_halves`: `2^{m−⌊m/2⌋} + 2^{⌊m/2⌋} + 1 ≤ 3·2^{m/2}`.
* `lemmaV`: uniformly in `M ≥ 2` and in the window, `D_eq/λ ≤ 0.72 e^{g²/2} m (3ψ + ψ²)(1 + ε)`
  for `m ≥ m₀(g, ε)`, `ψ = 2^{m/2}/M`. The paper prints `e^{λ²/2}`; the factor is `e^{g²/2}`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

variable {m : ℕ}

theorem count_sameA (A x : Finset (Fin m)) :
    ∑ y : Finset (Fin m), (if x ∩ A = y ∩ A then (1 : ℝ) else 0) = 2 ^ (m - A.card) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have : ((univ : Finset (Finset (Fin m))).filter fun y => x ∩ A = y ∩ A).card = (Aᶜ).powerset.card := by
    apply card_bij' (fun y _ => y \ A) (fun z _ => (x ∩ A) ∪ z)
    · intro y _; simp only [mem_powerset]; intro i hi; simp at hi ⊢; exact hi.2
    · intro z hz
      simp only [mem_powerset] at hz
      simp only [mem_filter, mem_univ, true_and]
      ext i; simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inl ⟨h1, h2⟩, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · have := hz h1; simp at this; exact absurd h2 this
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      ext i; simp only [mem_union, mem_sdiff]
      constructor
      · rintro (h | h)
        · have : i ∈ y ∩ A := hy ▸ h; exact (mem_inter.mp this).1
        · exact h.1
      · intro hi; by_cases hA : i ∈ A
        · left; rw [hy]; exact mem_inter.mpr ⟨hi, hA⟩
        · right; exact ⟨hi, hA⟩
    · intro z hz
      simp only [mem_powerset] at hz
      ext i; simp only [mem_sdiff, mem_union, mem_inter]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1.2 h2
        · exact h1
      · intro h; have := hz h; simp at this; exact ⟨Or.inr h, this⟩
  rw [this, card_powerset, card_compl, Fintype.card_fin]; push_cast; rfl

theorem count_sameB (A x : Finset (Fin m)) :
    ∑ y : Finset (Fin m), (if x \ A = y \ A then (1 : ℝ) else 0) = 2 ^ A.card := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have : ((univ : Finset (Finset (Fin m))).filter fun y => x \ A = y \ A).card = A.powerset.card := by
    apply card_bij' (fun y _ => y ∩ A) (fun z _ => (x \ A) ∪ z)
    · intro y _; simp only [mem_powerset]; exact inter_subset_right
    · intro z hz
      simp only [mem_powerset] at hz
      simp only [mem_filter, mem_univ, true_and]
      ext i; simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inl ⟨h1, h2⟩, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd (hz h1) h2
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      ext i; simp only [mem_union, mem_inter]
      constructor
      · rintro (h | h)
        · have : i ∈ y \ A := hy ▸ h; exact (mem_sdiff.mp this).1
        · exact h.1
      · intro hi; by_cases hA : i ∈ A
        · right; exact ⟨hi, hA⟩
        · left; rw [hy]; exact mem_sdiff.mpr ⟨hi, hA⟩
    · intro z hz
      simp only [mem_powerset] at hz
      ext i; simp only [mem_inter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h2 h1.2
        · exact h1
      · intro h; exact ⟨Or.inr h, hz h⟩
  rw [this, card_powerset]; push_cast; rfl

theorem count_compl (x : Finset (Fin m)) :
    ∑ y : Finset (Fin m), (if y = xᶜ then (1 : ℝ) else 0) = 1 := by
  rw [sum_ite_eq']; simp

/-- `D_eq · Pr(S_E = s)`: the sum over the pairs `x ≠ x′`. -/
noncomputable def DeqA (M m : ℕ) (A : Finset (Fin m)) (a s : ℤ) : ℝ :=
  (∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, pairPA M m A x y a s) / lawS M m s

/-- **The sum over the pairs of Lemma V**:
`Σ_{x≠x′} Pr ≤ (2^{2m−h} + 2^{m+h} + 2^m)M⁻³ + 4^m M⁻⁴`, `h = |A|`. -/
theorem sum_pairPA {M : ℕ} (hM : 0 < M) {A : Finset (Fin m)} (hA : A.Nonempty) (hB : Aᶜ.Nonempty)
    (a s : ℤ) :
    ∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, pairPA M m A x y a s ≤
      2 ^ m * (2 ^ (m - A.card) + 2 ^ A.card + 1) / (M : ℝ) ^ 3 + 4 ^ m / (M : ℝ) ^ 4 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : ∀ x y : Finset (Fin m), 0 ≤ 1 / (M : ℝ) ^ 3 * ((if x ∩ A = y ∩ A then 1 else 0) +
      (if x \ A = y \ A then 1 else 0) + (if y = xᶜ then 1 else 0)) + 1 / (M : ℝ) ^ 4 := by
    intro x y
    have : (0 : ℝ) ≤ (if x ∩ A = y ∩ A then 1 else 0) + (if x \ A = y \ A then 1 else 0) +
        (if y = xᶜ then 1 else 0) := by
      have h1 : (0 : ℝ) ≤ if x ∩ A = y ∩ A then 1 else 0 := by split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ if x \ A = y \ A then 1 else 0 := by split_ifs <;> norm_num
      have h3 : (0 : ℝ) ≤ if y = xᶜ then 1 else 0 := by split_ifs <;> norm_num
      linarith
    positivity
  calc ∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, pairPA M m A x y a s
      ≤ ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), (1 / (M : ℝ) ^ 3 *
          ((if x ∩ A = y ∩ A then 1 else 0) + (if x \ A = y \ A then 1 else 0) +
            (if y = xᶜ then 1 else 0)) + 1 / (M : ℝ) ^ 4) := by
        refine sum_le_sum fun x _ => ?_
        calc ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, pairPA M m A x y a s
            ≤ ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, (1 / (M : ℝ) ^ 3 *
              ((if x ∩ A = y ∩ A then 1 else 0) + (if x \ A = y \ A then 1 else 0) +
                (if y = xᶜ then 1 else 0)) + 1 / (M : ℝ) ^ 4) :=
              sum_le_sum fun y hy => pairPA_bound hM hA hB (Ne.symm (mem_erase.mp hy).1) a s
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun y _ _ => hb x y
    _ = 2 ^ m * (2 ^ (m - A.card) + 2 ^ A.card + 1) / (M : ℝ) ^ 3 + 4 ^ m / (M : ℝ) ^ 4 := by
        simp only [sum_add_distrib, ← mul_sum, count_sameA, count_sameB, count_compl, sum_const,
          card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
        rw [e4]; ring

theorem three_halves (m : ℕ) : (2 : ℝ) ^ (m - m / 2) + 2 ^ (m / 2) + 1 ≤ 3 * √((2 : ℝ) ^ m) := by
  have hs : ∀ k : ℕ, √((2 : ℝ) ^ (2 * k)) = 2 ^ k := fun k => by
    rw [show (2 : ℝ) ^ (2 * k) = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm], Real.sqrt_sq (by positivity)]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h1 : (k + k) / 2 = k := by omega
    have h2 : k + k - k = k := by omega
    rw [h1, h2, show k + k = 2 * k by ring, hs]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  · subst hk
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 - k = k + 1 := by omega
    rw [h1, h2]
    have hs2 : √((2 : ℝ) ^ (2 * k + 1)) = 2 ^ k * √2 := by
      rw [pow_succ, Real.sqrt_mul (by positivity), hs]
    rw [hs2, pow_succ]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hs2' : (1.41 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **Lemma V (equal half-sums)** (paper §6.7): for `𝒫₁` with a half `A` of size `⌊m/2⌋`,
`ψ = 2^{m/2}/M`, uniformly in `M ≥ 2` and in the window, for `m ≥ m₀(g, ε)`,
`D_eq/λ ≤ 0.72 e^{g²/2} m (3ψ + ψ²)(1 + ε)`. The paper prints `e^{λ²/2}`; the factor is `e^{g²/2}`,
from `Pr(S_E = s) ≥ e^{−g²/2}/(σ√(2πm))` in the window (T3). No hypothesis. -/
theorem lemmaV {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      DeqA M m A a s / lamB M m s u ≤
        0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) * (1 + ε) := by
  set ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set ε₁ := ε' / 4
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg hε₁
  set m₂ := ⌈17 * √(2 * π) * exp (g ^ 2 / 2) / ε₁⌉₊
  refine ⟨max (max m₁ m₂) 2, fun M m hM hm A hA s u a ha hw hu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hM0 : 0 < M := by omega
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hσ := sig2_pos hM
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsu : (2 : ℤ) ∣ u - s := ⟨a - s, by linarith⟩
  -- the halves are non-empty
  have hAne : A.Nonempty := card_pos.mp (by omega)
  have hBne : Aᶜ.Nonempty := card_pos.mp (by rw [card_compl, Fintype.card_fin]; omega)
  -- `λ ≥ (1 − ε₁) λ_m`
  have hlm := lamM_pos hM (by omega : 1 ≤ m)
  have hl := h₁ M m hM hm1 s u hw hu hsu
  have hlam : (1 - ε₁) * lamM M m ≤ lamB M m s u := by
    have := (abs_le.mp hl).1
    rw [div_sub_one hlm.ne', le_div_iff₀ hlm] at this; linarith
  -- `p ≥ (1 − ε₁) g_m(s)`
  have hdel : del2 g m ≤ ε₁ := by
    unfold del2
    rw [div_le_iff₀ hmR]
    have : 17 * √(2 * π) * exp (g ^ 2 / 2) / ε₁ ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm2)
    rw [div_le_iff₀ hε₁] at this; linarith
  have hgm0 := gm_ge hM (by omega : 1 ≤ m) hw
  have hgm : 0 < gaussB M m s := lt_of_lt_of_le (by positivity) hgm0
  have hrel := law_rel hM hm0 hw
  have hp : (1 - ε₁) * gaussB M m s ≤ lawS M m s := by
    have := (abs_le.mp hrel).1
    rw [div_sub_one hgm.ne', le_div_iff₀ hgm] at this
    have := mul_le_mul_of_nonneg_right hdel hgm.le
    linarith
  have hε₁1 : ε₁ ≤ 1 / 4 := by simp only [ε₁]; linarith
  have hp0 : 0 < lawS M m s := lt_of_lt_of_le (by have : 0 < 1 - ε₁ := by linarith
                                                  positivity) hp
  have hlam0 : 0 < lamB M m s u := lt_of_lt_of_le (by have : 0 < 1 - ε₁ := by linarith
                                                      positivity) hlam
  -- the sum over the pairs
  have hT := sum_pairPA hM0 hAne hBne a s
  rw [hA] at hT
  set ψ := √((2 : ℝ) ^ m) / M
  have hψ2 : ψ ^ 2 = 2 ^ m / (M : ℝ) ^ 2 := by
    simp only [ψ]; rw [div_pow, Real.sq_sqrt (by positivity)]
  have hT' : 2 ^ m * (2 ^ (m - m / 2) + 2 ^ (m / 2) + 1) / (M : ℝ) ^ 3 + 4 ^ m / (M : ℝ) ^ 4 ≤
      2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) := by
    have h3 := three_halves m
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4, hψ2]
    simp only [ψ]
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have : 2 ^ m * (2 ^ (m - m / 2) + 2 ^ (m / 2) + 1) / (M : ℝ) ^ 3 ≤
        2 ^ m * (3 * √((2 : ℝ) ^ m)) / (M : ℝ) ^ 3 := by gcongr
    have e : 2 ^ m / (M : ℝ) ^ 2 * (3 * (√((2 : ℝ) ^ m) / M) + 2 ^ m / (M : ℝ) ^ 2) =
        2 ^ m * (3 * √((2 : ℝ) ^ m)) / (M : ℝ) ^ 3 + 2 ^ m * 2 ^ m / (M : ℝ) ^ 4 := by
      field_simp
    rw [e]; linarith
  -- `p λ ≥ (1 − ε₁)² g_m(s) λ_m`
  have hpl : (1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m ≤
      lawS M m s * lamB M m s u := by
    have h1 : 0 < 1 - ε₁ := by linarith
    calc (1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m
        = ((1 - ε₁) * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ))))) *
          ((1 - ε₁) * lamM M m) := by ring
      _ ≤ ((1 - ε₁) * gaussB M m s) * ((1 - ε₁) * lamM M m) := by
          gcongr; rw [Real.exp_neg]; exact hgm0
      _ ≤ lawS M m s * lamB M m s u := mul_le_mul hp hlam (by positivity) hp0.le
  -- the constants
  have hσM : √(sig2 M) ≤ M / √12 := by
    rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
    unfold sig2; linarith
  have hcM : cMB M ≤ 5 / 8 := by
    unfold cMB
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : 1 / (6 * (M : ℝ) ^ 2) ≤ 1 / 24 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hlamM : 2 ^ m / (M * √(2 * π * m * (5 / 8))) * 2 ≤ lamM M m := by
    unfold lamM
    have hc0 : 0 < cMB M := by unfold cMB; positivity
    have hs1 : √(2 * π * m * cMB M) ≤ √(2 * π * m * (5 / 8)) := Real.sqrt_le_sqrt (by
      have : 0 < 2 * π * m := by positivity
      nlinarith)
    rw [pow_succ]
    have : 0 < √(2 * π * m * cMB M) := Real.sqrt_pos.mpr (by positivity)
    calc 2 ^ m / (↑M * √(2 * π * ↑m * (5 / 8))) * 2 = 2 ^ m * 2 / (↑M * √(2 * π * ↑m * (5 / 8))) := by ring
      _ ≤ 2 ^ m * 2 / (↑M * √(2 * π * ↑m * cMB M)) := by gcongr
  -- assembling
  unfold DeqA
  rw [div_div, div_le_iff₀ (mul_pos hp0 hlam0)]
  refine hT.trans (hT'.trans ?_)
  have hK : (1 : ℝ) ≤ 0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8))) := by
    rw [le_div_iff₀ (by positivity), ← Real.sqrt_mul (by positivity)]
    have h12 : (3.46 : ℝ) ≤ √12 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [one_mul, Real.sqrt_le_left (by positivity)]
    have hpi : π * π < 3.15 * 3.15 := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2
    have h12' : (3.46 : ℝ) * 3.46 ≤ √12 * √12 := mul_self_le_mul_self (by norm_num) h12
    have : 2 * π * (2 * π * (5 / 8)) ≤ (0.72 * (2 * 3.46)) ^ 2 := by nlinarith
    nlinarith
  have h1e : 1 ≤ (1 + ε) * (1 - ε₁) ^ 2 := by
    have : 1 + ε' ≤ 1 + ε := by simp only [ε']; linarith [min_le_left ε 1]
    have h2 : 1 ≤ (1 + ε') * (1 - ε₁) ^ 2 := by
      have hq : 0 ≤ 8 - 7 * ε' + ε' ^ 2 := by nlinarith
      have he : (1 + ε') * (1 - ε' / 4) ^ 2 = 1 + ε' * (8 - 7 * ε' + ε' ^ 2) / 16 := by ring
      simp only [ε₁]; rw [he]
      have := mul_nonneg hε'.le hq; linarith
    exact h2.trans (mul_le_mul_of_nonneg_right this (sq_nonneg _))
  have hsm : √(2 * π * m * (5 / 8)) = √(2 * π * (5 / 8)) * √(m : ℝ) := by
    rw [show 2 * π * m * (5 / 8) = 2 * π * (5 / 8) * m by ring, Real.sqrt_mul (by positivity)]
  have hmm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hmR.le
  have hψ0 : 0 ≤ 3 * ψ + ψ ^ 2 := by simp only [ψ]; positivity
  have hE : exp (g ^ 2 / 2) * exp (-(g ^ 2 / 2)) = 1 := by rw [← exp_add]; simp
  -- `2^m/M² (3ψ+ψ²) ≤ R · (1−ε₁)² g λ_m`, then `≤ R · p λ`
  have hlow : 2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) ≤
      0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) * (1 + ε) *
        ((1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m) := by
    have hlam2 : (1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (M / √12 * √(m : ℝ)))) *
        (2 ^ m / (M * √(2 * π * m * (5 / 8))) * 2) ≤
        (1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) * lamM M m := by
      have : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
      gcongr
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hlam2 (by positivity))
    rw [hsm]
    have e : 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) * (1 + ε) *
        ((1 - ε₁) ^ 2 * (exp (-(g ^ 2 / 2)) / (√(2 * π) * (M / √12 * √(m : ℝ)))) *
          (2 ^ m / (M * (√(2 * π * (5 / 8)) * √(m : ℝ))) * 2)) =
        2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) *
          ((1 + ε) * (1 - ε₁) ^ 2 * (0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8))))) *
          (exp (g ^ 2 / 2) * exp (-(g ^ 2 / 2))) * (m / (√(m : ℝ) * √(m : ℝ))) := by
      field_simp
    rw [e, hE, hmm, div_self hmR.ne', mul_one, mul_one]
    have hA0 : 0 ≤ 2 ^ m / (M : ℝ) ^ 2 * (3 * ψ + ψ ^ 2) := by positivity
    have : 1 ≤ (1 + ε) * (1 - ε₁) ^ 2 * (0.72 * (2 * √12) / (√(2 * π) * √(2 * π * (5 / 8)))) := by
      nlinarith
    nlinarith
  refine hlow.trans ?_
  apply mul_le_mul_of_nonneg_left hpl
  positivity

end ArcsAlgo.LLT
