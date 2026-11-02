module

public import ArcsAlgo.Chain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Chebyshev
set_option autoImplicit false

/-!
# Rigorous versions of the algorithm: finite parts (paper §6)

* `Z_sq_split` (Lemma B‴, the exact identity behind it): splitting a pair of sign vectors into the
  positions where they agree and those where they differ,
  `Z_E(u)² = Σ_{D ⊆ E} Z_{E∖D}(u) · Z_D(0)`.
* `cos_pow_four` and `mean_cos_pow_four` (Theorem LV): `cos⁴x = 3/8 + cos 2x/2 + cos 4x/8`, hence
  `E cos⁴(πwθ) = 3/8 + Re D(θ)/2 + Re D(2θ)/8`.
-/

@[expose] public section

namespace ArcsAlgo.RandomWeights

open Finset

/-! ### Lemma B‴ -/

section Signs

variable {ι : Type*} [DecidableEq ι] (w : ι → ℤ)

/-- `Z_J(v)`: the number of sign vectors on `J` with `Σ_J ε_i w_i = v`; a sign vector is the set
`P ⊆ J` of its `+1` positions, and `Σ ε_i w_i = 2 Σ_P w − Σ_J w`. -/
def Zs (J : Finset ι) (v : ℤ) : ℕ :=
  (J.powerset.filter fun P => 2 * ∑ i ∈ P, w i - ∑ i ∈ J, w i = v).card

/-- **Lemma B‴, the identity** (paper §6.3): split a pair `(ε, ε′)` into the positions `E ∖ D`
where the signs agree and the positions `D` where they differ; the conditions
`Σεw = Σε′w = u` become: the agreeing part sums to `u` and the differing part to `0`. Hence
`Z_E(u)² = Σ_{D ⊆ E} Z_{E∖D}(u) Z_D(0)`. Grouping `D` by its size and averaging over the weights
given the block sums gives the conditional formula of Lemma B‴. -/
theorem Z_sq_split (E : Finset ι) (u : ℤ) :
    Zs w E u ^ 2 = ∑ D ∈ E.powerset, Zs w (E \ D) u * Zs w D 0 := by
  rw [sq, Zs, ← card_product]
  simp only [Zs, ← card_product]
  rw [← card_sigma]
  symm
  refine card_bij' (fun x _ => (x.2.1 ∪ x.2.2, x.2.1 ∪ (x.1 \ x.2.2)))
    (fun y _ => ⟨symmDiff y.1 y.2, (y.1 ∩ y.2, y.1 \ y.2)⟩) ?_ ?_ ?_ ?_
  · rintro ⟨D, Q, R⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_filter] at hx
    obtain ⟨hD, ⟨hQ, hQs⟩, ⟨hR, hRs⟩⟩ := hx
    have hQR : Disjoint Q R :=
      disjoint_of_subset_left hQ (disjoint_of_subset_right hR disjoint_sdiff_self_left)
    have hQR' : Disjoint Q (D \ R) :=
      disjoint_of_subset_left hQ (disjoint_of_subset_right sdiff_subset disjoint_sdiff_self_left)
    have hE : ∑ i ∈ E, w i = ∑ i ∈ E \ D, w i + ∑ i ∈ D, w i := (sum_sdiff hD).symm
    have hDR : ∑ i ∈ D \ R, w i = ∑ i ∈ D, w i - ∑ i ∈ R, w i := by
      rw [eq_sub_iff_add_eq, sum_sdiff hR]
    simp only [mem_product, mem_filter, mem_powerset]
    refine ⟨⟨union_subset (hQ.trans sdiff_subset) (hR.trans hD), ?_⟩,
      ⟨union_subset (hQ.trans sdiff_subset) (sdiff_subset.trans hD), ?_⟩⟩
    · rw [sum_union hQR, hE]; linarith
    · rw [sum_union hQR', hE, hDR]; linarith
  · rintro ⟨P, P'⟩ hy
    simp only [mem_product, mem_filter, mem_powerset] at hy
    obtain ⟨⟨hP, hPs⟩, ⟨hP', hP's⟩⟩ := hy
    have hD : symmDiff P P' ⊆ E := by
      intro x hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with h | h
      · exact hP h.1
      · exact hP' h.1
    have split : ∀ X Y : Finset ι, ∑ i ∈ X, w i = ∑ i ∈ X ∩ Y, w i + ∑ i ∈ X \ Y, w i := by
      intro X Y
      rw [← sum_union (disjoint_left.2 fun x h1 h2 => (mem_sdiff.1 h2).2 (mem_inter.1 h1).2)]
      congr 1; ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    have h1 := split P P'
    have h2 : ∑ i ∈ P', w i = ∑ i ∈ P ∩ P', w i + ∑ i ∈ P' \ P, w i := by
      rw [inter_comm]; exact split P' P
    have h3 : ∑ i ∈ symmDiff P P', w i = ∑ i ∈ P \ P', w i + ∑ i ∈ P' \ P, w i := by
      rw [Finset.symmDiff_def, sum_union disjoint_sdiff_sdiff]
    have hE : ∑ i ∈ E, w i = ∑ i ∈ E \ symmDiff P P', w i + ∑ i ∈ symmDiff P P', w i :=
      (sum_sdiff hD).symm
    simp only [mem_sigma, mem_powerset, mem_product, mem_filter]
    refine ⟨hD, ⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
    · intro x hx
      simp only [mem_inter] at hx
      simp only [mem_sdiff, Finset.mem_symmDiff]
      exact ⟨hP hx.1, by tauto⟩
    · intro x hx
      simp only [mem_sdiff] at hx
      simp [Finset.mem_symmDiff, hx]
  · rintro ⟨D, Q, R⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_filter] at hx
    obtain ⟨hD, ⟨hQ, _⟩, ⟨hR, _⟩⟩ := hx
    have hq : ∀ x, x ∈ Q → x ∉ D := fun x h => (mem_sdiff.1 (hQ h)).2
    have hr : ∀ x, x ∈ R → x ∈ D := fun x h => hR h
    simp only [Sigma.mk.injEq, heq_iff_eq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · ext x
      have := hq x; have := hr x
      simp only [Finset.mem_symmDiff, mem_union, mem_sdiff]
      tauto
    · ext x
      have := hq x; have := hr x
      simp only [mem_inter, mem_union, mem_sdiff]
      tauto
    · ext x
      have := hq x; have := hr x
      simp only [mem_union, mem_sdiff]
      tauto
  · rintro ⟨P, P'⟩ _
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext x
      simp only [mem_union, mem_inter, mem_sdiff]
      tauto
    · ext x
      simp only [mem_union, mem_inter, mem_sdiff, Finset.mem_symmDiff]
      tauto

end Signs

/-! ### Theorem LV: the fourth moment of a factor -/

/-- `cos⁴x = 3/8 + cos(2x)/2 + cos(4x)/8` (paper §6.6, proof of Theorem LV). -/
theorem cos_pow_four (x : ℝ) : Real.cos x ^ 4 = 3 / 8 + Real.cos (2 * x) / 2 + Real.cos (4 * x) / 8 := by
  have h1 := Real.cos_sq x
  have h2 := Real.cos_sq (2 * x)
  rw [show 2 * (2 * x) = 4 * x by ring] at h2
  calc Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
    _ = _ := by rw [h1]; nlinarith [h2]

/-- **Theorem LV, the identity** (paper §6.6): for `w` uniform in `{1, …, M}`,
`E cos⁴(πwθ) = 3/8 + Re D(θ)/2 + Re D(2θ)/8`, with `Re D(θ) = E cos(2πwθ)` the real part of
`D(θ) = E e(wθ)`. -/
theorem mean_cos_pow_four (M : ℕ) (hM : 0 < M) (θ : ℝ) :
    (∑ w ∈ Icc 1 M, Real.cos (Real.pi * w * θ) ^ 4) / M =
      3 / 8 + ((∑ w ∈ Icc 1 M, Real.cos (2 * Real.pi * w * θ)) / M) / 2 +
        ((∑ w ∈ Icc 1 M, Real.cos (2 * Real.pi * w * (2 * θ))) / M) / 8 := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have hpt : ∀ w ∈ Icc 1 M, Real.cos (Real.pi * w * θ) ^ 4 =
      3 / 8 + Real.cos (2 * Real.pi * w * θ) / 2 + Real.cos (2 * Real.pi * w * (2 * θ)) / 8 := by
    intro w _
    rw [cos_pow_four, show 2 * (Real.pi * w * θ) = 2 * Real.pi * w * θ by ring,
      show 4 * (Real.pi * w * θ) = 2 * Real.pi * w * (2 * θ) by ring]
  rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_div]
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  generalize (∑ w ∈ Icc 1 M, Real.cos (2 * Real.pi * w * θ)) = A
  generalize (∑ w ∈ Icc 1 M, Real.cos (2 * Real.pi * w * (2 * θ))) = B
  field_simp

/-! ### Lemma C (2) -/

open Classical in
/-- **Lemma C (2), first part** (paper §6.5): if all but `k` weights are divisible by `d`
(`W` is a permutation of `A ++ B` with `|A| = k` and `d ∣ b` for `b ∈ B`), at most `2^k` classes
mod `d` contain a subset sum; hence at least `d − 2^k` classes are empty. -/
theorem classes_le (A B W : List ℕ) (d : ℕ) (hB : ∀ b ∈ B, d ∣ b) (hW : W.Perm (A ++ B)) :
    ((range d).filter fun c => ∃ t, IsSubsetSum W t ∧ t % d = c).card ≤ 2 ^ A.length := by
  have hsub : ((range d).filter fun c => ∃ t, IsSubsetSum W t ∧ t % d = c) ⊆
      (A.sublists'.map fun L => L.sum % d).toFinset := by
    intro c hc
    simp only [mem_filter] at hc
    obtain ⟨_, t, ht, rfl⟩ := hc
    rw [isSubsetSum_perm hW, isSubsetSum_append] at ht
    obtain ⟨a, b, ha, hb, rfl⟩ := ht
    obtain ⟨L, hL, rfl⟩ := isSubsetSum_iff_sublist.1 ha
    obtain ⟨L', hL', rfl⟩ := isSubsetSum_iff_sublist.1 hb
    have hdvd : d ∣ L'.sum := List.dvd_sum fun x hx => hB x (hL'.subset hx)
    obtain ⟨k, hk⟩ := hdvd
    simp only [List.mem_toFinset, List.mem_map, List.mem_sublists']
    exact ⟨L, hL, by rw [hk, Nat.add_mul_mod_self_left]⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (A.sublists'.map fun L => L.sum % d).length := List.toFinset_card_le _
    _ = 2 ^ A.length := by simp

/-! ### Lemma J -/

/-- **Lemma J (averaging over the residues)** (paper §6.7), for a finitely supported law of the
weights and of `P` (outcomes `ω ∈ s` with probabilities `p ω`): with `N = Σ_r Z_r`,
`Y_P = Σ_r Z_r²` and `R_P = {r : Z_r > 0}`, the probability of success
`E[|R_P|/P]` is at least `(E N)² / E[P·Y_P]`. -/
theorem roundSuccess_ge {Ω : Type*} (s : Finset Ω) (p : Ω → ℝ) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (P : Ω → ℕ) (hP : ∀ ω ∈ s, 0 < P ω) (Z : Ω → ℕ → ℕ) :
    (∑ ω ∈ s, p ω * ∑ r ∈ range (P ω), (Z ω r : ℝ)) ^ 2 /
        (∑ ω ∈ s, p ω * P ω * ∑ r ∈ range (P ω), (Z ω r : ℝ) ^ 2) ≤
      ∑ ω ∈ s, p ω * ((range (P ω)).filter fun r => 0 < Z ω r).card / P ω := by
  classical
  set N : Ω → ℝ := fun ω => ∑ r ∈ range (P ω), (Z ω r : ℝ)
  set Y : Ω → ℝ := fun ω => ∑ r ∈ range (P ω), (Z ω r : ℝ) ^ 2
  set R : Ω → ℝ := fun ω => (((range (P ω)).filter fun r => 0 < Z ω r).card : ℝ)
  -- Cauchy–Schwarz on the support: `N² ≤ |R_P| · Y_P`
  have hCS : ∀ ω, N ω ^ 2 ≤ R ω * Y ω := by
    intro ω
    have hN : N ω = ∑ r ∈ (range (P ω)).filter fun r => 0 < Z ω r, (Z ω r : ℝ) := by
      simp only [N]; rw [sum_filter]; apply sum_congr rfl; intro r _; split_ifs with h <;> simp_all
    have hY : Y ω = ∑ r ∈ (range (P ω)).filter fun r => 0 < Z ω r, (Z ω r : ℝ) ^ 2 := by
      simp only [Y]; rw [sum_filter]; apply sum_congr rfl; intro r _; split_ifs with h <;> simp_all
    rw [hN, hY]
    exact sq_sum_le_card_mul_sum_sq
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => sum_nonneg fun _ _ => sq_nonneg _
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hNY : ∀ ω, Y ω = 0 → N ω = 0 := by
    intro ω h
    have := hCS ω
    rw [h, mul_zero] at this
    nlinarith [sq_nonneg (N ω)]
  set s' := s.filter fun ω => 0 < p ω ∧ 0 < Y ω
  have hf : ∑ ω ∈ s, p ω * N ω = ∑ ω ∈ s', p ω * N ω := by
    rw [sum_filter]; apply sum_congr rfl; intro ω hω
    split_ifs with h
    · rfl
    · push Not at h
      rcases (hp ω hω).lt_or_eq with h1 | h1
      · rw [hNY ω (le_antisymm (h h1) (hY0 ω)), mul_zero]
      · rw [← h1, zero_mul]
  have hg : ∑ ω ∈ s, p ω * P ω * Y ω = ∑ ω ∈ s', p ω * P ω * Y ω := by
    rw [sum_filter]; apply sum_congr rfl; intro ω hω
    split_ifs with h
    · rfl
    · push Not at h
      rcases (hp ω hω).lt_or_eq with h1 | h1
      · rw [le_antisymm (h h1) (hY0 ω), mul_zero]
      · rw [← h1, zero_mul, zero_mul]
  have hRhs : ∑ ω ∈ s', p ω * N ω ^ 2 / (P ω * Y ω) ≤ ∑ ω ∈ s, p ω * R ω / P ω := by
    calc ∑ ω ∈ s', p ω * N ω ^ 2 / (P ω * Y ω) ≤ ∑ ω ∈ s', p ω * R ω / P ω := by
          apply sum_le_sum; intro ω hω
          simp only [s', mem_filter] at hω
          have hPpos : (0 : ℝ) < P ω := by exact_mod_cast hP ω hω.1
          rw [div_le_div_iff₀ (mul_pos hPpos hω.2.2) hPpos]
          have := hCS ω
          nlinarith [hω.2.1.le, mul_le_mul_of_nonneg_left this (mul_nonneg hω.2.1.le hPpos.le)]
      _ ≤ ∑ ω ∈ s, p ω * R ω / P ω := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro ω hω _
          exact div_nonneg (mul_nonneg (hp ω hω) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [hf, hg]
  refine le_trans ?_ hRhs
  have hgpos : ∀ ω ∈ s', 0 < p ω * P ω * Y ω := by
    intro ω hω
    simp only [s', mem_filter] at hω
    exact mul_pos (mul_pos hω.2.1 (by exact_mod_cast hP ω hω.1)) hω.2.2
  calc _ ≤ ∑ ω ∈ s', (p ω * N ω) ^ 2 / (p ω * P ω * Y ω) := sq_sum_div_le_sum_sq_div _ _ hgpos
    _ = ∑ ω ∈ s', p ω * N ω ^ 2 / (P ω * Y ω) := by
      apply sum_congr rfl; intro ω hω
      simp only [s', mem_filter] at hω
      have : p ω ≠ 0 := hω.2.1.ne'
      field_simp

end ArcsAlgo.RandomWeights
