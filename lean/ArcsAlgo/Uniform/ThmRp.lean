module

public import ArcsAlgo.Uniform.ThmR
public import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false

/-!
# Theorem R′ (paper §6.4)

`r` disjoint endgame blocks `E₁, …, E_r` of size `m` and the rest `G`; all weights independent and
uniform in `{1, …, M}`. Round `j` includes the blocks of `K_j ∌ j` entirely (any rule that looks
only at the block sums), runs the centre rule on `G` and an exact search on `E_j`.

* `condR_round`: on `|T − S/2| ≤ S_G/2 − rmM`, every round satisfies the hypothesis of Lemma A,
  `|T_j − (S_G + S_{E_j})/2| ≤ S_G/2`, whatever blocks are included.
* `rounds_fail`: given `w_G` and the block sums, the residuals are determined and the blocks'
  internal configurations are independent, each conditioned on its sum (`card_pi_filter`), so
  `Pr(all rounds fail) ≤ 2^{−r} + r·2e^{−g²/6}` when each fails with probability `≤ 1/2` on the
  window.
* `thmRp_gen`: that bound for `λ_m ≥ 8` and `m ≥ m₀(g)` (Lemma B(1), B(3)).
* `thmRp`: with `r = ⌈log₂(2/δ)⌉` and `g = √(6 log(4r/δ))`, the failure probability is `≤ δ`.

The running time is not formalized.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

open ArcsAlgo

/-- The product of independent coordinates: `#{x : ∀ j, P_j(x_j)} = Π_j #{P_j}`. -/
theorem card_pi_filter {r : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (P : Fin r → X → Prop)
    [∀ j, DecidablePred (P j)] :
    (univ.filter fun x : Fin r → X => ∀ j, P j (x j)).card = ∏ j, (univ.filter (P j)).card := by
  rw [← Fintype.card_piFinset]
  congr 1; ext x; simp [Fintype.mem_piFinset]

theorem card_fail_le {M m : ℕ} {s u : ℤ} {c : ℝ} (hc0 : 0 ≤ c) (hc : p0B M m s u ≤ c) :
    ((univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card : ℝ) ≤ c * cntS M m s := by
  by_cases h0 : (cntS M m s : ℝ) = 0
  · have : (univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card = 0 := by
      have h0' : cntS M m s = 0 := by exact_mod_cast h0
      unfold cntS at h0'
      apply Nat.eq_zero_of_le_zero
      rw [← h0']; exact card_le_card fun w hw => by
        simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.1
    rw [this, h0]; simp
  · have : ((univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card : ℝ) =
        p0B M m s u * cntS M m s := by unfold p0B; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)

theorem sum_cntS (M m : ℕ) : ∑ s ∈ I0 m M, (cntS M m s : ℝ) = (M : ℝ) ^ m := by
  have : ∑ s ∈ I0 m M, (cntS M m s : ℝ) = ((univ : Finset (Fin m → Fin M)).card : ℝ) := by
    unfold cntS
    rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := Sw) (t := I0 m M) (fun w _ => Sw_mem w)]
  rw [this, card_univ]; simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring

/-- The doubled hypothesis of Theorem R′: `|T − S/2| ≤ S_G/2 − rmM`. -/
def condRp {h M r : ℕ} (m : ℕ) (wG : Fin h → Fin M) (b : Fin r → ℤ) (T : ℤ) : Prop :=
  |2 * T - (((wsOf wG).sum : ℤ) + ∑ k, b k)| ≤ ((wsOf wG).sum : ℤ) - 2 * r * m * M

instance {h M r m : ℕ} (wG : Fin h → Fin M) (b : Fin r → ℤ) (T : ℤ) :
    Decidable (condRp m wG b T) := by unfold condRp; infer_instance

/-- The target of round `j`: the blocks of `K_j` are included entirely. -/
def targetRp {r : ℕ} (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) : ℤ := T - ∑ k ∈ K, b k

/-- **The rounds of Theorem R′ satisfy the hypothesis of Lemma A**: whatever blocks `K_j ∌ j` are
included, `|T_j − (S_G + S_{E_j})/2| ≤ S_G/2`. -/
theorem condR_round {h M r m : ℕ} (wG : Fin h → Fin M) {b : Fin r → ℤ} {T : ℤ}
    (hb : ∀ k, 0 ≤ b k ∧ b k ≤ m * M) (hc : condRp m wG b T) (j : Fin r) {K : Finset (Fin r)}
    (hK : j ∉ K) : condR wG (targetRp T b K) (b j) := by
  unfold condR targetRp
  unfold condRp at hc
  set SG := ((wsOf wG).sum : ℤ)
  have hsplit : ∑ k, b k = b j + ∑ k ∈ univ.erase j, b k := (add_sum_erase _ _ (mem_univ j)).symm
  have hKsub : K ⊆ univ.erase j := fun k hk => mem_erase.mpr ⟨fun h => hK (h ▸ hk), mem_univ _⟩
  have hK1 : 0 ≤ ∑ k ∈ K, b k := sum_nonneg fun k _ => (hb k).1
  have hK2 : ∑ k ∈ K, b k ≤ ∑ k ∈ univ.erase j, b k :=
    sum_le_sum_of_subset_of_nonneg hKsub fun k _ _ => (hb k).1
  have hR : ∑ k ∈ univ.erase j, b k ≤ r * m * M := by
    calc ∑ k ∈ univ.erase j, b k ≤ ∑ k ∈ (univ : Finset (Fin r)), b k :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun k _ _ => (hb k).1
      _ ≤ ∑ _k : Fin r, (m * M : ℤ) := sum_le_sum fun k _ => (hb k).2
      _ = r * m * M := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have e : 2 * (T - ∑ k ∈ K, b k) - (SG + b j) = (2 * T - (SG + ∑ k, b k)) +
      (∑ k ∈ univ.erase j, b k - 2 * ∑ k ∈ K, b k) := by rw [hsplit]; ring
  rw [e]
  have h2 : |∑ k ∈ univ.erase j, b k - 2 * ∑ k ∈ K, b k| ≤ r * m * M := by
    rw [abs_le]; constructor <;> linarith
  calc |(2 * T - (SG + ∑ k, b k)) + (∑ k ∈ univ.erase j, b k - 2 * ∑ k ∈ K, b k)|
      ≤ |2 * T - (SG + ∑ k, b k)| + |∑ k ∈ univ.erase j, b k - 2 * ∑ k ∈ K, b k| := abs_add_le _ _
    _ ≤ (SG - 2 * r * m * M) + r * m * M := add_le_add hc h2
    _ ≤ SG := by
        have : (0 : ℤ) ≤ r * m * M := by positivity
        linarith

/-- The averaging over the head `G`, for a general second factor. -/
theorem fail_avg' {h M : ℕ} (hM : 0 < M) {Ω : Type*} [Fintype Ω]
    (P : (Fin h → Fin M) → Ω → Prop) [∀ a, DecidablePred (P a)] {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ wH, ((univ.filter (P wH)).card : ℝ) ≤ B * Fintype.card Ω) :
    ((univ.filter fun p : (Fin h → Fin M) × Ω => P p.1 p.2).card : ℝ) /
      ((M : ℝ) ^ h * Fintype.card Ω) ≤ B := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases hΩ : (Fintype.card Ω : ℝ) = 0
  · rw [hΩ, mul_zero, div_zero]; exact hB0
  have hΩ0 : (0 : ℝ) < Fintype.card Ω := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hΩ)
  have e : ((univ.filter fun p : (Fin h → Fin M) × Ω => P p.1 p.2).card : ℝ) =
      ∑ wH : Fin h → Fin M, ((univ.filter (P wH)).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun wH _ => ?_
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [e, div_le_iff₀ (by positivity)]
  calc ∑ wH : Fin h → Fin M, ((univ.filter (P wH)).card : ℝ) ≤ ∑ _wH : Fin h → Fin M, B * Fintype.card Ω :=
        sum_le_sum fun wH _ => hB wH
    _ = B * ((M : ℝ) ^ h * Fintype.card Ω) := by
        rw [sum_const, card_univ, nsmul_eq_mul]; simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast; ring

/-- The block sums. -/
def bsum {r m M : ℕ} (wB : Fin r → Fin m → Fin M) : Fin r → ℤ := fun j => Sw (wB j)

/-- The residual of round `j`. -/
def uRp {h M r : ℕ} (wG : Fin h → Fin M) (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) (j : Fin r) : ℤ :=
  residR wG (targetRp T b K) (b j)

theorem bsum_mem {r m M : ℕ} (wB : Fin r → Fin m → Fin M) :
    bsum wB ∈ Fintype.piFinset fun _ : Fin r => I0 m M := by
  rw [Fintype.mem_piFinset]; intro j; exact Sw_mem _

set_option maxHeartbeats 1000000 in
/-- **The failures of the rounds are conditionally independent** (paper §6.4, proof of Theorem R′):
for fixed `w_G`, if every round fails with conditional probability `≤ 1/2` on the window, then
`Pr(all rounds fail) ≤ 2^{−r} + r·2e^{−g²/6}`. -/
theorem rounds_fail {h M r m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} (hg : 0 ≤ g)
    (wG : Fin h → Fin M) (T : (Fin r → ℤ) → ℤ) (K : Fin r → (Fin r → ℤ) → Finset (Fin r))
    (hp : ∀ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M), ∀ j : Fin r,
      |(b j : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) →
      condRp m wG b (T b) → p0B M m (b j) (uRp wG (T b) b (K j b) j) ≤ 1 / 2) :
    ((univ.filter fun wB : Fin r → Fin m → Fin M => condRp m wG (bsum wB) (T (bsum wB)) ∧
        ∀ j, Zc (wB j) (uRp wG (T (bsum wB)) (bsum wB) (K j (bsum wB)) j) = 0).card : ℝ) ≤
      ((1 / 2) ^ r + r * (2 * exp (-(g ^ 2 / 6)))) * ((M : ℝ) ^ m) ^ r := by
  have hM0 : 0 < M := by omega
  have hMm : (0 : ℝ) < (M : ℝ) ^ m := by have : (0 : ℝ) < M := by exact_mod_cast hM0
                                         positivity
  set W : ℤ → Prop := fun s => |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)
  set ev := univ.filter fun wB : Fin r → Fin m → Fin M => condRp m wG (bsum wB) (T (bsum wB)) ∧
        ∀ j, Zc (wB j) (uRp wG (T (bsum wB)) (bsum wB) (K j (bsum wB)) j) = 0
  set A := univ.filter fun wB : Fin r → Fin m → Fin M => ∃ j, ¬ W (Sw (wB j))
  set B := univ.filter fun wB : Fin r → Fin m → Fin M => (∀ j, W (Sw (wB j))) ∧
    condRp m wG (bsum wB) (T (bsum wB)) ∧
      ∀ j, Zc (wB j) (uRp wG (T (bsum wB)) (bsum wB) (K j (bsum wB)) j) = 0
  have hsub : ev ⊆ A ∪ B := by
    intro wB hw
    simp only [ev, A, B, mem_filter, mem_univ, true_and, mem_union] at hw ⊢
    by_cases h : ∀ j, W (Sw (wB j))
    · right; exact ⟨h, hw⟩
    · left; push Not at h; exact h
  -- the window fails for some block
  have hA : (A.card : ℝ) ≤ r * (2 * exp (-(g ^ 2 / 6))) * ((M : ℝ) ^ m) ^ r := by
    have hAj : ∀ j : Fin r, ((univ.filter fun wB : Fin r → Fin m → Fin M => ¬ W (Sw (wB j))).card : ℝ) ≤
        2 * exp (-(g ^ 2 / 6)) * ((M : ℝ) ^ m) ^ r := by
      intro j
      have e : (univ.filter fun wB : Fin r → Fin m → Fin M => ¬ W (Sw (wB j))) =
          univ.filter fun wB : Fin r → Fin m → Fin M => ∀ k, (k = j → ¬ W (Sw (wB k))) := by
        ext wB; simp
      have hc : (univ.filter fun wB : Fin r → Fin m → Fin M => ∀ k, (k = j → ¬ W (Sw (wB k)))).card =
          ∏ k, (univ.filter fun x : Fin m → Fin M => k = j → ¬ W (Sw x)).card := by
        rw [← Fintype.card_piFinset]; congr 1; ext x; simp [Fintype.mem_piFinset]
      rw [e, hc]
      push_cast
      rw [Fintype.prod_eq_mul_prod_compl j]
      have hrest : ∀ k ∈ ({j}ᶜ : Finset (Fin r)),
          (((univ.filter fun x : Fin m → Fin M => k = j → ¬ W (Sw x)).card : ℕ) : ℝ) = (M : ℝ) ^ m := by
        intro k hk
        have hkj : k ≠ j := by simpa using hk
        have : (univ.filter fun x : Fin m → Fin M => k = j → ¬ W (Sw x)) = univ := by
          ext x; simp [hkj]
        rw [this, card_univ]; simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
      rw [prod_congr rfl hrest, prod_const, card_compl, card_singleton, Fintype.card_fin]
      have hwin := window_compl (m := m) hM hm hg
      rw [div_le_iff₀ hMm] at hwin
      have e2 : (univ.filter fun x : Fin m → Fin M => j = j → ¬ W (Sw x)) =
          univ.filter fun x : Fin m → Fin M => g * √(sig2 M) * √(m : ℝ) < |(Sw x : ℝ) - m * muW M| := by
        ext x; simp [W]
      rw [e2]
      have hr : 1 ≤ r := by have := j.isLt; omega
      have e3 : ((M : ℝ) ^ m) ^ r = (M : ℝ) ^ m * ((M : ℝ) ^ m) ^ (r - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e3]
      have : 0 ≤ ((M : ℝ) ^ m) ^ (r - 1) := by positivity
      nlinarith
    calc (A.card : ℝ) ≤ ∑ j : Fin r,
          ((univ.filter fun wB : Fin r → Fin m → Fin M => ¬ W (Sw (wB j))).card : ℝ) := by
          have : A ⊆ univ.biUnion fun j : Fin r =>
              univ.filter fun wB : Fin r → Fin m → Fin M => ¬ W (Sw (wB j)) := by
            intro wB hw
            simp only [A, mem_filter, mem_univ, true_and] at hw
            obtain ⟨j, hj⟩ := hw
            exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
          exact_mod_cast (card_le_card this).trans card_biUnion_le
      _ ≤ ∑ _j : Fin r, 2 * exp (-(g ^ 2 / 6)) * ((M : ℝ) ^ m) ^ r := sum_le_sum fun j _ => hAj j
      _ = r * (2 * exp (-(g ^ 2 / 6))) * ((M : ℝ) ^ m) ^ r := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- all blocks in the window
  have hB : (B.card : ℝ) ≤ (1 / 2) ^ r * ((M : ℝ) ^ m) ^ r := by
    rw [card_eq_sum_ones, Nat.cast_sum,
      ← sum_fiberwise_of_maps_to (g := bsum) (t := Fintype.piFinset fun _ : Fin r => I0 m M)
        (fun wB _ => bsum_mem wB)]
    have hfib : ∀ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M),
        ∑ x ∈ B.filter (fun x => bsum x = b), ((1 : ℕ) : ℝ) ≤ ∏ j, (1 / 2 * (cntS M m (b j) : ℝ)) := by
      intro b hbm
      rw [← Nat.cast_sum, ← card_eq_sum_ones]
      by_cases hb : (∀ j, W (b j)) ∧ condRp m wG b (T b)
      · have hsub : B.filter (fun x => bsum x = b) ⊆ univ.filter fun wB : Fin r → Fin m → Fin M =>
            ∀ j, (fun j (w : Fin m → Fin M) => Sw w = b j ∧
              Zc w (uRp wG (T b) b (K j b) j) = 0) j (wB j) := by
          intro x hx
          simp only [B, mem_filter, mem_univ, true_and] at hx ⊢
          obtain ⟨⟨-, -, hz⟩, hxb⟩ := hx
          intro j
          have hj : Sw (x j) = b j := by rw [← hxb]; rfl
          refine ⟨hj, ?_⟩
          have := hz j; rw [hxb] at this; exact this
        refine (Nat.cast_le.mpr (card_le_card hsub)).trans ?_
        have hc : (univ.filter fun wB : Fin r → Fin m → Fin M =>
            ∀ j, (fun j (w : Fin m → Fin M) => Sw w = b j ∧
              Zc w (uRp wG (T b) b (K j b) j) = 0) j (wB j)).card =
            ∏ j, (univ.filter fun w : Fin m → Fin M => Sw w = b j ∧
              Zc w (uRp wG (T b) b (K j b) j) = 0).card := by
          rw [← Fintype.card_piFinset]; congr 1; ext x; simp [Fintype.mem_piFinset]
        rw [hc]; push_cast
        refine Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
        exact card_fail_le (by norm_num) (hp b hbm j (hb.1 j) hb.2)
      · have : B.filter (fun x => bsum x = b) = ∅ := by
          rw [filter_eq_empty_iff]
          intro x hx hxb
          simp only [B, mem_filter, mem_univ, true_and] at hx
          apply hb
          refine ⟨fun j => ?_, ?_⟩
          · have := hx.1 j; rw [show Sw (x j) = b j by rw [← hxb]; rfl] at this; exact this
          · have := hx.2.1; rw [hxb] at this; exact this
        rw [this]; simp only [card_empty, Nat.cast_zero]
        exact prod_nonneg fun j _ => by positivity
    calc ∑ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M),
          ∑ x ∈ B.filter (fun x => bsum x = b), ((1 : ℕ) : ℝ)
        ≤ ∑ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M), ∏ j, (1 / 2 * (cntS M m (b j) : ℝ)) :=
          sum_le_sum hfib
      _ = ∏ _j : Fin r, ∑ s ∈ I0 m M, (1 / 2 * (cntS M m s : ℝ)) := by
          rw [Finset.prod_univ_sum]
      _ = (1 / 2) ^ r * ((M : ℝ) ^ m) ^ r := by
          rw [← mul_sum, sum_cntS, prod_const, card_univ, Fintype.card_fin, mul_pow]
  have hcard : (ev.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  calc (ev.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := hcard
    _ ≤ r * (2 * exp (-(g ^ 2 / 6))) * ((M : ℝ) ^ m) ^ r + (1 / 2) ^ r * ((M : ℝ) ^ m) ^ r :=
        add_le_add hA hB
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **Theorem R′, general form** (paper §6.4): `r` disjoint endgame blocks `E₁, …, E_r` of size `m`
and the rest `G`, all weights independent and uniform in `{1, …, M}`; the target `T` depends on
`w_G` and the block sums, and round `j` includes the blocks `K_j ∌ j` (any rule that looks only at
the block sums), then runs the centre rule on `G` and an exact search on `E_j`. On the event
`|T − S/2| ≤ S_G/2 − rmM`, for `λ_m ≥ 8` and `m ≥ m₀(g)`:
`Pr(every round fails) ≤ 2^{−r} + r·2e^{−g²/6}`. -/
theorem thmRp_gen {g : ℝ} (hg : 0 ≤ g) :
    ∃ m₀ : ℕ, ∀ M h m r : ℕ, 2 ≤ M → m₀ ≤ m → 8 ≤ lamM M m →
      ∀ (T : (Fin h → Fin M) → (Fin r → ℤ) → ℤ) (K : Fin r → (Fin r → ℤ) → Finset (Fin r)),
      (∀ j b, j ∉ K j b) →
      ((univ.filter fun p : (Fin h → Fin M) × (Fin r → Fin m → Fin M) =>
          condRp m p.1 (bsum p.2) (T p.1 (bsum p.2)) ∧
            ∀ j, Zc (p.2 j) (uRp p.1 (T p.1 (bsum p.2)) (bsum p.2) (K j (bsum p.2)) j) = 0).card : ℝ) /
        ((M : ℝ) ^ h * Fintype.card (Fin r → Fin m → Fin M)) ≤
        (1 / 2) ^ r + r * (2 * exp (-(g ^ 2 / 6))) := by
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg (ε := 1 / 4) (by norm_num)
  obtain ⟨m₂, h₂⟩ := lemmaB3_unif hg (ε := 1 / 6) (by norm_num)
  refine ⟨max (max m₁ m₂) 1, fun M h m r hM hm hl8 T K hK => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hM0 : 0 < M := by omega
  have hcard : (Fintype.card (Fin r → Fin m → Fin M) : ℝ) = ((M : ℝ) ^ m) ^ r := by
    simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  refine fail_avg' hM0 (fun wG (wB : Fin r → Fin m → Fin M) =>
      condRp m wG (bsum wB) (T wG (bsum wB)) ∧
        ∀ j, Zc (wB j) (uRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j) = 0)
    (by positivity) fun wG => ?_
  rw [hcard]
  refine rounds_fail hM hm0 hg wG (T wG) K ?_
  intro b hbm j hw hc
  have hb : ∀ k, 0 ≤ b k ∧ b k ≤ m * M := by
    intro k
    have := (Fintype.mem_piFinset.mp hbm) k
    unfold I0 at this; rw [mem_Icc] at this; exact this
  have hcR := condR_round wG hb hc j (hK j b)
  obtain ⟨hu, hpar⟩ := residR_bound wG hcR
  have hB3 := h₂ M m hM hm2 (b j) _ hw hu hpar
  have hB1 := h₁ M m hM hm1 (b j) _ hw hu hpar
  have hlm := lamM_pos hM hm0
  have hlam : 6 ≤ lamB M m (b j) (uRp wG (T wG b) b (K j b) j) := by
    have := (abs_le.mp hB1).1
    unfold uRp at this ⊢
    rw [div_sub_one hlm.ne', le_div_iff₀ hlm] at this
    linarith
  have : 2 / lamB M m (b j) (uRp wG (T wG b) b (K j b) j) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  unfold uRp at hB3 this ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem R′ (failure probability δ)** (paper §6.4): with `r = ⌈log₂(2/δ)⌉` blocks and
`g = √(6 log(4r/δ))`, for `λ_m ≥ 8` and `m` large enough, the rounds all fail with probability
`≤ δ` on the event `|T − S/2| ≤ S_G/2 − rmM`. The running time is not formalized. -/
theorem thmRp {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → 8 ≤ lamM M m →
      ∀ (T : (Fin h → Fin M) → (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → ℤ) → ℤ)
        (K : Fin ⌈Real.logb 2 (2 / δ)⌉₊ → (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → ℤ) →
          Finset (Fin ⌈Real.logb 2 (2 / δ)⌉₊)),
      (∀ j b, j ∉ K j b) →
      ((univ.filter fun p : (Fin h → Fin M) × (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → Fin m → Fin M) =>
          condRp m p.1 (bsum p.2) (T p.1 (bsum p.2)) ∧
            ∀ j, Zc (p.2 j) (uRp p.1 (T p.1 (bsum p.2)) (bsum p.2) (K j (bsum p.2)) j) = 0).card : ℝ) /
        ((M : ℝ) ^ h * Fintype.card (Fin ⌈Real.logb 2 (2 / δ)⌉₊ → Fin m → Fin M)) ≤ δ := by
  set r := ⌈Real.logb 2 (2 / δ)⌉₊
  have hlog : 0 < Real.logb 2 (2 / δ) := by
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ hδ0]; linarith
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hlog).ne'
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h4 : 1 ≤ 4 * (r : ℝ) / δ := by
    rw [le_div_iff₀ hδ0]; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set g := √(6 * Real.log (4 * r / δ))
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  obtain ⟨m₀, hm₀⟩ := thmRp_gen hg
  refine ⟨m₀, fun M h m hM hm hl8 T K hK => (hm₀ M h m r hM hm hl8 T K hK).trans ?_⟩
  have hp : (1 / 2 : ℝ) ^ r ≤ δ / 2 := by
    have h2r : 2 / δ ≤ (2 : ℝ) ^ r := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_ceil (Real.logb 2 (2 / δ)))
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at this
      exact this
    rw [one_div_pow, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hδ0] at h2r
    linarith
  have hexp : r * (2 * exp (-(g ^ 2 / 6))) = δ / 2 := by
    have hg2 : g ^ 2 = 6 * Real.log (4 * r / δ) := Real.sq_sqrt (by
      have := Real.log_nonneg h4; linarith)
    rw [hg2, show 6 * Real.log (4 * r / δ) / 6 = Real.log (4 * r / δ) by ring, Real.exp_neg,
      Real.exp_log (by positivity)]
    field_simp; ring
  linarith

end ArcsAlgo.LLT
