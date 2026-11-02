module

public import ArcsAlgo.Uniform.RppRound
public import ArcsAlgo.Uniform.ThmRp
set_option autoImplicit false

/-!
# Theorem R″: the rounds (paper §6.7)

`R` disjoint blocks of `m` weights and the rest `G`, as in Theorem R′; round `j` runs the filtered
endgame on `E_j` with its own prime `P_j` (uniform among the primes of `[P₀, 2P₀)`) and residue `r_j`
(uniform in `ℤ/P_j`), drawn independently of everything else.

* `sPr`: `Pr_{P,r}(round succeeds | weights)`; given all the weights, the rounds fail independently
  with probabilities `1 − sPr`, so `Pr(all fail | w) = Π_j (1 − sPr_j)`.
* `rounds_fail_filt`: for fixed `w_G`, the blocks are independent given their sums, and a round in
  the window succeeds with probability `≥ p` given its sum, so
  `E[1[|T − S/2| ≤ S_G/2 − RmM]·Π_j(1 − sPr_j)] ≤ (1 − (1 − 2e^{−g²/6})p)^R` (Hoeffding off the window).
* `thmRpp_gen`: with `succB_unif`, for `P₀ ≥ 100`, `|A| = ⌊m/2⌋`, `m ≥ m₀(g, ε)`:
  `Pr(every round fails) ≤ (1 − (1 − 2e^{−g²/6})·p/(1 + ε))^R`.
* `pow_le_delta`: `(1 − x)^R ≤ δ` once `xR ≥ ln(1/δ)`.

The only hypothesis is that of Lemma K (`RosserSchoenfeld`, cited). The running time is not
formalized.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

open ArcsAlgo ArcsAlgo.PrimeK

variable {m M : ℕ}

/-- `Pr_{P, r}(round succeeds | weights)`: `P` uniform among the primes of `[P₀, 2P₀)`, `r` uniform
in `ℤ/P`. -/
noncomputable def sPr (P₀ : ℕ) (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) : ℝ :=
  (∑ p ∈ primesIn P₀, (live A w a p : ℝ) / p) / (primesIn P₀).card

theorem sPr_nonneg (P₀ : ℕ) (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) : 0 ≤ sPr P₀ A w a := by
  unfold sPr; positivity

theorem sPr_le_one (P₀ : ℕ) (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) : sPr P₀ A w a ≤ 1 := by
  unfold sPr
  rcases (Nat.cast_nonneg (α := ℝ) (primesIn P₀).card).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  rw [div_le_one h]
  calc ∑ p ∈ primesIn P₀, (live A w a p : ℝ) / p ≤ ∑ _p ∈ primesIn P₀, (1 : ℝ) :=
        sum_le_sum fun p hp => by
          have hp0 : (0 : ℝ) < p := by exact_mod_cast primesIn_pos hp
          rw [div_le_one hp0]
          have : live A w a p ≤ p := by
            unfold live; exact (card_filter_le _ _).trans (by simp)
          exact_mod_cast this
    _ = (primesIn P₀).card := by simp

theorem sum_sPr (M m P₀ : ℕ) (A : Finset (Fin m)) (s a : ℤ) :
    ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), sPr P₀ A w a =
      cntS M m s * succB M m P₀ A s a := by
  unfold sPr succB
  rcases (Nat.cast_nonneg (α := ℝ) (cntS M m s)).eq_or_lt with h | h
  · have hF : univ.filter (fun w : Fin m → Fin M => Sw w = s) = ∅ := by
      rw [← card_eq_zero]; unfold cntS at h; exact_mod_cast h.symm
    rw [hF, ← h]; simp
  rcases (Nat.cast_nonneg (α := ℝ) (primesIn P₀).card).eq_or_lt with h' | h'
  · rw [← h']; simp
  rw [← sum_div]; field_simp

/-- The target of round `j`: `a_j = (S_{E_j} + u_j)/2`. -/
def aRp {h M r : ℕ} (wG : Fin h → Fin M) (T : ℤ) (b : Fin r → ℤ) (K : Finset (Fin r)) (j : Fin r) : ℤ :=
  (b j + uRp wG T b K j) / 2

theorem fiber_eq {r m M : ℕ} (b : Fin r → ℤ) :
    (univ.filter fun wB : Fin r → Fin m → Fin M => bsum wB = b) =
      Fintype.piFinset fun j => univ.filter fun w : Fin m → Fin M => Sw w = b j := by
  ext wB; simp [Fintype.mem_piFinset, bsum, funext_iff]

/-- `Σ_s #{S_E = s}·(1 − p·1[s in the window]) ≤ (1 − (1 − 2e^{−g²/6})p)·M^m`. -/
theorem sum_cnt_window (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} (hg : 0 ≤ g) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ s ∈ I0 m M, (cntS M m s : ℝ) *
        (1 - p * if |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) then 1 else 0) ≤
      (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * p) * (M : ℝ) ^ m := by
  set W : ℤ → Prop := fun s => |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)
  have hM' : (0 : ℝ) < (M : ℝ) ^ m := by have : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
                                         positivity
  have hin : ∑ s ∈ I0 m M, (cntS M m s : ℝ) * (if W s then 1 else 0) =
      ((univ.filter fun w : Fin m → Fin M => W (Sw w)).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := Sw) (t := I0 m M) (fun w _ => Sw_mem w), Nat.cast_sum]
    refine sum_congr rfl fun s _ => ?_
    unfold cntS
    by_cases hs : W s
    · rw [if_pos hs, mul_one]; congr 2; ext w; simp only [mem_filter, mem_univ, true_and]
      constructor <;> intro h' <;> first | exact h'.2 | exact ⟨by rw [h']; exact hs, h'⟩
    · rw [if_neg hs, mul_zero]
      have : (univ.filter fun w : Fin m → Fin M => W (Sw w)).filter (fun w => Sw w = s) = ∅ := by
        rw [filter_eq_empty_iff]; intro w hw hws
        exact hs (hws ▸ (mem_filter.mp hw).2)
      rw [this]; simp
  have hout := window_compl (m := m) hM hm hg
  rw [div_le_iff₀ hM'] at hout
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Fin M)))
    (p := fun w => W (Sw w))
  have hcard : ((univ : Finset (Fin m → Fin M)).card : ℝ) = (M : ℝ) ^ m := by
    rw [card_univ]; simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hneg : (univ.filter fun w : Fin m → Fin M => ¬ W (Sw w)) =
      univ.filter fun w : Fin m → Fin M => g * √(sig2 M) * √(m : ℝ) < |(Sw w : ℝ) - m * muW M| := by
    ext w; simp [W]
  have hW : (1 - 2 * exp (-(g ^ 2 / 6))) * (M : ℝ) ^ m ≤
      ((univ.filter fun w : Fin m → Fin M => W (Sw w)).card : ℝ) := by
    have h2 : ((univ.filter fun w : Fin m → Fin M => W (Sw w)).card : ℝ) +
        ((univ.filter fun w : Fin m → Fin M => ¬ W (Sw w)).card : ℝ) = (M : ℝ) ^ m := by
      rw [← hcard]; exact_mod_cast hsplit
    rw [hneg] at h2
    linarith
  have e : ∑ s ∈ I0 m M, (cntS M m s : ℝ) * (1 - p * if W s then 1 else 0) =
      (M : ℝ) ^ m - p * ((univ.filter fun w : Fin m → Fin M => W (Sw w)).card : ℝ) := by
    rw [← hin, ← sum_cntS M m, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => by ring
  rw [e]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The filtered rounds fail conditionally independently** (paper §6.7, proof of Theorem R″):
for fixed `w_G`, the blocks' internal configurations are independent given the block sums, and the
filters `(P_j, r_j)` are drawn independently, so `Pr(all rounds fail | w_G, w_B)` is the product
`Π_j (1 − Pr_{P,r}(round j succeeds | w_{E_j}))`. If every round in the window succeeds with
probability `≥ p` given its block sum, then summed over the blocks
`E[1[|T − S/2| ≤ S_G/2 − RmM]·Π_j(…)] ≤ (1 − (1 − 2e^{−g²/6})p)^R`. -/
theorem rounds_fail_filt {h M r m P₀ : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} (hg : 0 ≤ g)
    (A : Finset (Fin m)) (wG : Fin h → Fin M) (T : (Fin r → ℤ) → ℤ)
    (K : Fin r → (Fin r → ℤ) → Finset (Fin r)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M), ∀ j : Fin r,
      |(b j : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) →
      condRp m wG b (T b) → p ≤ succB M m P₀ A (b j) (aRp wG (T b) b (K j b) j)) :
    ∑ wB : Fin r → Fin m → Fin M, (if condRp m wG (bsum wB) (T (bsum wB)) then
        ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0) ≤
      ((1 - (1 - 2 * exp (-(g ^ 2 / 6))) * p) * (M : ℝ) ^ m) ^ r := by
  set W : ℤ → Prop := fun s => |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)
  set ψ : ℤ → ℝ := fun s => (cntS M m s : ℝ) * (1 - p * if W s then 1 else 0) with hψ
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s => by
    simp only [ψ]
    have : (if W s then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    exact mul_nonneg (Nat.cast_nonneg _) (by nlinarith)
  rw [← sum_fiberwise_of_maps_to (g := bsum) (t := Fintype.piFinset fun _ : Fin r => I0 m M)
    (fun wB _ => bsum_mem wB)]
  have hfib : ∀ b ∈ Fintype.piFinset (fun _ : Fin r => I0 m M),
      ∑ wB ∈ univ.filter (fun wB : Fin r → Fin m → Fin M => bsum wB = b),
        (if condRp m wG (bsum wB) (T (bsum wB)) then
          ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0) ≤
        ∏ j, ψ (b j) := by
    intro b hb
    rw [sum_congr rfl fun wB hwB => by rw [(mem_filter.mp hwB).2]]
    by_cases hc : condRp m wG b (T b)
    · simp only [if_pos hc]
      rw [fiber_eq, ← prod_univ_sum (t := fun j => univ.filter fun w : Fin m → Fin M => Sw w = b j)
        (f := fun j w => 1 - sPr P₀ A w (aRp wG (T b) b (K j b) j))]
      refine Finset.prod_le_prod₀ (fun j _ => sum_nonneg fun w _ => ?_) fun j _ => ?_
      · have := sPr_le_one P₀ A w (aRp wG (T b) b (K j b) j); linarith
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_sPr]
      simp only [ψ]
      unfold cntS
      by_cases hw : W (b j)
      · rw [if_pos hw, mul_one]
        have := hp b hb j hw hc
        have h0 : (0 : ℝ) ≤ ((univ.filter fun w : Fin m → Fin M => Sw w = b j).card : ℝ) := by positivity
        nlinarith
      · rw [if_neg hw, mul_zero, sub_zero, mul_one]
        have : 0 ≤ succB M m P₀ A (b j) (aRp wG (T b) b (K j b) j) := by unfold succB; positivity
        have h0 : (0 : ℝ) ≤ ((univ.filter fun w : Fin m → Fin M => Sw w = b j).card : ℝ) := by positivity
        nlinarith
    · simp only [if_neg hc, sum_const_zero]
      exact prod_nonneg fun j _ => hψ0 _
  refine (sum_le_sum hfib).trans ?_
  rw [← prod_univ_sum (t := fun _ : Fin r => I0 m M) (f := fun _ s => ψ s), prod_const, card_univ,
    Fintype.card_fin]
  exact pow_le_pow_left₀ (sum_nonneg fun s _ => hψ0 s) (sum_cnt_window hM hm hg hp0) r

theorem pRpp_nonneg (g : ℝ) {M m P₀ : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) : 0 ≤ pRpp g M m P₀ := by
  have hL := lamM_pos hM hm
  have hlg : 0 ≤ log (m * M) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith)
  unfold pRpp
  have : 0 ≤ 2 * (P₀ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) := by positivity
  have : 0 ≤ 6 * log (m * M) * (1 + 2 / lamM M m) := by positivity
  positivity

theorem pRpp_le_one (g : ℝ) {M m P₀ : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) : pRpp g M m P₀ ≤ 1 := by
  have hL := lamM_pos hM hm
  have hmM : (2 : ℝ) ≤ m * M := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hlg : log 2 ≤ log (m * M) := log_le_log (by norm_num) hmM
  have h2 := Real.log_two_gt_d9
  have h1 : 0 ≤ 2 * (P₀ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) := by positivity
  have h3 : 0 ≤ 2 / lamM M m := by positivity
  have h4 : 1 ≤ 6 * log (m * M) * (1 + 2 / lamM M m) := by nlinarith
  unfold pRpp
  rw [div_le_one (by linarith)]; linarith

set_option maxHeartbeats 2000000 in
/-- **Theorem R″, general form** (paper §6.7): `R` disjoint blocks `E_j` of `m` weights and the
rest `G`, all weights independent and uniform in `{1, …, M}`; the target `T` depends on `w_G` and
the block sums, and round `j` includes the blocks `K_j ∌ j` (any rule that looks only at the block
sums), runs the centre rule on `G` and the filtered endgame on `E_j`, with halves `A`, `|A| = ⌊m/2⌋`,
a prime `P_j` uniform among the primes of `[P₀, 2P₀)` and `r_j` uniform in `ℤ/P_j`, drawn
independently of everything else. On the event `|T − S/2| ≤ S_G/2 − RmM`, for `P₀ ≥ 100` and
`m ≥ m₀(g, ε)`:
`Pr(every round fails) ≤ (1 − (1 − 2e^{−g²/6})·p/(1 + ε))^R`, with `p` as in `pRpp`.
The only hypothesis is that of Lemma K (Rosser–Schoenfeld). -/
theorem thmRpp_gen (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M h m R P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤
        (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * (pRpp g M m P₀ / (1 + ε))) ^ R := by
  obtain ⟨m₀, h₀⟩ := succB_unif hRS hg hε
  refine ⟨max m₀ 1, fun M h m R P₀ hM hm hP A hA T K hK => ?_⟩
  have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  set p := pRpp g M m P₀ / (1 + ε)
  have hp0 : 0 ≤ p := div_nonneg (pRpp_nonneg g hM hm1) (by linarith)
  have hp1 : p ≤ 1 := by
    have := pRpp_le_one g (P₀ := P₀) hM hm1
    have : p ≤ pRpp g M m P₀ := div_le_self (pRpp_nonneg g hM hm1) (by linarith)
    linarith
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hround : ∀ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
      (if condRp m wG (bsum wB) (T wG (bsum wB)) then
        ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0) ≤
      ((1 - (1 - 2 * exp (-(g ^ 2 / 6))) * p) * (M : ℝ) ^ m) ^ R := by
    intro wG
    refine rounds_fail_filt hM hm1 hg A wG (T wG) K hp0 hp1 ?_
    intro b hbm j hw hc
    have hb : ∀ k, 0 ≤ b k ∧ b k ≤ m * M := by
      intro k
      have := (Fintype.mem_piFinset.mp hbm) k
      unfold I0 at this; rw [mem_Icc] at this; exact this
    have hcR := condR_round wG hb hc j (hK j b)
    obtain ⟨hu, hpar⟩ := residR_bound wG hcR
    have ha : 2 * aRp wG (T wG b) b (K j b) j = b j + uRp wG (T wG b) b (K j b) j := by
      unfold aRp uRp; omega
    exact h₀ M m P₀ hM hm0 hP A hA (b j) _ _ ha hw hu hpar
  have hsum := sum_le_sum fun wG (_ : wG ∈ (univ : Finset (Fin h → Fin M))) => hround wG
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  simp only [Fintype.card_fun, Fintype.card_fin] at hsum
  push_cast at hsum
  rw [div_le_iff₀ (by positivity)]
  refine hsum.trans (le_of_eq ?_)
  rw [mul_pow]; ring

/-- `(1 − x)^R ≤ δ` as soon as `xR ≥ ln(1/δ)`: the number of rounds in Theorem R″. -/
theorem pow_le_delta {x δ : ℝ} (hx1 : x ≤ 1) (hδ : 0 < δ) {R : ℕ} (hR : log (1 / δ) ≤ x * R) :
    (1 - x) ^ R ≤ δ := by
  calc (1 - x) ^ R ≤ (exp (-x)) ^ R :=
        pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-x); linarith) R
    _ = exp (-(x * R)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ exp (-log (1 / δ)) := exp_le_exp.mpr (by linarith)
    _ = δ := by rw [log_div (by norm_num) hδ.ne', log_one, zero_sub, neg_neg, exp_log hδ]

end ArcsAlgo.LLT
