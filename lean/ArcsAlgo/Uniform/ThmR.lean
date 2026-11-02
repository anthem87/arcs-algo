module

public import ArcsAlgo.Uniform.Hoeff
public import ArcsAlgo.CentreRule
set_option autoImplicit false

/-!
# Theorem R (paper §6.4)

The head `H` and the endgame block `E` have independent weights uniform in `{1, …, M}`; the target
`T` depends on the weights only through `w_H` and `S_E`. The centre rule on `H` (Lemma A,
`centre_rule_corollary`) leaves the residual `u = 2t − S_E` (`residR`), with `|u| ≤ M` and
`u ≡ S_E (mod 2)` (`residR_bound`); the endgame (meet-in-the-middle, an exact search) fails iff
`Z(u) = 0`. Since `u` depends on `E` only through `S_E` and `H` is independent of `E`, Lemma B(3)
applies conditionally on `S_E` in the window (`fail_fiber`), and Hoeffding bounds the window's
complement (`window_compl`).

`thmR`: for `g ≥ 0`, `ε > 0` there is `m₀` such that for `M ≥ 2`, `m ≥ m₀`, `0 < λ* ≤ λ_m`,
`Pr(|T − S/2| ≤ S_H/2 and Z(u) = 0) ≤ 2/λ* + ε + 2e^{−g²/6}`. The running time is not formalized.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

open ArcsAlgo

/-- The weights of the head `H`, as the list read by the centre rule. -/
def wsOf {h M : ℕ} (wH : Fin h → Fin M) : List ℕ := List.ofFn fun i => (wH i : ℕ) + 1

/-- The residual of the endgame after the centre rule on `H`, in doubled form:
`u = 2t − S_E`, where `t` is the target left for `E` and `E₀ = 2T − S`. -/
def residR {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : ℤ :=
  (wsOf wH).foldl centreStep (2 * T - (((wsOf wH).sum : ℤ) + s))

/-- The hypothesis `|T − S/2| ≤ S_H/2` of Theorem R, in doubled form. -/
def condR {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : Prop :=
  |2 * T - (((wsOf wH).sum : ℤ) + s)| ≤ ((wsOf wH).sum : ℤ)

instance {h M : ℕ} (wH : Fin h → Fin M) (T s : ℤ) : Decidable (condR wH T s) := by
  unfold condR; infer_instance

theorem foldl_centre_parity (ws : List ℕ) (E : ℤ) :
    (2 : ℤ) ∣ ws.foldl centreStep E - E - (ws.sum : ℤ) := by
  induction ws generalizing E with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons, List.sum_cons]
    have := ih (centreStep E w)
    unfold centreStep at this ⊢
    split_ifs at this ⊢ with hc
    · obtain ⟨k, hk⟩ := this; exact ⟨k - w, by push_cast at hk ⊢; linarith⟩
    · obtain ⟨k, hk⟩ := this; exact ⟨k, by push_cast at hk ⊢; linarith⟩

theorem listMax_le {ws : List ℕ} {M : ℕ} (h : ∀ w ∈ ws, w ≤ M) : listMax ws ≤ M := by
  induction ws with
  | nil => simp [listMax]
  | cons w ws ih =>
    simp only [listMax, List.foldr_cons] at ih ⊢
    exact max_le (h w (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- **Lemma A for the endgame**: under `|T − S/2| ≤ S_H/2`, `|u| ≤ M` and `u ≡ s (mod 2)`. -/
theorem residR_bound {h M : ℕ} (wH : Fin h → Fin M) {T s : ℤ} (hc : condR wH T s) :
    |residR wH T s| ≤ M ∧ (2 : ℤ) ∣ residR wH T s - s := by
  constructor
  · have hle : listMax (wsOf wH) ≤ M := listMax_le fun w hw => by
      simp only [wsOf, List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw; have := (wH i).isLt; omega
    have := centre_rule_corollary (2 * T - (((wsOf wH).sum : ℤ) + s)) (wsOf wH) (by
      unfold condR at hc; have : (0 : ℤ) ≤ listMax (wsOf wH) := Nat.cast_nonneg _; linarith)
    unfold residR
    exact this.trans (by exact_mod_cast hle)
  · have := foldl_centre_parity (wsOf wH) (2 * T - (((wsOf wH).sum : ℤ) + s))
    unfold residR
    obtain ⟨k, hk⟩ := this
    exact ⟨k + T - s, by linarith⟩

theorem Sw_mem {m M : ℕ} (w : Fin m → Fin M) : Sw w ∈ I0 m M := by
  unfold I0; rw [mem_Icc]
  have := SJ_le (univ : Finset (Fin m)) w
  unfold SJ at this; unfold Sw; exact this

/-- The failure count for fixed `w_H`, conditioned on each value of `S_E`. -/
theorem fail_fiber {h M m : ℕ} (hM : 0 < M) (wH : Fin h → Fin M) (T : (Fin h → Fin M) → ℤ → ℤ)
    (W : ℤ → Prop) [DecidablePred W] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ s, W s → condR wH (T wH s) s → p0B M m s (residR wH (T wH s) s) ≤ c) :
    ((univ.filter fun wE : Fin m → Fin M =>
        condR wH (T wH (Sw wE)) (Sw wE) ∧ Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0).card : ℝ) ≤
      c * (M : ℝ) ^ m + ((univ.filter fun wE : Fin m → Fin M => ¬ W (Sw wE)).card : ℝ) := by
  set F := univ.filter fun wE : Fin m → Fin M =>
        condR wH (T wH (Sw wE)) (Sw wE) ∧ Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0
  have hsplit : F ⊆ F.filter (fun wE => W (Sw wE)) ∪ univ.filter (fun wE : Fin m → Fin M => ¬ W (Sw wE)) := by
    intro wE hw; by_cases h : W (Sw wE)
    · exact mem_union_left _ (mem_filter.mpr ⟨hw, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  have h1 : (F.card : ℝ) ≤ ((F.filter (fun wE => W (Sw wE))).card : ℝ) +
      ((univ.filter fun wE : Fin m → Fin M => ¬ W (Sw wE)).card : ℝ) := by
    exact_mod_cast (card_le_card hsplit).trans (card_union_le _ _)
  have h2 : ((F.filter (fun wE => W (Sw wE))).card : ℝ) ≤ c * (M : ℝ) ^ m := by
    rw [card_eq_sum_ones, Nat.cast_sum,
      ← sum_fiberwise_of_maps_to (g := Sw) (t := I0 m M) (fun w _ => Sw_mem w)]
    have hfib : ∀ s ∈ I0 m M, ∑ x ∈ (F.filter (fun wE => W (Sw wE))).filter (fun x => Sw x = s),
        ((1 : ℕ) : ℝ) ≤ c * cntS M m s := by
      intro s _
      rw [← Nat.cast_sum, ← card_eq_sum_ones]
      by_cases hs : W s ∧ condR wH (T wH s) s
      · have hsub : (F.filter (fun wE => W (Sw wE))).filter (fun x => Sw x = s) ⊆
            univ.filter (fun w : Fin m → Fin M => Sw w = s ∧ Zc w (residR wH (T wH s) s) = 0) := by
          intro x hx
          simp only [F, mem_filter, mem_univ, true_and] at hx ⊢
          obtain ⟨⟨⟨-, hz⟩, -⟩, hx⟩ := hx
          rw [hx] at hz; exact ⟨hx, hz⟩
        have hp := hc s hs.1 hs.2
        refine (Nat.cast_le.mpr (card_le_card hsub)).trans ?_
        by_cases h0 : (cntS M m s : ℝ) = 0
        · have : (univ.filter (fun w : Fin m → Fin M => Sw w = s ∧
              Zc w (residR wH (T wH s) s) = 0)).card = 0 := by
            have h0' : cntS M m s = 0 := by exact_mod_cast h0
            unfold cntS at h0'
            apply Nat.eq_zero_of_le_zero
            rw [← h0']; exact card_le_card fun w hw => by
              simp only [mem_filter, mem_univ, true_and] at hw ⊢; exact hw.1
          rw [this, h0]; simp
        · have : ((univ.filter (fun w : Fin m → Fin M => Sw w = s ∧
              Zc w (residR wH (T wH s) s) = 0)).card : ℝ) =
              p0B M m s (residR wH (T wH s) s) * cntS M m s := by
            unfold p0B; field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
      · have : (F.filter (fun wE => W (Sw wE))).filter (fun x => Sw x = s) = ∅ := by
          rw [filter_eq_empty_iff]
          intro x hx
          simp only [F, mem_filter, mem_univ, true_and] at hx
          intro hxs; rw [hxs] at hx; exact hs ⟨hx.2, hx.1.1⟩
        rw [this]; simp only [card_empty, Nat.cast_zero]; positivity
    calc ∑ s ∈ I0 m M, ∑ x ∈ (F.filter (fun wE => W (Sw wE))).filter (fun x => Sw x = s), ((1 : ℕ) : ℝ)
        ≤ ∑ s ∈ I0 m M, c * (cntS M m s : ℝ) := sum_le_sum hfib
      _ = c * (M : ℝ) ^ m := by
          rw [← mul_sum]; congr 1
          have : ∑ s ∈ I0 m M, (cntS M m s : ℝ) = ((univ : Finset (Fin m → Fin M)).card : ℝ) := by
            unfold cntS
            rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := Sw) (t := I0 m M)
              (fun w _ => Sw_mem w)]
          rw [this, card_univ]; simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  linarith

/-- The probability of failure, averaged over `w_H`. -/
theorem fail_avg {h M m : ℕ} (hM : 0 < M) (P : (Fin h → Fin M) → (Fin m → Fin M) → Prop)
    [∀ a, DecidablePred (P a)] {B : ℝ} (hB : ∀ wH, ((univ.filter (P wH)).card : ℝ) ≤ B * (M : ℝ) ^ m) :
    ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) => P p.1 p.2).card : ℝ) /
      ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ B := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e : ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) => P p.1 p.2).card : ℝ) =
      ∑ wH : Fin h → Fin M, ((univ.filter (P wH)).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun wH _ => ?_
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [e, div_le_iff₀ (by positivity)]
  calc ∑ wH : Fin h → Fin M, ((univ.filter (P wH)).card : ℝ) ≤ ∑ _wH : Fin h → Fin M, B * (M : ℝ) ^ m :=
        sum_le_sum fun wH _ => hB wH
    _ = B * ((M : ℝ) ^ h * (M : ℝ) ^ m) := by
        rw [sum_const, card_univ, nsmul_eq_mul]; simp only [Fintype.card_fun, Fintype.card_fin]; push_cast; ring

/-- **Theorem R (random weights)** (paper §6.4): let the weights of `H` and `E` be independent and
uniform in `{1, …, M}`, `|E| = m`, and let the target `T` depend on the weights only through
`w_H` and `S_E`. On the event `|T − S/2| ≤ S_H/2`, the centre rule on `H` followed by an exact
search on `E` (meet-in-the-middle) fails only if `Z(u) = 0` for the residual `u` left by the centre
rule. For every `g ≥ 0`, `ε > 0` there is `m₀` such that for all `M ≥ 2`, `m ≥ m₀` and
`0 < λ* ≤ λ_m`:
`Pr(|T − S/2| ≤ S_H/2 and the endgame has no solution) ≤ 2/λ* + ε + 2e^{−g²/6}`.
The `O(m^{−1/2+3η})` of the paper is the `ε` here (Lemma B in its `o(1)` form). The running time
is not formalized. -/
theorem thmR {g ε : ℝ} (hg : 0 ≤ g) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ lamS : ℝ, 0 < lamS → lamS ≤ lamM M m →
      ∀ T : (Fin h → Fin M) → ℤ → ℤ,
      ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 2 / lamS + ε + 2 * exp (-(g ^ 2 / 6)) := by
  set ε₁ := min (1 / 2) (ε / 4)
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by linarith)
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg hε₁
  obtain ⟨m₂, h₂⟩ := lemmaB3_unif hg (ε := ε / 2) (by linarith)
  refine ⟨max (max m₁ m₂) 1, fun M h m hM hm lamS hl0 hlS T => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hM0 : 0 < M := by omega
  have hE := exp_pos (-(g ^ 2 / 6))
  -- the trivial case `λ* ≤ 2`
  by_cases hl2 : lamS ≤ 2
  · have h1 : (1 : ℝ) ≤ 2 / lamS := by rw [le_div_iff₀ hl0]; linarith
    have hP : ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 1 := by
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
      rw [div_le_one (by positivity)]
      have := card_le_univ (univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0)
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at this
      exact_mod_cast this
    linarith
  push Not at hl2
  set c := 2 / ((1 - ε₁) * lamS) + ε / 2
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁4 : ε₁ ≤ ε / 4 := min_le_right _ _
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - ε₁ := by linarith
    positivity
  have hc : ∀ (wH : Fin h → Fin M) (s : ℤ),
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → condR wH (T wH s) s →
      p0B M m s (residR wH (T wH s) s) ≤ c := by
    intro wH s hw hcs
    obtain ⟨hu, hpar⟩ := residR_bound wH hcs
    have hB3 := h₂ M m hM hm2 s _ hw hu hpar
    have hB1 := h₁ M m hM hm1 s _ hw hu hpar
    have hlm := lamM_pos hM hm0
    have hlam : (1 - ε₁) * lamS ≤ lamB M m s (residR wH (T wH s) s) := by
      have := (abs_le.mp hB1).1
      rw [div_sub_one hlm.ne', le_div_iff₀ hlm] at this
      have : (1 - ε₁) * lamS ≤ (1 - ε₁) * lamM M m := mul_le_mul_of_nonneg_left hlS (by linarith)
      linarith
    have hpos : 0 < (1 - ε₁) * lamS := mul_pos (by linarith) hl0
    have : 2 / lamB M m s (residR wH (T wH s) s) ≤ 2 / ((1 - ε₁) * lamS) :=
      div_le_div_of_nonneg_left (by norm_num) hpos hlam
    simp only [c]; linarith
  have hfail : ∀ wH : Fin h → Fin M, ((univ.filter fun wE : Fin m → Fin M =>
        condR wH (T wH (Sw wE)) (Sw wE) ∧ Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0).card : ℝ) ≤
      (c + 2 * exp (-(g ^ 2 / 6))) * (M : ℝ) ^ m := by
    intro wH
    have := fail_fiber hM0 wH T (fun s => |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) hc0
      (fun s hw hcs => hc wH s hw hcs)
    have hwin := window_compl (m := m) hM hm0 hg
    have hMm : (0 : ℝ) < (M : ℝ) ^ m := by have : (0 : ℝ) < M := by exact_mod_cast hM0
                                           positivity
    rw [div_le_iff₀ hMm] at hwin
    have e : (univ.filter fun wE : Fin m → Fin M =>
        ¬ |(Sw wE : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) =
        univ.filter fun wE : Fin m → Fin M => g * √(sig2 M) * √(m : ℝ) < |(Sw wE : ℝ) - m * muW M| := by
      ext w; simp
    rw [e] at this
    calc _ ≤ c * (M : ℝ) ^ m + ((univ.filter fun wE : Fin m → Fin M =>
            g * √(sig2 M) * √(m : ℝ) < |(Sw wE : ℝ) - m * muW M|).card : ℝ) := this
      _ ≤ c * (M : ℝ) ^ m + 2 * exp (-(g ^ 2 / 6)) * (M : ℝ) ^ m := by linarith
      _ = (c + 2 * exp (-(g ^ 2 / 6))) * (M : ℝ) ^ m := by ring
  have hfa := fail_avg hM0 (fun wH wE => condR wH (T wH (Sw wE)) (Sw wE) ∧
    Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0) hfail
  refine hfa.trans ?_
  have hd : 2 / ((1 - ε₁) * lamS) ≤ 2 / lamS + ε / 2 := by
    have h1 : 0 < 1 - ε₁ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : (2 / lamS + ε / 2) * ((1 - ε₁) * lamS) = 2 * (1 - ε₁) + ε / 2 * (1 - ε₁) * lamS := by
      field_simp
    rw [this]
    have h3 : (1 : ℝ) ≤ (1 - ε₁) * lamS := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ ε / 2)
    have h5 : ε / 2 * (1 - ε₁) * lamS = ε / 2 * ((1 - ε₁) * lamS) := by ring
    linarith
  simp only [c]; linarith

/-- **Theorem R with the rate** (paper §6.4): there is `C(g)` such that, for `m ≥ m₀(g)`, all
`M ≥ 2` and `0 < λ* ≤ λ_m`, the probability that `|T − S/2| ≤ S_H/2` and the endgame has no solution
is at most `2/λ* + C m^{−1/5} + 2e^{−g²/6}`, with `T` any function of `(w_H, S_E)` (Lemmas A, B(1), B(3)
with their rates). -/
theorem thmR_rate {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M h m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ lamS : ℝ, 0 < lamS → lamS ≤ lamM M m →
      ∀ T : (Fin h → Fin M) → ℤ → ℤ,
      ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 2 / lamS + C * (m : ℝ) ^ (-(1 / 5 : ℝ)) + 2 * exp (-(g ^ 2 / 6)) := by
  obtain ⟨C₁, hC₁, m₁, h₁⟩ := lemmaB1_rate hg
  obtain ⟨C₃, hC₃, m₂, h₂⟩ := lemmaB3_rate hg
  refine ⟨2 * C₁ + C₃, by positivity, ?_⟩
  refine ⟨max (max m₁ m₂) (max 1 ⌈(2 * C₁ + 1) ^ 5⌉₊), fun M h m hM hm lamS hl0 hlS T => ?_⟩
  set r := (m : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmK : (2 * C₁ + 1) ^ 5 ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  have hrK : r * (2 * C₁ + 1) ≤ 1 := by
    have hK0 : (0 : ℝ) < 2 * C₁ + 1 := by positivity
    have hy : 2 * C₁ + 1 ≤ (m : ℝ) ^ ((1 : ℝ) / 5) := by
      have h := Real.rpow_le_rpow (by positivity) hmK (by norm_num : (0 : ℝ) ≤ 1 / 5)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, show ((5 : ℕ) : ℝ) * (1 / 5) = 1 by norm_num,
        Real.rpow_one] at h
    have hm0' : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmK
    rw [hr, Real.rpow_neg hm0'.le, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hy
  set ε₁ := C₁ * r
  set ε := 2 * (2 * C₁ + C₃) * r
  have hε0 : 0 ≤ ε := by positivity
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hM0 : 0 < M := by omega
  have hE := exp_pos (-(g ^ 2 / 6))
  -- the trivial case `λ* ≤ 2`
  by_cases hl2 : lamS ≤ 2
  · have h1 : (1 : ℝ) ≤ 2 / lamS := by rw [le_div_iff₀ hl0]; linarith
    have hP : ((univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0).card : ℝ) /
        ((M : ℝ) ^ h * (M : ℝ) ^ m) ≤ 1 := by
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
      rw [div_le_one (by positivity)]
      have := card_le_univ (univ.filter fun p : (Fin h → Fin M) × (Fin m → Fin M) =>
          condR p.1 (T p.1 (Sw p.2)) (Sw p.2) ∧
            Zc p.2 (residR p.1 (T p.1 (Sw p.2)) (Sw p.2)) = 0)
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at this
      exact_mod_cast this
    linarith
  push Not at hl2
  set c := 2 / ((1 - ε₁) * lamS) + C₃ * r
  have hε₁2 : ε₁ ≤ 1 / 2 := by simp only [ε₁]; nlinarith
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - ε₁ := by linarith
    positivity
  have hc : ∀ (wH : Fin h → Fin M) (s : ℤ),
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → condR wH (T wH s) s →
      p0B M m s (residR wH (T wH s) s) ≤ c := by
    intro wH s hw hcs
    obtain ⟨hu, hpar⟩ := residR_bound wH hcs
    have hB3 := h₂ M m hM hm2 s _ hw hu hpar
    have hB1 := h₁ M m hM hm1 s _ hw hu hpar
    have hlm := lamM_pos hM hm0
    have hlam : (1 - ε₁) * lamS ≤ lamB M m s (residR wH (T wH s) s) := by
      have := (abs_le.mp hB1).1
      rw [div_sub_one hlm.ne', le_div_iff₀ hlm] at this
      have : (1 - ε₁) * lamS ≤ (1 - ε₁) * lamM M m := mul_le_mul_of_nonneg_left hlS (by linarith)
      linarith
    have hpos : 0 < (1 - ε₁) * lamS := mul_pos (by linarith) hl0
    have : 2 / lamB M m s (residR wH (T wH s) s) ≤ 2 / ((1 - ε₁) * lamS) :=
      div_le_div_of_nonneg_left (by norm_num) hpos hlam
    simp only [c, ε₁]; nlinarith
  have hfail : ∀ wH : Fin h → Fin M, ((univ.filter fun wE : Fin m → Fin M =>
        condR wH (T wH (Sw wE)) (Sw wE) ∧ Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0).card : ℝ) ≤
      (c + 2 * exp (-(g ^ 2 / 6))) * (M : ℝ) ^ m := by
    intro wH
    have := fail_fiber hM0 wH T (fun s => |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) hc0
      (fun s hw hcs => hc wH s hw hcs)
    have hwin := window_compl (m := m) hM hm0 hg
    have hMm : (0 : ℝ) < (M : ℝ) ^ m := by have : (0 : ℝ) < M := by exact_mod_cast hM0
                                           positivity
    rw [div_le_iff₀ hMm] at hwin
    have e : (univ.filter fun wE : Fin m → Fin M =>
        ¬ |(Sw wE : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) =
        univ.filter fun wE : Fin m → Fin M => g * √(sig2 M) * √(m : ℝ) < |(Sw wE : ℝ) - m * muW M| := by
      ext w; simp
    rw [e] at this
    calc _ ≤ c * (M : ℝ) ^ m + ((univ.filter fun wE : Fin m → Fin M =>
            g * √(sig2 M) * √(m : ℝ) < |(Sw wE : ℝ) - m * muW M|).card : ℝ) := this
      _ ≤ c * (M : ℝ) ^ m + 2 * exp (-(g ^ 2 / 6)) * (M : ℝ) ^ m := by linarith
      _ = (c + 2 * exp (-(g ^ 2 / 6))) * (M : ℝ) ^ m := by ring
  have hfa := fail_avg hM0 (fun wH wE => condR wH (T wH (Sw wE)) (Sw wE) ∧
    Zc wE (residR wH (T wH (Sw wE)) (Sw wE)) = 0) hfail
  refine hfa.trans ?_
  have hd : 2 / ((1 - ε₁) * lamS) ≤ 2 / lamS + 2 * ε₁ := by
    have h1 : 0 < 1 - ε₁ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : (2 / lamS + 2 * ε₁) * ((1 - ε₁) * lamS) = 2 * (1 - ε₁) + 2 * ε₁ * (1 - ε₁) * lamS := by
      field_simp
    rw [this]
    have h3 : (1 : ℝ) ≤ (1 - ε₁) * lamS := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * ε₁)
    have h5 : 2 * ε₁ * (1 - ε₁) * lamS = 2 * ε₁ * ((1 - ε₁) * lamS) := by ring
    linarith
  simp only [c, ε₁]; nlinarith

end ArcsAlgo.LLT
