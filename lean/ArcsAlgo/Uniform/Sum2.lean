module

public import ArcsAlgo.Uniform.TypPair
public import ArcsAlgo.Uniform.Chernoff
set_option autoImplicit false

/-!
# The second moment summed over pairs (paper §6.3, proof of Lemma B(2))

`B2_sum`: for fixed `M ≥ 2`, `m ≥ 32`, `16T ≤ m`, in the window,
`Σ_{x,y} Pr(S_x = S_y = a, S_E = s) ≤ Σ_x R(x)·(1 + 1[u = 0])
  + F/g_m(s)·(Σ_x R(x) + 2^m·3808/(σ²m²))² + 4^m E + 6·4^m e^{−2T²/m}/M³`,
where `R(x) = Pr(S_x = a, S_{E∖x} = s − a)`. The diagonal gives `Σ_x R(x)`, the complementary pairs
`1[u = 0] Σ_x R(x)`; typical pairs use `pair_typ`, with the Gaussians `G(x)` replaced back by `R(x)`
through Lemma B0′ (`pp_gg`); the other pairs are at most `M⁻³` each and, through the three binomial
counts `|x|`, `|y|`, `|x △ y|` (`atyp_count`, `sum_symmDiff`), number at most `6·4^m e^{−2T²/m}`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

variable {m : ℕ}

theorem sum_card (f : ℕ → ℝ) :
    ∑ x : Finset (Fin m), f x.card = ∑ k ∈ range (m + 1), (m.choose k : ℝ) * f k := by
  have := sum_powerset_apply_card f (x := (univ : Finset (Fin m)))
  rw [← powerset_univ, this, card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

theorem card_finset_fin (m : ℕ) : ((univ : Finset (Finset (Fin m))).card : ℝ) = 2 ^ m := by
  rw [card_univ, Fintype.card_finset, Fintype.card_fin]; push_cast; ring

/-- The number of `x ⊆ E` with `||x| − m/2| > T` is at most `2·2^m e^{−2T²/m}` (Chernoff). -/
theorem atyp_count (hm : 0 < m) {T : ℝ} (hT : 0 ≤ T) :
    ∑ x : Finset (Fin m), (if T < |(x.card : ℝ) - m / 2| then (1 : ℝ) else 0) ≤
      2 * 2 ^ m * exp (-(2 * T ^ 2 / m)) := by
  rw [sum_card (fun k => if T < |(k : ℝ) - m / 2| then (1 : ℝ) else 0)]
  refine le_trans ?_ (binom_tail hm hT)
  rw [sum_filter]
  refine sum_le_sum fun k _ => ?_
  split_ifs with h1 h2
  · simp
  · exact absurd h1.le h2
  · simp
  · simp

/-- `y ↦ x △ y` is a bijection, and `|x △ y| = |x ∖ y| + |y ∖ x|`. -/
theorem sum_symmDiff (x : Finset (Fin m)) (f : ℕ → ℝ) :
    ∑ y : Finset (Fin m), f ((x \ y).card + (y \ x).card) = ∑ d : Finset (Fin m), f d.card := by
  have hc : ∀ y : Finset (Fin m), (x \ y).card + (y \ x).card = (symmDiff x y).card := fun y => by
    rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff]
  simp only [hc]
  exact Fintype.sum_equiv
    ⟨fun y => symmDiff x y, fun d => symmDiff x d, fun y => by simp, fun d => by simp⟩ _ _
    (fun y => rfl)

theorem gaussB_pos {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) (v : ℤ) : 0 < gaussB M k v := by
  have hσ := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold gaussB
  have : 0 < √(2 * π * k * sig2 M) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- `x ≠ E ∖ x` for `m ≥ 1`. -/
theorem ne_compl_self (hm : 1 ≤ m) (x : Finset (Fin m)) : xᶜ ≠ x := by
  intro h
  have i : Fin m := ⟨0, hm⟩
  have h1 : i ∈ xᶜ ↔ i ∈ x := by rw [h]
  rw [mem_compl] at h1
  tauto

set_option maxHeartbeats 2000000 in
/-- **The second moment, summed over pairs** (paper §6.3, proof of Lemma B(2)), for fixed
`M, m, T`:
`Σ_{x,y} Pr(S_x = S_y = a, S_E = s) ≤ Σ_x R(x)·(1 + 1[u = 0])
  + F/g_m(s)·(Σ_x R(x) + 2^m·3808/(σ²m²))² + 4^m E + 6·4^m e^{−2T²/m}/M³`. -/
theorem B2_sum {M m T : ℕ} (hM : 2 ≤ M) (hm : 32 ≤ m) (hTm : 16 * T ≤ m) {g : ℝ} (hg : 0 ≤ g)
    {s u a : ℤ} (ha : 2 * a = s + u) (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ))
    (hu : |u| ≤ M) :
    ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s ≤
      (∑ x : Finset (Fin m), Rx M m x a s) * (1 + if u = 0 then 1 else 0) +
      FacB g m T / gaussB M m s *
        (∑ x : Finset (Fin m), Rx M m x a s + 2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2))) ^ 2 +
      4 ^ m * ErrB M m + 6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) / (M : ℝ) ^ 3 := by
  have hM0 : 0 < M := by omega
  have hσ := sig2_pos hM
  have hgm := gaussB_pos hM (by omega : 1 ≤ m) s
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hM3 : (0 : ℝ) < (M : ℝ) ^ 3 := by have : (0 : ℝ) < M := by exact_mod_cast hM0
                                         positivity
  have hFac : 0 ≤ FacB g m T := by unfold FacB; positivity
  have hErr : 0 ≤ ErrB M m := by unfold ErrB; positivity
  set F := FacB g m T
  set E := ErrB M m
  set gm := gaussB M m s
  -- the indicator functions
  let tx : Finset (Fin m) → Prop := fun x => |(x.card : ℝ) - m / 2| ≤ T
  let fx : Finset (Fin m) → ℝ := fun x => if |(x.card : ℝ) - m / 2| ≤ T then Rg M m x a s else 0
  let nx : ℕ → ℝ := fun k => if (T : ℝ) < |(k : ℝ) - m / 2| then 1 else 0
  have hfx0 : ∀ x, 0 ≤ fx x := fun x => by
    simp only [fx]; split_ifs
    · exact mul_nonneg (gaussB_nonneg _ _ _) (gaussB_nonneg _ _ _)
    · rfl
  have hnx0 : ∀ k, 0 ≤ nx k := fun k => by simp only [nx]; split_ifs <;> norm_num
  set bd : Finset (Fin m) → Finset (Fin m) → ℝ := fun x y =>
    F / gm * (fx x * fx y) + E + 1 / (M : ℝ) ^ 3 *
      (nx x.card + nx y.card + nx ((x \ y).card + (y \ x).card))
  have hbd0 : ∀ x y, 0 ≤ bd x y := fun x y => by
    simp only [bd]
    have := hfx0 x; have := hfx0 y; have := hnx0 x.card; have := hnx0 y.card
    have := hnx0 ((x \ y).card + (y \ x).card)
    positivity
  -- each pair other than `x` and `E ∖ x`
  have hrest : ∀ x y, y ≠ x → y ≠ xᶜ → pairP M m x y a s ≤ bd x y := by
    intro x y h1 h2
    by_cases htyp : |(x.card : ℝ) - m / 2| ≤ T ∧ |(y.card : ℝ) - m / 2| ≤ T ∧
        |((x \ y).card + (y \ x).card : ℝ) - m / 2| ≤ T
    · obtain ⟨t1, t2, t3⟩ := htyp
      have hp := pair_typ hM hm hTm hg ha hw hu t1 t2 t3
      have hfx : fx x = Rg M m x a s := by simp only [fx]; rw [if_pos t1]
      have hfy : fx y = Rg M m y a s := by simp only [fx]; rw [if_pos t2]
      have hn1 : nx x.card = 0 := by simp only [nx]; rw [if_neg (not_lt.mpr t1)]
      have hn2 : nx y.card = 0 := by simp only [nx]; rw [if_neg (not_lt.mpr t2)]
      have hn3 : nx ((x \ y).card + (y \ x).card) = 0 := by
        simp only [nx]; rw [if_neg]; push_cast; exact not_lt.mpr t3
      simp only [bd]
      rw [hfx, hfy, hn1, hn2, hn3]
      rw [← le_div_iff₀ hgm] at hp
      calc pairP M m x y a s ≤ (F * (Rg M m x a s * Rg M m y a s) + E * gm) / gm := hp
        _ = F / gm * (Rg M m x a s * Rg M m y a s) + E + 1 / (M : ℝ) ^ 3 * (0 + 0 + 0) := by
            field_simp; ring
    · have hp := pairP_le_inv3 hM0 (Ne.symm h1) h2 a s
      have hn : 1 ≤ nx x.card + nx y.card + nx ((x \ y).card + (y \ x).card) := by
        simp only [nx]
        push Not at htyp
        by_cases t1 : |(x.card : ℝ) - m / 2| ≤ T
        · by_cases t2 : |(y.card : ℝ) - m / 2| ≤ T
          · have t3 := htyp t1 t2
            rw [if_neg (not_lt.mpr t1), if_neg (not_lt.mpr t2), if_pos (by push_cast; exact t3)]
            norm_num
          · rw [if_pos (not_le.mp t2)]
            split_ifs <;> norm_num
        · rw [if_pos (not_le.mp t1)]
          split_ifs <;> norm_num
      have : 1 / (M : ℝ) ^ 3 ≤ 1 / (M : ℝ) ^ 3 *
          (nx x.card + nx y.card + nx ((x \ y).card + (y \ x).card)) :=
        le_mul_of_one_le_right (by positivity) hn
      have := hfx0 x; have := hfx0 y
      have : 0 ≤ F / gm * (fx x * fx y) := by positivity
      simp only [bd]; linarith
  -- the sum over `y`, for fixed `x`
  have hx : ∀ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s ≤
      Rx M m x a s * (1 + if u = 0 then 1 else 0) + ∑ y : Finset (Fin m), bd x y := by
    intro x
    have hxc : xᶜ ∈ (univ : Finset (Finset (Fin m))).erase x :=
      mem_erase.mpr ⟨ne_compl_self (by omega) x, mem_univ _⟩
    rw [← add_sum_erase _ _ (mem_univ x), ← add_sum_erase _ _ hxc]
    have hcomp : pairP M m x xᶜ a s ≤ Rx M m x a s * (if u = 0 then 1 else 0) := by
      split_ifs with hu0
      · rw [pairP_compl_eq hM0 x (by subst hu0; omega)]; ring_nf; rfl
      · rw [pairP_compl_zero x (by omega)]; simp
    have hr : ∑ y ∈ ((univ : Finset (Finset (Fin m))).erase x).erase xᶜ, pairP M m x y a s ≤
        ∑ y : Finset (Fin m), bd x y := by
      calc ∑ y ∈ ((univ : Finset (Finset (Fin m))).erase x).erase xᶜ, pairP M m x y a s
          ≤ ∑ y ∈ ((univ : Finset (Finset (Fin m))).erase x).erase xᶜ, bd x y := by
            refine sum_le_sum fun y hy => ?_
            have h1 := mem_erase.mp hy
            have h2 := mem_erase.mp h1.2
            exact hrest x y h2.1 h1.1
        _ ≤ ∑ y : Finset (Fin m), bd x y :=
            sum_le_sum_of_subset_of_nonneg (fun y _ => mem_univ y) fun y _ _ => hbd0 x y
    rw [pairP_diag hM0]
    linarith
  -- summing the bounds
  have hsumbd : ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), bd x y =
      F / gm * (∑ x : Finset (Fin m), fx x) ^ 2 + 4 ^ m * E +
        1 / (M : ℝ) ^ 3 * (2 ^ m * ∑ x : Finset (Fin m), nx x.card +
          2 ^ m * ∑ y : Finset (Fin m), nx y.card +
          ∑ x : Finset (Fin m), ∑ d : Finset (Fin m), nx d.card) := by
    simp only [bd, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_finset,
      Fintype.card_fin, nsmul_eq_mul]
    have h3 : ∀ x : Finset (Fin m), ∑ y : Finset (Fin m), nx ((x \ y).card + (y \ x).card) =
        ∑ d : Finset (Fin m), nx d.card := fun x => sum_symmDiff x nx
    simp only [h3]
    rw [sq, sum_mul_sum]
    push_cast
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4]
    simp only [← sum_mul, ← mul_sum, sum_const, card_univ, Fintype.card_finset, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hA := atyp_count (m := m) (by omega) hT0
  have hfxs : ∑ x : Finset (Fin m), fx x ≤
      ∑ x : Finset (Fin m), Rx M m x a s + 2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) := by
    have : ∀ x : Finset (Fin m), fx x ≤ Rx M m x a s + 3808 / (sig2 M * (m : ℝ) ^ 2) := by
      intro x
      simp only [fx]
      split_ifs with t
      · have ht := abs_le.mp t
        have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
        have hT' : 16 * (T : ℝ) ≤ m := by exact_mod_cast hTm
        have hk : x.card ≤ m := by simpa using card_le_univ x
        have c1 : 2 ≤ x.card := by
          have : (2 : ℝ) ≤ x.card := by linarith
          exact_mod_cast this
        have c2 : x.card + 2 ≤ m := by
          have : (x.card : ℝ) + 2 ≤ m := by linarith
          exact_mod_cast this
        have c3 : m ≤ 4 * x.card := by
          have : (m : ℝ) ≤ 4 * x.card := by linarith
          exact_mod_cast this
        have c4 : 4 * x.card ≤ 3 * m := by
          have : 4 * (x.card : ℝ) ≤ 3 * m := by linarith
          exact_mod_cast this
        have := pp_gg hM c1 c2 c3 c4 a (s - a)
        unfold Rx Rg
        have := (abs_le.mp this).1
        linarith
      · have := Rx_nonneg (M := M) x a s
        have : 0 ≤ 3808 / (sig2 M * (m : ℝ) ^ 2) := by positivity
        linarith
    calc ∑ x : Finset (Fin m), fx x ≤ ∑ x : Finset (Fin m), (Rx M m x a s + 3808 / (sig2 M * (m : ℝ) ^ 2)) :=
          sum_le_sum fun x _ => this x
      _ = _ := by rw [sum_add_distrib, sum_const, card_univ, Fintype.card_finset, Fintype.card_fin,
                  nsmul_eq_mul]; push_cast; ring
  have hfxs0 : 0 ≤ ∑ x : Finset (Fin m), fx x := sum_nonneg fun x _ => hfx0 x
  have hsq : (∑ x : Finset (Fin m), fx x) ^ 2 ≤
      (∑ x : Finset (Fin m), Rx M m x a s + 2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2))) ^ 2 :=
    pow_le_pow_left₀ hfxs0 hfxs 2
  have hcount : 2 ^ m * ∑ x : Finset (Fin m), nx x.card + 2 ^ m * ∑ y : Finset (Fin m), nx y.card +
      ∑ x : Finset (Fin m), ∑ d : Finset (Fin m), nx d.card ≤
      6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) := by
    have e : ∑ x : Finset (Fin m), ∑ d : Finset (Fin m), nx d.card =
        2 ^ m * ∑ d : Finset (Fin m), nx d.card := by
      rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    rw [e]
    have e4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4]
    have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
    have := mul_le_mul_of_nonneg_left hA h2m
    nlinarith
  have hF' : 0 ≤ F / gm := div_nonneg hFac hgm.le
  calc ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s
      ≤ ∑ x : Finset (Fin m), (Rx M m x a s * (1 + if u = 0 then 1 else 0) +
          ∑ y : Finset (Fin m), bd x y) := sum_le_sum fun x _ => hx x
    _ = (∑ x : Finset (Fin m), Rx M m x a s) * (1 + if u = 0 then 1 else 0) +
          ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), bd x y := by rw [sum_add_distrib, sum_mul]
    _ ≤ _ := by
        rw [hsumbd]
        have h1 := mul_le_mul_of_nonneg_left hsq hF'
        have h2 := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ) ^ 3)
        have e : 1 / (M : ℝ) ^ 3 * (6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m))) =
            6 * 4 ^ m * exp (-(2 * (T : ℝ) ^ 2 / m)) / (M : ℝ) ^ 3 := by ring
        linarith

end ArcsAlgo.LLT
