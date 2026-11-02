module

public import ArcsAlgo.Uniform.FirstId
public import ArcsAlgo.Uniform.Inv
set_option autoImplicit false

/-!
# The second moment as a sum over pairs, and the four classes (paper §6.3, Lemma B(2))

* `sumZ2_eq`: with `2a = s + u`, `Σ_{S_E = s} Z(u)² / M^m = Σ_{x, y ⊆ E} Pr(S_x = S_y = a, S_E = s)`.
* `pairP_eq`: with `C = x ∩ y`, `A = x ∖ y`, `B = y ∖ x`, `D = E ∖ (x ∪ y)`,
  `Pr(S_x = S_y = a, S_E = s) = Σ_c Pr(S_C = c) Pr(S_A = a − c) Pr(S_B = a − c) Pr(S_D = s − 2a + c)`:
  the four class sums are independent (`prW_and`) and each is a sum of `|A|, |B|, |C|, |D|` weights
  (`prW_SJ`).
* `sum_lawS_le`: probabilities of distinct values add up to at most one.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

theorem prW_congr {E E' : (Fin m → Fin M) → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ w, E w ↔ E' w) : prW M m E = prW M m E' := by
  unfold prW; congr 1
  exact sum_congr rfl fun w _ => by by_cases hw : E w <;> simp [hw, (h w).mp, ← h w]

theorem dependsOn_and {J K : Finset (Fin m)} {E₁ E₂ : (Fin m → Fin M) → Prop}
    (h1 : DependsOn J E₁) (h2 : DependsOn K E₂) : DependsOn (J ∪ K) (fun w => E₁ w ∧ E₂ w) := by
  intro w w' h
  show E₁ w ∧ E₂ w ↔ E₁ w' ∧ E₂ w'
  rw [h1 w w' fun i hi => h i (mem_union_left _ hi), h2 w w' fun i hi => h i (mem_union_right _ hi)]

/-- `Pr(S_k = 0) = 0` for `k ≥ 1`. -/
theorem lawS_succ_zero (M n : ℕ) : lawS M (n + 1) 0 = 0 := by
  unfold lawS
  rw [div_eq_zero_iff]; left
  norm_cast
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w _
  apply ne_of_gt
  exact sum_pos (fun i _ => by positivity) univ_nonempty

theorem lawS_nonneg (M k : ℕ) (v : ℤ) : 0 ≤ lawS M k v := by unfold lawS; positivity

/-- Probabilities of distinct values add up to at most one. -/
theorem sum_lawS_le (hM : 0 < M) (k : ℕ) (I : Finset ℤ) {f : ℤ → ℤ} (hf : Function.Injective f) :
    ∑ c ∈ I, lawS M k (f c) ≤ 1 := by
  rw [← sum_image (fun x _ y _ h => hf h)]
  set J := I.image f
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMk : (0 : ℝ) < (M : ℝ) ^ k := by positivity
  unfold lawS
  rw [← sum_div, div_le_one hMk]
  have : ∀ v ∈ J, ((univ.filter fun w : Fin k → Fin M => ∑ i, ((w i : ℤ) + 1) = v).card : ℝ) =
      ∑ w : Fin k → Fin M, if ∑ i, ((w i : ℤ) + 1) = v then (1 : ℝ) else 0 := by
    intro v _; rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]; simp
  rw [sum_congr rfl this, sum_comm]
  calc ∑ w : Fin k → Fin M, ∑ v ∈ J, (if ∑ i, ((w i : ℤ) + 1) = v then (1 : ℝ) else 0)
      ≤ ∑ _w : Fin k → Fin M, (1 : ℝ) := by
        refine sum_le_sum fun w _ => ?_
        rw [sum_ite_eq]; split_ifs <;> norm_num
    _ = (M : ℝ) ^ k := by simp

theorem SJ_le (J : Finset (Fin m)) (w : Fin m → Fin M) : 0 ≤ SJ J w ∧ SJ J w ≤ m * M := by
  unfold SJ
  constructor
  · exact sum_nonneg fun i _ => by positivity
  · calc ∑ i ∈ J, ((w i : ℤ) + 1) ≤ ∑ _i ∈ J, (M : ℤ) :=
          sum_le_sum fun i _ => by have := (w i).isLt; omega
      _ = J.card * M := by rw [sum_const, nsmul_eq_mul]
      _ ≤ m * M := by
          have : J.card ≤ m := by simpa using card_le_univ J
          have : (J.card : ℤ) ≤ m := by exact_mod_cast this
          nlinarith [(Nat.cast_nonneg M : (0 : ℤ) ≤ M)]

/-- `Pr(S_x = a, S_y = a, S_E = s)` for two subsets `x, y` of the block. -/
noncomputable def pairP (M m : ℕ) (x y : Finset (Fin m)) (a s : ℤ) : ℝ :=
  prW M m (fun w => SJ x w = a ∧ SJ y w = a ∧ Sw w = s)

/-- The range of the common sum `S_{x ∩ y}`. -/
def I0 (m M : ℕ) : Finset ℤ := Icc 0 (m * M)

/-- **The four classes** (paper §6.3, proof of Lemma B(2)): with `C = x ∩ y`, `A = x ∖ y`,
`B = y ∖ x`, `D = E ∖ (x ∪ y)`,
`Pr(S_x = S_y = a, S_E = s) = Σ_c Pr(S_C = c) Pr(S_A = a − c) Pr(S_B = a − c) Pr(S_D = s − 2a + c)`,
each class sum being a sum of `|A|, |B|, |C|, |D|` independent weights. -/
theorem pairP_eq (hM : 0 < M) (x y : Finset (Fin m)) (a s : ℤ) :
    pairP M m x y a s = ∑ c ∈ I0 m M, lawS M (x ∩ y).card c * lawS M (x \ y).card (a - c) *
      lawS M (y \ x).card (a - c) * lawS M (x ∪ y)ᶜ.card (s - 2 * a + c) := by
  set C := x ∩ y; set A := x \ y; set B := y \ x; set D := (x ∪ y)ᶜ
  have hx : ∀ w : Fin m → Fin M, SJ x w = SJ C w + SJ A w := fun w => by
    unfold SJ; rw [sum_inter_add_sum_sdiff]
  have hy : ∀ w : Fin m → Fin M, SJ y w = SJ C w + SJ B w := fun w => by
    unfold SJ; simp only [C, B]; rw [inter_comm, sum_inter_add_sum_sdiff]
  have hE : ∀ w : Fin m → Fin M, Sw w = SJ C w + SJ A w + SJ B w + SJ D w := fun w => by
    have e1 := Sw_eq w (x ∪ y)
    have e2 : SJ (x ∪ y) w + SJ C w = SJ x w + SJ y w := by unfold SJ; rw [sum_union_inter]
    rw [e1]; have := hx w; have := hy w; simp only [D]; omega
  let F : ℤ → (Fin m → Fin M) → Prop := fun c w =>
    SJ C w = c ∧ (SJ A w = a - c ∧ (SJ B w = a - c ∧ SJ D w = s - 2 * a + c))
  have h1 : ∀ w : Fin m → Fin M, (if SJ x w = a ∧ SJ y w = a ∧ Sw w = s then (1 : ℝ) else 0) =
      ∑ c ∈ I0 m M, if F c w then (1 : ℝ) else 0 := by
    intro w
    have hmem : SJ C w ∈ I0 m M := by
      unfold I0; rw [mem_Icc]; exact SJ_le C w
    have hF : ∀ c, F c w ↔ c = SJ C w ∧ (SJ x w = a ∧ SJ y w = a ∧ Sw w = s) := by
      intro c; simp only [F]; have := hx w; have := hy w; have := hE w
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; refine ⟨h1.symm, ?_, ?_, ?_⟩ <;> omega
      · rintro ⟨h1, h2, h3, h4⟩; refine ⟨h1.symm, ?_, ?_, ?_⟩ <;> omega
    simp only [hF]
    by_cases hev : SJ x w = a ∧ SJ y w = a ∧ Sw w = s
    · simp only [hev, and_true, ite_true]
      rw [sum_ite_eq' (I0 m M) (SJ C w) (fun _ => (1 : ℝ)), if_pos hmem]
    · simp [hev]
  have hdC : Disjoint C (A ∪ (B ∪ D)) := by
    rw [disjoint_left]; intro i; simp [C, A, B, D]; tauto
  have hdA : Disjoint A (B ∪ D) := by
    rw [disjoint_left]; intro i; simp [A, B, D]; tauto
  have hdB : Disjoint B D := by
    rw [disjoint_left]; intro i; simp [B, D]; tauto
  have hprod : ∀ c, prW M m (F c) = lawS M C.card c * lawS M A.card (a - c) *
      lawS M B.card (a - c) * lawS M D.card (s - 2 * a + c) := by
    intro c
    have dB := dependsOn_SJ (M := M) B (· = a - c)
    have dD := dependsOn_SJ (M := M) D (· = s - 2 * a + c)
    have dA := dependsOn_SJ (M := M) A (· = a - c)
    have dC := dependsOn_SJ (M := M) C (· = c)
    have e3 := prW_and hM hdB _ _ dB dD
    have e2 := prW_and hM hdA _ _ dA (dependsOn_and dB dD)
    have e1 := prW_and hM hdC _ _ dC (dependsOn_and dA (dependsOn_and dB dD))
    simp only [F]
    rw [e1, e2, e3, prW_SJ hM, prW_SJ hM, prW_SJ hM, prW_SJ hM]; ring
  unfold pairP prW
  rw [sum_congr rfl fun w _ => h1 w, sum_comm, sum_div]
  refine sum_congr rfl fun c _ => ?_
  have := hprod c; unfold prW at this; rw [this]

/-- `Z(u) = #{x ⊆ E : S_x = a}` on `S_E = s`, `2a = s + u`. -/
theorem Zc_eq (w : Fin m → Fin M) {s u a : ℤ} (hs : Sw w = s) (ha : 2 * a = s + u) :
    (Zc w u : ℝ) = ∑ x : Finset (Fin m), if SJ x w = a then (1 : ℝ) else 0 := by
  unfold Zc
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, ← (signEquiv m).symm.sum_comp]
  refine sum_congr rfl fun x _ => ?_
  have e1 := Sw_eq w x
  have e2 := Tsg_eq w ((signEquiv m).symm x)
  simp only [Equiv.apply_symm_apply] at e2
  by_cases h : SJ x w = a
  · rw [if_pos h, if_pos (by omega)]; simp
  · rw [if_neg h, if_neg (by omega)]

/-- **The second moment as a sum over pairs**:
`Σ_{S_E = s} Z(u)² / M^m = Σ_{x, y} Pr(S_x = S_y = a, S_E = s)`. -/
theorem sumZ2_eq (s u a : ℤ) (ha : 2 * a = s + u) :
    (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2) / (M : ℝ) ^ m =
      ∑ x : Finset (Fin m), ∑ y : Finset (Fin m), pairP M m x y a s := by
  have h : ∀ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2 =
      ∑ x : Finset (Fin m), ∑ y : Finset (Fin m),
        if SJ x w = a ∧ SJ y w = a ∧ Sw w = s then (1 : ℝ) else 0 := by
    intro w hw
    have hs := (mem_filter.mp hw).2
    rw [Zc_eq w hs ha, sq, sum_mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    by_cases hx : SJ x w = a <;> by_cases hy : SJ y w = a <;> simp [hx, hy, hs]
  rw [sum_congr rfl h, sum_filter]
  have h2 : ∀ w : Fin m → Fin M, (if Sw w = s then ∑ x : Finset (Fin m), ∑ y : Finset (Fin m),
      (if SJ x w = a ∧ SJ y w = a ∧ Sw w = s then (1 : ℝ) else 0) else 0) =
      ∑ x : Finset (Fin m), ∑ y : Finset (Fin m),
      (if SJ x w = a ∧ SJ y w = a ∧ Sw w = s then (1 : ℝ) else 0) := by
    intro w; split_ifs with hs
    · rfl
    · symm; exact sum_eq_zero fun x _ => sum_eq_zero fun y _ => by simp [hs]
  rw [sum_congr rfl fun w _ => h2 w, sum_comm, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm, sum_div]
  rfl

end ArcsAlgo.LLT
