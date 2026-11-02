module

public import ArcsAlgo.Uniform.SecondId
public import ArcsAlgo.RandomWeights
set_option autoImplicit false

/-!
# Lemma B‴: exact reduction to first moments (paper §6.3)

With `λ_k(v, t) = E[#{ε ∈ {±1}^k : Σ ε_i w_i = v} | S_k = t]` (`lamZ`),
`E[Z(u)² | S_E = s] = Σ_k C(m,k) Σ_{s₁} Pr(S_{m−k} = s₁)Pr(S_k = s − s₁)/Pr(S_m = s) · λ_{m−k}(u, s₁) λ_k(0, s − s₁)`
(`lemmaBppp`). The proof splits a pair of sign vectors into the positions where they agree and where
they differ (`Z_sq_split`); given their weight sums the two parts are independent (`factor_D`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `Σ_{S_k = t} Z_k(v) / M^k = E[Z_k(v); S_k = t]` for a block of `k` weights. -/
noncomputable def PhiZ (M k : ℕ) (v t : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin k → Fin M => Sw w = t), (Zc w v : ℝ)) / (M : ℝ) ^ k

/-- `λ_k(v, t) = E[#{ε ∈ {±1}^k : Σ ε_i w_i = v} | S_k = t]` (paper §6.3, Lemma B‴). -/
noncomputable def lamZ (M k : ℕ) (v t : ℤ) : ℝ := PhiZ M k v t / lawS M k t

/-- `E[Z(u)² | S_E = s]` for the block `E` of `m` weights. -/
noncomputable def condZ2 (M m : ℕ) (u s : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2) / (M : ℝ) ^ m /
    lawS M m s

theorem lawS_eq_card (M k : ℕ) (t : ℤ) :
    lawS M k t = ((univ.filter fun w : Fin k → Fin M => Sw w = t).card : ℝ) / (M : ℝ) ^ k := rfl

/-- `E[Z_k(v); S_k = t] = Pr(S_k = t)·λ_k(v, t)`. -/
theorem PhiZ_eq (hM : 0 < M) (k : ℕ) (v t : ℤ) : PhiZ M k v t = lawS M k t * lamZ M k v t := by
  unfold lamZ
  by_cases h : lawS M k t = 0
  · rw [h, zero_mul]
    have hc : (univ.filter fun w : Fin k → Fin M => Sw w = t) = ∅ := by
      rw [lawS_eq_card, div_eq_zero_iff] at h
      rcases h with h | h
      · exact_mod_cast card_eq_zero.mp (by exact_mod_cast h)
      · exact absurd h (by positivity)
    unfold PhiZ; rw [hc]; simp
  · field_simp

/-- No solution when `t + v` is odd. -/
theorem Zc_parity {k : ℕ} (w : Fin k → Fin M) (v : ℤ) (h : ¬ ∃ a, 2 * a = Sw w + v) : Zc w v = 0 := by
  unfold Zc
  rw [card_eq_zero, filter_eq_empty_iff]
  intro ε _ hε
  apply h
  refine ⟨SJ (signEquiv k ε) w, ?_⟩
  have e1 := Sw_eq w (signEquiv k ε)
  have e2 := Tsg_eq w ε
  omega

/-- `Z(u) = Z_E(u)` in the notation of `Z_sq_split`. -/
theorem Zc_eq_Zs {k : ℕ} (w : Fin k → Fin M) (v : ℤ) :
    Zc w v = RandomWeights.Zs (fun i => (w i : ℤ) + 1) univ v := by
  unfold Zc RandomWeights.Zs
  rw [powerset_univ]
  refine card_bij (fun ε _ => signEquiv k ε) (fun ε hε => ?_) (fun ε _ ε' _ h => (signEquiv k).injective h)
    (fun P hP => ⟨(signEquiv k).symm P, ?_, by simp⟩)
  · simp only [mem_filter, mem_univ, true_and] at hε ⊢
    have e1 := Sw_eq w (signEquiv k ε)
    have e2 := Tsg_eq w ε
    unfold Sw SJ at *
    omega
  · simp only [mem_filter, mem_univ, true_and] at hP ⊢
    have e1 := Sw_eq w P
    have e2 := Tsg_eq w ((signEquiv k).symm P)
    simp only [Equiv.apply_symm_apply] at e2
    unfold Sw SJ at *
    omega

/-- Events built from `S_P` and `S_J`, `P ⊆ J`, depend only on the weights in `J`. -/
theorem dependsOn_SJ2 {P J : Finset (Fin m)} (hP : P ⊆ J) (Q : ℤ → ℤ → Prop) :
    DependsOn (M := M) J (fun w => Q (SJ P w) (SJ J w)) := by
  intro w w' h
  have h1 : SJ P w = SJ P w' := sum_congr rfl fun i hi => by rw [h i (hP hi)]
  have h2 : SJ J w = SJ J w' := sum_congr rfl fun i hi => by rw [h i hi]
  show Q (SJ P w) (SJ J w) ↔ Q (SJ P w') (SJ J w'); rw [h1, h2]

/-- The first moment of a sub-block: for `J ⊆ E`,
`Σ_{P ⊆ J} Pr(2S_P − S_J = v, S_J = t) = E[Z_{|J|}(v); S_{|J|} = t]`. -/
theorem sumP_eq (hM : 0 < M) (J : Finset (Fin m)) (v t : ℤ) :
    ∑ P ∈ J.powerset, prW M m (fun w => 2 * SJ P w - SJ J w = v ∧ SJ J w = t) =
      PhiZ M J.card v t := by
  by_cases hpar : ∃ a, 2 * a = t + v
  · obtain ⟨a, ha⟩ := hpar
    have h1 : ∀ P ∈ J.powerset, prW M m (fun w => 2 * SJ P w - SJ J w = v ∧ SJ J w = t) =
        lawS M P.card a * lawS M (J.card - P.card) (t - a) := by
      intro P hP
      rw [mem_powerset] at hP
      have hs : ∀ w : Fin m → Fin M, SJ J w = SJ P w + SJ (J \ P) w := fun w => by
        unfold SJ; rw [add_comm, sum_sdiff hP]
      rw [prW_congr (E' := fun w => SJ P w = a ∧ SJ (J \ P) w = t - a) (fun w => by
        have := hs w; constructor
        · rintro ⟨h1, h2⟩; constructor <;> omega
        · rintro ⟨h1, h2⟩; constructor <;> omega)]
      rw [prW_and hM disjoint_sdiff _ _ (dependsOn_SJ P (· = a)) (dependsOn_SJ (J \ P) (· = t - a)),
        prW_SJ hM, prW_SJ hM, card_sdiff_of_subset hP]
    rw [sum_congr rfl h1]
    have := sum_powerset_apply_card (fun k => lawS M k a * lawS M (J.card - k) (t - a)) (x := J)
    rw [this]
    unfold PhiZ
    rw [sumZ_eq hM t v a ha]
    simp [nsmul_eq_mul]
  · have h1 : ∀ P ∈ J.powerset, prW M m (fun w => 2 * SJ P w - SJ J w = v ∧ SJ J w = t) = 0 := by
      intro P _
      unfold prW
      rw [div_eq_zero_iff]; left
      refine sum_eq_zero fun w _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hpar ⟨SJ P w, by omega⟩
    rw [sum_congr rfl h1, sum_const_zero]
    unfold PhiZ
    symm; rw [div_eq_zero_iff]; left
    refine sum_eq_zero fun w hw => ?_
    have hs := (mem_filter.mp hw).2
    rw [Zc_parity w v (by rw [hs]; exact hpar)]; simp

/-- `Z_J(v)·1[S_J = t] = Σ_{P ⊆ J} 1[2S_P − S_J = v, S_J = t]`. -/
theorem Zs_ind (J : Finset (Fin m)) (v t : ℤ) (w : Fin m → Fin M) :
    (if SJ J w = t then (RandomWeights.Zs (fun i => (w i : ℤ) + 1) J v : ℝ) else 0) =
      ∑ P ∈ J.powerset, if 2 * SJ P w - SJ J w = v ∧ SJ J w = t then (1 : ℝ) else 0 := by
  unfold RandomWeights.Zs
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  split_ifs with h
  · refine sum_congr rfl fun P _ => ?_
    unfold SJ at h ⊢
    simp only [h, and_true, Nat.cast_one]
  · symm; exact sum_eq_zero fun P _ => by simp [h]

/-- **The factorization on a fixed set `D` of differing positions**:
`E[Z_{E∖D}(u) Z_D(0); S_E = s] = Σ_{s₁} E[Z_{m−k}(u); S_{m−k} = s₁]·E[Z_k(0); S_k = s − s₁]`. -/
theorem factor_D (hM : 0 < M) (D : Finset (Fin m)) (u s : ℤ) :
    (∑ w : Fin m → Fin M, if Sw w = s then
        (RandomWeights.Zs (fun i => (w i : ℤ) + 1) Dᶜ u : ℝ) *
          RandomWeights.Zs (fun i => (w i : ℤ) + 1) D 0 else 0) / (M : ℝ) ^ m =
      ∑ s₁ ∈ I0 m M, PhiZ M (m - D.card) u s₁ * PhiZ M D.card 0 (s - s₁) := by
  -- split `1[S_E = s]` over the value `s₁` of `S_{Dᶜ}`
  have hsplit : ∀ w : Fin m → Fin M,
      (if Sw w = s then (RandomWeights.Zs (fun i => (w i : ℤ) + 1) Dᶜ u : ℝ) *
          RandomWeights.Zs (fun i => (w i : ℤ) + 1) D 0 else 0) =
        ∑ s₁ ∈ I0 m M, (if SJ Dᶜ w = s₁ then (RandomWeights.Zs (fun i => (w i : ℤ) + 1) Dᶜ u : ℝ)
            else 0) * (if SJ D w = s - s₁ then (RandomWeights.Zs (fun i => (w i : ℤ) + 1) D 0 : ℝ)
            else 0) := by
    intro w
    have hE : Sw w = SJ Dᶜ w + SJ D w := by rw [Sw_eq w D]; ring
    have hmem : SJ Dᶜ w ∈ I0 m M := by unfold I0; rw [mem_Icc]; exact SJ_le Dᶜ w
    rw [sum_eq_single_of_mem (SJ Dᶜ w) hmem (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])]
    rw [if_pos rfl]
    by_cases h : Sw w = s
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega), mul_zero]
  rw [sum_congr rfl fun w _ => hsplit w, sum_comm, sum_div]
  refine sum_congr rfl fun s₁ _ => ?_
  have hd : Disjoint Dᶜ D := disjoint_compl_left
  have key : ∀ P ∈ Dᶜ.powerset, ∀ Q ∈ D.powerset,
      prW M m (fun w => 2 * SJ P w - SJ Dᶜ w = u ∧ SJ Dᶜ w = s₁) *
        prW M m (fun w => 2 * SJ Q w - SJ D w = 0 ∧ SJ D w = s - s₁) =
      (∑ w : Fin m → Fin M, (if 2 * SJ P w - SJ Dᶜ w = u ∧ SJ Dᶜ w = s₁ then (1 : ℝ) else 0) *
        (if 2 * SJ Q w - SJ D w = 0 ∧ SJ D w = s - s₁ then (1 : ℝ) else 0)) / (M : ℝ) ^ m := by
    intro P hP Q hQ
    rw [mem_powerset] at hP hQ
    rw [← prW_and hM hd _ _ (dependsOn_SJ2 hP (fun x y => 2 * x - y = u ∧ y = s₁))
      (dependsOn_SJ2 hQ (fun x y => 2 * x - y = 0 ∧ y = s - s₁))]
    unfold prW
    congr 1
    refine sum_congr rfl fun w _ => ?_
    dsimp only
    by_cases h1 : 2 * SJ P w - SJ Dᶜ w = u ∧ SJ Dᶜ w = s₁ <;>
      by_cases h2 : 2 * SJ Q w - SJ D w = 0 ∧ SJ D w = s - s₁
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, mul_one]
    · rw [if_neg (fun h => h2 h.2), if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
  have hcD : Dᶜ.card = m - D.card := by rw [card_compl, Fintype.card_fin]
  rw [← hcD, ← sumP_eq hM Dᶜ u s₁, ← sumP_eq hM D 0 (s - s₁), sum_mul_sum,
    sum_congr rfl fun P hP => sum_congr rfl fun Q hQ => key P hP Q hQ]
  simp only [← sum_div]
  congr 1
  simp only [Zs_ind, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_comm]

/-- `Z(u)² = Σ_{D ⊆ E} Z_{E∖D}(u)·Z_D(0)` (`Z_sq_split` for the block `E = Fin m`). -/
theorem Zc_sq_split (w : Fin m → Fin M) (u : ℤ) :
    (Zc w u : ℝ) ^ 2 = ∑ D ∈ (univ : Finset (Fin m)).powerset,
      (RandomWeights.Zs (fun i => (w i : ℤ) + 1) Dᶜ u : ℝ) *
        RandomWeights.Zs (fun i => (w i : ℤ) + 1) D 0 := by
  rw [Zc_eq_Zs]
  have := RandomWeights.Z_sq_split (fun i => (w i : ℤ) + 1) (univ : Finset (Fin m)) u
  simp only [← compl_eq_univ_sdiff] at this
  exact_mod_cast this

/-- **Lemma B‴, unconditioned form**:
`E[Z(u)²; S_E = s] = Σ_k C(m,k) Σ_{s₁} E[Z_{m−k}(u); S_{m−k} = s₁]·E[Z_k(0); S_k = s − s₁]`. -/
theorem sumZ2_split (hM : 0 < M) (u s : ℤ) :
    (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2) / (M : ℝ) ^ m =
      ∑ k ∈ range (m + 1), (m.choose k : ℝ) *
        ∑ s₁ ∈ I0 m M, PhiZ M (m - k) u s₁ * PhiZ M k 0 (s - s₁) := by
  rw [sum_filter]
  have h1 : ∀ w : Fin m → Fin M, (if Sw w = s then (Zc w u : ℝ) ^ 2 else 0) =
      ∑ D ∈ (univ : Finset (Fin m)).powerset, if Sw w = s then
        (RandomWeights.Zs (fun i => (w i : ℤ) + 1) Dᶜ u : ℝ) *
          RandomWeights.Zs (fun i => (w i : ℤ) + 1) D 0 else 0 := by
    intro w
    split_ifs
    · exact Zc_sq_split w u
    · simp
  rw [sum_congr rfl fun w _ => h1 w, sum_comm, sum_div]
  rw [sum_congr rfl fun D _ => factor_D hM D u s]
  have := sum_powerset_apply_card
    (fun k => ∑ s₁ ∈ I0 m M, PhiZ M (m - k) u s₁ * PhiZ M k 0 (s - s₁)) (x := (univ : Finset (Fin m)))
  rw [this, card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **Lemma B‴ (exact reduction to first moments)** (paper §6.3). With
`λ_k(v, t) = E[#{ε ∈ {±1}^k : Σ ε_i w_i = v} | S_k = t]` (`lamZ`),
`E[Z(u)² | S_E = s] = Σ_k C(m,k) Σ_{s₁} Pr(S_{m−k} = s₁)Pr(S_k = s − s₁)/Pr(S_m = s) ·
  λ_{m−k}(u, s₁)·λ_k(0, s − s₁)`.
The sum over `s₁` runs over `[0, mM]`, which contains every value of `S_{m−k}`. -/
theorem lemmaBppp (hM : 0 < M) (u s : ℤ) :
    condZ2 M m u s = ∑ k ∈ range (m + 1), (m.choose k : ℝ) * ∑ s₁ ∈ I0 m M,
      lawS M (m - k) s₁ * lawS M k (s - s₁) / lawS M m s * lamZ M (m - k) u s₁ * lamZ M k 0 (s - s₁) := by
  unfold condZ2
  rw [sumZ2_split hM, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_div_assoc, sum_div]
  congr 1
  refine sum_congr rfl fun s₁ _ => ?_
  rw [PhiZ_eq hM, PhiZ_eq hM]
  ring

end ArcsAlgo.LLT
