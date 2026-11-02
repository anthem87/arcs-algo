module

public import ArcsAlgo.Uniform.Pair
set_option autoImplicit false

/-!
# Lemma V: one pair (paper §6.7)

For `𝒫₁` with halves `A`, `B = E ∖ A`, a pair `(x, x′)` with `x ≠ x′` contributes to `D_eq` the
probability `Pr(S_x = S_{x′} = a, S_{x∩A} = S_{x′∩A}, S_E = s)` (`pairPA`).

* `pairPA_le`: with the six classes `C = x ∩ x′`, `D = E ∖ (x ∪ x′)`, `10A`, `01A`, `10B`, `01B`
  (independent sums), if `01A, 10B, 01B` are non-empty the probability is `≤ M⁻³`, and `≤ M⁻⁴` when
  `C ∪ D ≠ ∅`: three factors are `≤ 1/M` by (T1), and `Σ_c Pr(S_C = c) Pr(S_D = c − u) ≤ 1/M`.
* `pairPA_zero`: two classes required to have equal sums cannot have exactly one of them empty.
* `pairPA_bound`: for every pair, `≤ M⁻³(1[x_A = x′_A] + 1[x_B = x′_B] + 1[x′ = E ∖ x]) + M⁻⁴`
  (when one half agrees, the pair is a pair of Lemma B, `pairP_le_inv3`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

theorem prW_mono {E E' : (Fin m → Fin M) → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ w, E w → E' w) : prW M m E ≤ prW M m E' := by
  unfold prW
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum fun w _ => by
    by_cases hw : E w
    · rw [if_pos hw, if_pos (h w hw)]
    · rw [if_neg hw]; split_ifs <;> norm_num

/-- `Pr(S_x = a, S_{x′} = a, S_{x∩A} = S_{x′∩A}, S_E = s)`: the pairs of Lemma V. -/
noncomputable def pairPA (M m : ℕ) (A x y : Finset (Fin m)) (a s : ℤ) : ℝ :=
  prW M m (fun w => SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s)

theorem pairPA_le_pairP (A x y : Finset (Fin m)) (a s : ℤ) : pairPA M m A x y a s ≤ pairP M m x y a s :=
  prW_mono fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩

theorem SJ_union {J K : Finset (Fin m)} (h : Disjoint J K) (w : Fin m → Fin M) :
    SJ (J ∪ K) w = SJ J w + SJ K w := by unfold SJ; rw [sum_union h]

theorem lawS_le_inv'' (hM : 0 < M) {k : ℕ} (hk : 1 ≤ k) (v : ℤ) : lawS M k v ≤ 1 / M :=
  lawS_le_inv' hM hk v

theorem SJ_split {J U V : Finset (Fin m)} (hJ : J = U ∪ V) (hd : Disjoint U V) (w : Fin m → Fin M) :
    SJ J w = SJ U w + SJ V w := by rw [hJ]; exact SJ_union hd w

theorem Sw_eq_SJ (w : Fin m → Fin M) : Sw w = SJ univ w := rfl

/-- **The pairs of Lemma V whose halves both differ** (paper §6.7): with the six classes
`C = x ∩ x′`, `D = E ∖ (x ∪ x′)`, `10A`, `01A`, `10B`, `01B`, if the classes `01A, 10B, 01B` are
non-empty, the probability is at most `M⁻³`, and at most `M⁻⁴` if `C ∪ D ≠ ∅`. -/
theorem pairPA_le (hM : 0 < M) (A x y : Finset (Fin m)) (a s : ℤ)
    (h2 : 1 ≤ ((y \ x) ∩ A).card) (h3 : 1 ≤ ((x \ y) \ A).card) (h4 : 1 ≤ ((y \ x) \ A).card) :
    pairPA M m A x y a s ≤ 1 / (M : ℝ) ^ 3 *
      (if 1 ≤ (x ∩ y).card ∨ 1 ≤ (x ∪ y)ᶜ.card then 1 / (M : ℝ) else 1) := by
  obtain ⟨C, hC⟩ : ∃ C, C = x ∩ y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (x ∪ y)ᶜ := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, P = (x \ y) ∩ A := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = (y \ x) ∩ A := ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ P, P = (x \ y) \ A := ⟨_, rfl⟩
  obtain ⟨P4, hP4⟩ : ∃ P, P = (y \ x) \ A := ⟨_, rfl⟩
  rw [← hC, ← hD]; rw [← hP2] at h2; rw [← hP3] at h3; rw [← hP4] at h4
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have dj : ∀ {U V : Finset (Fin m)}, (∀ i, i ∈ U → i ∉ V) → Disjoint U V := fun h =>
    disjoint_left.mpr h
  subst hC hD hP1 hP2 hP3 hP4
  -- the class sums
  have hx : ∀ w : Fin m → Fin M, SJ x w = SJ (x ∩ y) w + SJ ((x \ y) ∩ A) w + SJ ((x \ y) \ A) w := by
    intro w
    rw [SJ_split (U := x ∩ y ∪ (x \ y) ∩ A) (V := (x \ y) \ A) (by ext i; simp; tauto)
      (dj fun i hi => by simp at hi ⊢; tauto),
      SJ_split (J := x ∩ y ∪ (x \ y) ∩ A) rfl (dj fun i hi => by simp at hi ⊢; tauto)]
  have hy : ∀ w : Fin m → Fin M, SJ y w = SJ (x ∩ y) w + SJ ((y \ x) ∩ A) w + SJ ((y \ x) \ A) w := by
    intro w
    rw [SJ_split (U := x ∩ y ∪ (y \ x) ∩ A) (V := (y \ x) \ A) (by ext i; simp; tauto)
      (dj fun i hi => by simp at hi ⊢; tauto),
      SJ_split (J := x ∩ y ∪ (y \ x) ∩ A) rfl (dj fun i hi => by simp at hi ⊢; tauto)]
  have hxA : ∀ w : Fin m → Fin M, SJ (x ∩ A) w = SJ (x ∩ y ∩ A) w + SJ ((x \ y) ∩ A) w := fun w =>
    SJ_split (by ext i; simp; tauto) (dj fun i hi => by simp at hi ⊢; tauto) w
  have hyA : ∀ w : Fin m → Fin M, SJ (y ∩ A) w = SJ (x ∩ y ∩ A) w + SJ ((y \ x) ∩ A) w := fun w =>
    SJ_split (by ext i; simp; tauto) (dj fun i hi => by simp at hi ⊢; tauto) w
  have hE : ∀ w : Fin m → Fin M, Sw w = SJ (x ∩ y) w + SJ ((x \ y) ∩ A) w + SJ ((y \ x) ∩ A) w +
      SJ ((x \ y) \ A) w + SJ ((y \ x) \ A) w + SJ (x ∪ y)ᶜ w := by
    intro w
    rw [Sw_eq_SJ, SJ_split (U := x ∪ y) (V := (x ∪ y)ᶜ) (by ext i; simp; tauto) disjoint_compl_right,
      SJ_split (J := x ∪ y) (U := x) (V := (y \ x) ∩ A ∪ (y \ x) \ A) (by ext i; simp; tauto)
        (dj fun i hi => by simp at hi ⊢; tauto),
      SJ_split (J := (y \ x) ∩ A ∪ (y \ x) \ A) rfl (dj fun i hi => by simp at hi ⊢; tauto), hx]
    ring
  -- the decomposition over `c = S_C`, `α = S_{10A}`
  set C := x ∩ y; set D := (x ∪ y)ᶜ
  set P1 := (x \ y) ∩ A; set P2 := (y \ x) ∩ A; set P3 := (x \ y) \ A; set P4 := (y \ x) \ A
  let F : ℤ → ℤ → (Fin m → Fin M) → Prop := fun c α w =>
    SJ C w = c ∧ (SJ P1 w = α ∧ (SJ P2 w = α ∧ (SJ P3 w = a - c - α ∧
      (SJ P4 w = a - c - α ∧ SJ D w = s - 2 * a + c))))
  have hind : ∀ w : Fin m → Fin M,
      (if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s then (1 : ℝ) else 0) =
      ∑ c ∈ I0 m M, ∑ α ∈ I0 m M, if F c α w then (1 : ℝ) else 0 := by
    intro w
    have hmC : SJ C w ∈ I0 m M := by unfold I0; rw [mem_Icc]; exact SJ_le C w
    have hm1 : SJ P1 w ∈ I0 m M := by unfold I0; rw [mem_Icc]; exact SJ_le P1 w
    have hF : ∀ c α, F c α w ↔ (c = SJ C w ∧ α = SJ P1 w) ∧
        (SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s) := by
      intro c α; simp only [F]
      have := hx w; have := hy w; have := hxA w; have := hyA w; have := hE w
      constructor
      · rintro ⟨e1, e2, e3, e4, e5, e6⟩; refine ⟨⟨e1.symm, e2.symm⟩, ?_, ?_, ?_, ?_⟩ <;> omega
      · rintro ⟨⟨e1, e2⟩, f1, f2, f3, f4⟩; refine ⟨e1.symm, e2.symm, ?_, ?_, ?_, ?_⟩ <;> omega
    simp only [hF]
    by_cases hev : SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s
    · simp only [hev, and_true, ite_true]
      rw [sum_eq_single (SJ C w)]
      · rw [sum_eq_single (SJ P1 w)]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd hm1 h
      · intro b _ hb; exact sum_eq_zero fun α _ => by simp [hb]
      · intro h; exact absurd hmC h
    · simp [hev]
  have dC1 : Disjoint C (P1 ∪ (P2 ∪ (P3 ∪ (P4 ∪ D)))) := dj fun i hi => by
    simp [C, P1, P2, P3, P4, D] at hi ⊢; tauto
  have d12 : Disjoint P1 (P2 ∪ (P3 ∪ (P4 ∪ D))) := dj fun i hi => by
    simp [P1, P2, P3, P4, D] at hi ⊢; tauto
  have d23 : Disjoint P2 (P3 ∪ (P4 ∪ D)) := dj fun i hi => by simp [P2, P3, P4, D] at hi ⊢; tauto
  have d34 : Disjoint P3 (P4 ∪ D) := dj fun i hi => by simp [P3, P4, D] at hi ⊢; tauto
  have d4D : Disjoint P4 D := dj fun i hi => by simp [P4, D] at hi ⊢; tauto
  have hprod : ∀ c α, prW M m (F c α) = lawS M C.card c * lawS M P1.card α * lawS M P2.card α *
      lawS M P3.card (a - c - α) * lawS M P4.card (a - c - α) * lawS M D.card (s - 2 * a + c) := by
    intro c α
    have dD := dependsOn_SJ (M := M) D (· = s - 2 * a + c)
    have d4 := dependsOn_SJ (M := M) P4 (· = a - c - α)
    have d3 := dependsOn_SJ (M := M) P3 (· = a - c - α)
    have d2 := dependsOn_SJ (M := M) P2 (· = α)
    have d1 := dependsOn_SJ (M := M) P1 (· = α)
    have d0 := dependsOn_SJ (M := M) C (· = c)
    have e5 := prW_and hM d4D _ _ d4 dD
    have e4 := prW_and hM d34 _ _ d3 (dependsOn_and d4 dD)
    have e3 := prW_and hM d23 _ _ d2 (dependsOn_and d3 (dependsOn_and d4 dD))
    have e2 := prW_and hM d12 _ _ d1 (dependsOn_and d2 (dependsOn_and d3 (dependsOn_and d4 dD)))
    have e1 := prW_and hM dC1 _ _ d0
      (dependsOn_and d1 (dependsOn_and d2 (dependsOn_and d3 (dependsOn_and d4 dD))))
    simp only [F]
    rw [e1, e2, e3, e4, e5, prW_SJ hM, prW_SJ hM, prW_SJ hM, prW_SJ hM, prW_SJ hM, prW_SJ hM]; ring
  have hsum : pairPA M m A x y a s = ∑ c ∈ I0 m M, ∑ α ∈ I0 m M, prW M m (F c α) := by
    unfold pairPA prW
    rw [sum_congr rfl fun w _ => hind w, sum_comm, sum_div]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm, sum_div]
  rw [hsum]
  simp only [hprod]
  -- the bound
  have hP2 := lawS_le_inv'' hM h2
  have hP3 := lawS_le_inv'' hM h3
  have hP4 := lawS_le_inv'' hM h4
  have hinner : ∀ c, ∑ α ∈ I0 m M, lawS M C.card c * lawS M P1.card α * lawS M P2.card α *
      lawS M P3.card (a - c - α) * lawS M P4.card (a - c - α) * lawS M D.card (s - 2 * a + c) ≤
      1 / (M : ℝ) ^ 3 * (lawS M C.card c * lawS M D.card (s - 2 * a + c)) := by
    intro c
    have hp0 := mul_nonneg (lawS_nonneg M C.card c) (lawS_nonneg M D.card (s - 2 * a + c))
    calc ∑ α ∈ I0 m M, lawS M C.card c * lawS M P1.card α * lawS M P2.card α *
          lawS M P3.card (a - c - α) * lawS M P4.card (a - c - α) * lawS M D.card (s - 2 * a + c)
        ≤ ∑ α ∈ I0 m M, lawS M P1.card α * ((1 / (M : ℝ)) ^ 3 *
            (lawS M C.card c * lawS M D.card (s - 2 * a + c))) := by
          refine sum_le_sum fun α _ => ?_
          have q1 := lawS_nonneg M P1.card α
          have q2 := lawS_nonneg M P2.card α
          have q3 := lawS_nonneg M P3.card (a - c - α)
          have q4 := lawS_nonneg M P4.card (a - c - α)
          have hM0 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
          have h234 : lawS M P2.card α * lawS M P3.card (a - c - α) * lawS M P4.card (a - c - α) ≤
              (1 / (M : ℝ)) ^ 3 := by
            have := mul_le_mul (mul_le_mul (hP2 α) (hP3 (a - c - α)) q3 hM0) (hP4 (a - c - α)) q4
              (mul_nonneg hM0 hM0)
            calc _ ≤ 1 / (M : ℝ) * (1 / M) * (1 / M) := this
              _ = (1 / (M : ℝ)) ^ 3 := by ring
          calc _ = lawS M P1.card α * (lawS M P2.card α * lawS M P3.card (a - c - α) *
                  lawS M P4.card (a - c - α)) * (lawS M C.card c * lawS M D.card (s - 2 * a + c)) := by ring
            _ ≤ lawS M P1.card α * (1 / (M : ℝ)) ^ 3 * (lawS M C.card c * lawS M D.card (s - 2 * a + c)) := by
                gcongr
            _ = _ := by ring
      _ = (∑ α ∈ I0 m M, lawS M P1.card (id α)) * ((1 / (M : ℝ)) ^ 3 *
            (lawS M C.card c * lawS M D.card (s - 2 * a + c))) := by rw [sum_mul]; rfl
      _ ≤ 1 * ((1 / (M : ℝ)) ^ 3 * (lawS M C.card c * lawS M D.card (s - 2 * a + c))) :=
          mul_le_mul_of_nonneg_right (sum_lawS_le hM _ _ Function.injective_id) (by positivity)
      _ = _ := by rw [one_mul, one_div_pow]
  have hinj : Function.Injective fun c : ℤ => s - 2 * a + c := fun c d h => by simp only at h; omega
  have hCD : ∑ c ∈ I0 m M, lawS M C.card c * lawS M D.card (s - 2 * a + c) ≤
      (if 1 ≤ C.card ∨ 1 ≤ D.card then 1 / (M : ℝ) else 1) := by
    split_ifs with hcd
    · rcases hcd with hγ | hδ
      · calc ∑ c ∈ I0 m M, lawS M C.card c * lawS M D.card (s - 2 * a + c)
            ≤ ∑ c ∈ I0 m M, 1 / (M : ℝ) * lawS M D.card (s - 2 * a + c) :=
              sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (lawS_le_inv'' hM hγ c) (lawS_nonneg _ _ _)
          _ = 1 / M * ∑ c ∈ I0 m M, lawS M D.card (s - 2 * a + c) := by rw [mul_sum]
          _ ≤ 1 / M * 1 := mul_le_mul_of_nonneg_left
              (sum_lawS_le (f := fun c => s - 2 * a + c) hM _ _ hinj) (by positivity)
          _ = 1 / M := mul_one _
      · calc ∑ c ∈ I0 m M, lawS M C.card c * lawS M D.card (s - 2 * a + c)
            ≤ ∑ c ∈ I0 m M, lawS M C.card c * (1 / (M : ℝ)) :=
              sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (lawS_le_inv'' hM hδ _) (lawS_nonneg _ _ _)
          _ = (∑ c ∈ I0 m M, lawS M C.card (id c)) * (1 / M) := by rw [sum_mul]; rfl
          _ ≤ 1 * (1 / M) := mul_le_mul_of_nonneg_right
              (sum_lawS_le hM _ _ Function.injective_id) (by positivity)
          _ = 1 / M := one_mul _
    · calc ∑ c ∈ I0 m M, lawS M C.card c * lawS M D.card (s - 2 * a + c)
          ≤ ∑ c ∈ I0 m M, lawS M C.card (id c) * 1 :=
            sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (by
              have := sum_lawS_le (f := fun c => s - 2 * a + c) hM D.card {c} hinj
              simpa using this) (lawS_nonneg _ _ _)
        _ ≤ 1 := by simp only [mul_one]; exact sum_lawS_le hM _ _ Function.injective_id
  calc ∑ c ∈ I0 m M, ∑ α ∈ I0 m M, lawS M C.card c * lawS M P1.card α * lawS M P2.card α *
        lawS M P3.card (a - c - α) * lawS M P4.card (a - c - α) * lawS M D.card (s - 2 * a + c)
      ≤ ∑ c ∈ I0 m M, 1 / (M : ℝ) ^ 3 * (lawS M C.card c * lawS M D.card (s - 2 * a + c)) :=
        sum_le_sum fun c _ => hinner c
    _ = 1 / (M : ℝ) ^ 3 * ∑ c ∈ I0 m M, lawS M C.card c * lawS M D.card (s - 2 * a + c) := by
        rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hCD (by positivity)

theorem SJ_ge_card (J : Finset (Fin m)) (w : Fin m → Fin M) : (J.card : ℤ) ≤ SJ J w := by
  unfold SJ
  calc (J.card : ℤ) = ∑ _i ∈ J, (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ J, ((w i : ℤ) + 1) := by
        apply sum_le_sum; intro i _
        have : (0 : ℤ) ≤ (w i : ℤ) := by positivity
        linarith

theorem SJ_empty (w : Fin m → Fin M) : SJ ∅ w = 0 := by unfold SJ; simp

theorem prW_false {E : (Fin m → Fin M) → Prop} [DecidablePred E] (h : ∀ w, ¬ E w) : prW M m E = 0 := by
  unfold prW; rw [sum_eq_zero fun w _ => if_neg (h w)]; simp

/-- Two classes required to have equal sums cannot have exactly one of them empty. -/
theorem pairPA_zero (A x y : Finset (Fin m)) (a s : ℤ)
    (h : ((x \ y) ∩ A = ∅ ∧ (y \ x) ∩ A ≠ ∅) ∨ ((x \ y) ∩ A ≠ ∅ ∧ (y \ x) ∩ A = ∅) ∨
      ((x \ y) \ A = ∅ ∧ (y \ x) \ A ≠ ∅) ∨ ((x \ y) \ A ≠ ∅ ∧ (y \ x) \ A = ∅)) :
    pairPA M m A x y a s = 0 := by
  unfold pairPA
  apply prW_false
  rintro w ⟨e1, e2, e3, -⟩
  have dj : ∀ {U V : Finset (Fin m)}, (∀ i, i ∈ U → i ∉ V) → Disjoint U V := fun h =>
    disjoint_left.mpr h
  have hxA : SJ (x ∩ A) w = SJ (x ∩ y ∩ A) w + SJ ((x \ y) ∩ A) w :=
    SJ_split (by ext i; simp; tauto) (dj fun i hi => by simp at hi ⊢; tauto) w
  have hyA : SJ (y ∩ A) w = SJ (x ∩ y ∩ A) w + SJ ((y \ x) ∩ A) w :=
    SJ_split (by ext i; simp; tauto) (dj fun i hi => by simp at hi ⊢; tauto) w
  have hx : SJ x w = SJ (x ∩ A) w + SJ ((x \ y) \ A) w + SJ ((x ∩ y) \ A) w := by
    rw [SJ_split (U := x ∩ A ∪ (x \ y) \ A) (V := (x ∩ y) \ A) (by ext i; simp; tauto)
      (dj fun i hi => by simp at hi ⊢; tauto),
      SJ_split (J := x ∩ A ∪ (x \ y) \ A) rfl (dj fun i hi => by simp at hi ⊢; tauto)]
  have hy : SJ y w = SJ (y ∩ A) w + SJ ((y \ x) \ A) w + SJ ((x ∩ y) \ A) w := by
    rw [SJ_split (U := y ∩ A ∪ (y \ x) \ A) (V := (x ∩ y) \ A) (by ext i; simp; tauto)
      (dj fun i hi => by simp at hi ⊢; tauto),
      SJ_split (J := y ∩ A ∪ (y \ x) \ A) rfl (dj fun i hi => by simp at hi ⊢; tauto)]
  have pos : ∀ J : Finset (Fin m), J ≠ ∅ → 1 ≤ SJ J w := fun J hJ => by
    have := SJ_ge_card J w
    have : 1 ≤ J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
    omega
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := pos _ h2; rw [h1, SJ_empty] at hxA; omega
  · have := pos _ h1; rw [h2, SJ_empty] at hyA; omega
  · have := pos _ h2; rw [h1, SJ_empty] at hx; omega
  · have := pos _ h1; rw [h2, SJ_empty] at hy; omega

/-- **The bound of one pair in Lemma V**: for `x ≠ x′`,
`Pr ≤ M⁻³(1[x_A = x′_A] + 1[x_B = x′_B] + 1[x′ = E ∖ x]) + M⁻⁴`, given non-empty halves `A`, `Aᶜ`. -/
theorem pairPA_bound (hM : 0 < M) {A x y : Finset (Fin m)} (hA : A.Nonempty) (hB : Aᶜ.Nonempty)
    (hxy : x ≠ y) (a s : ℤ) :
    pairPA M m A x y a s ≤ 1 / (M : ℝ) ^ 3 * ((if x ∩ A = y ∩ A then 1 else 0) +
      (if x \ A = y \ A then 1 else 0) + (if y = xᶜ then 1 else 0)) + 1 / (M : ℝ) ^ 4 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (0 : ℝ) ≤ 1 / (M : ℝ) ^ 3 := by positivity
  have h4 : (0 : ℝ) ≤ 1 / (M : ℝ) ^ 4 := by positivity
  have hnn : ∀ P : Prop, [Decidable P] → (0 : ℝ) ≤ if P then 1 else 0 := fun P _ => by
    split_ifs <;> norm_num
  set i1 : ℝ := if x ∩ A = y ∩ A then 1 else 0
  set i2 : ℝ := if x \ A = y \ A then 1 else 0
  set i3 : ℝ := if y = xᶜ then 1 else 0
  have hi1 := hnn (x ∩ A = y ∩ A); have hi2 := hnn (x \ A = y \ A); have hi3 := hnn (y = xᶜ)
  -- one half equal: Lemma B's bound `M⁻³`
  by_cases hA' : x ∩ A = y ∩ A
  · have hyc : y ≠ xᶜ := by
      rintro rfl
      obtain ⟨i, hi⟩ := hA
      have := congrArg (i ∈ ·) hA'; simp [hi] at this
    have hp := (pairPA_le_pairP A x y a s).trans (pairP_le_inv3 hM hxy hyc a s)
    have e : i1 = 1 := if_pos hA'
    have : 1 / (M : ℝ) ^ 3 ≤ 1 / (M : ℝ) ^ 3 * (i1 + i2 + i3) :=
      le_mul_of_one_le_right h3 (by rw [e]; linarith)
    linarith
  by_cases hB' : x \ A = y \ A
  · have hyc : y ≠ xᶜ := by
      rintro rfl
      obtain ⟨i, hi⟩ := hB
      have := congrArg (i ∈ ·) hB'; simp at hi; simp [hi] at this
    have hp := (pairPA_le_pairP A x y a s).trans (pairP_le_inv3 hM hxy hyc a s)
    have e : i2 = 1 := if_pos hB'
    have : 1 / (M : ℝ) ^ 3 ≤ 1 / (M : ℝ) ^ 3 * (i1 + i2 + i3) :=
      le_mul_of_one_le_right h3 (by rw [e]; linarith)
    linarith
  -- both halves differ
  have e1 : i1 = 0 := if_neg hA'
  have e2 : i2 = 0 := if_neg hB'
  rw [e1, e2]
  by_cases hz : ((x \ y) ∩ A = ∅ ∧ (y \ x) ∩ A ≠ ∅) ∨ ((x \ y) ∩ A ≠ ∅ ∧ (y \ x) ∩ A = ∅) ∨
      ((x \ y) \ A = ∅ ∧ (y \ x) \ A ≠ ∅) ∨ ((x \ y) \ A ≠ ∅ ∧ (y \ x) \ A = ∅)
  · rw [pairPA_zero A x y a s hz]
    have : 0 ≤ 1 / (M : ℝ) ^ 3 * (0 + 0 + i3) := mul_nonneg h3 (by linarith)
    linarith
  -- the four classes `10A, 01A, 10B, 01B` are non-empty
  have nA : (x \ y) ∩ A ≠ ∅ ∨ (y \ x) ∩ A ≠ ∅ := by
    by_contra h; push Not at h
    apply hA'; ext i
    have h1 := Finset.eq_empty_iff_forall_notMem.mp h.1 i
    have h2 := Finset.eq_empty_iff_forall_notMem.mp h.2 i
    simp only [mem_inter, mem_sdiff] at h1 h2 ⊢; clear * - h1 h2; tauto
  have nB : (x \ y) \ A ≠ ∅ ∨ (y \ x) \ A ≠ ∅ := by
    by_contra h; push Not at h
    apply hB'; ext i
    have h1 := Finset.eq_empty_iff_forall_notMem.mp h.1 i
    have h2 := Finset.eq_empty_iff_forall_notMem.mp h.2 i
    simp only [mem_inter, mem_sdiff] at h1 h2 ⊢; clear * - h1 h2; tauto
  have c2 : (y \ x) ∩ A ≠ ∅ := by
    intro hP2
    rcases nA with h | h
    · exact hz (Or.inr (Or.inl ⟨h, hP2⟩))
    · exact h hP2
  have c3 : (x \ y) \ A ≠ ∅ := by
    intro hP3
    rcases nB with h | h
    · exact h hP3
    · exact hz (Or.inr (Or.inr (Or.inl ⟨hP3, h⟩)))
  have c4 : (y \ x) \ A ≠ ∅ := by
    intro hP4
    rcases nB with h | h
    · exact hz (Or.inr (Or.inr (Or.inr ⟨h, hP4⟩)))
    · exact h hP4
  have card1 : ∀ J : Finset (Fin m), J ≠ ∅ → 1 ≤ J.card := fun J hJ =>
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
  have hb := pairPA_le hM A x y a s (card1 _ c2) (card1 _ c3) (card1 _ c4)
  refine hb.trans ?_
  have h34 : 1 / (M : ℝ) ^ 3 * (1 / M) = 1 / (M : ℝ) ^ 4 := by field_simp
  have hi3' : 0 ≤ 1 / (M : ℝ) ^ 3 * (0 + 0 + i3) := mul_nonneg h3 (by linarith)
  split_ifs with hcd
  · rw [h34]; linarith
  · by_cases hyc : y = xᶜ
    · have e3 : i3 = 1 := if_pos hyc
      rw [e3]; linarith
    exfalso; apply hyc
    push Not at hcd
    have e1 : x ∩ y = ∅ := Finset.card_eq_zero.mp (by omega)
    have e2 : (x ∪ y)ᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
    ext i
    have h1 := Finset.eq_empty_iff_forall_notMem.mp e1 i
    have h2 := Finset.eq_empty_iff_forall_notMem.mp e2 i
    simp only [mem_inter, mem_compl, mem_union] at h1 h2 ⊢; clear * - h1 h2; tauto

end ArcsAlgo.LLT
