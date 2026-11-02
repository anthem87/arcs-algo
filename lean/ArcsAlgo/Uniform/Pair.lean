module

public import ArcsAlgo.Uniform.SecondId
set_option autoImplicit false

/-!
# Diagonal, complementary and atypical pairs (paper §6.3, proof of Lemma B(2))

* `pairP_diag`: the diagonal `y = x` gives `Pr(S_x = a, S_{E∖x} = s − a)`, summing to `λ Pr(S_E = s)`.
* `pairP_compl_eq`, `pairP_compl_zero`: the pairs `y = E ∖ x` give the same for `u = 0` and vanish
  otherwise, so they sum to `λ·1[u = 0] Pr(S_E = s)`.
* `pairP_le_inv3`: every other pair has probability `≤ M⁻³` (by (T1), `Pr(S_k = v) ≤ 1/M`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `Pr(S_x = a, S_{E∖x} = s − a) = Pr(S_{|x|} = a) Pr(S_{m−|x|} = s − a)`. -/
noncomputable def Rx (M m : ℕ) (x : Finset (Fin m)) (a s : ℤ) : ℝ :=
  lawS M x.card a * lawS M (m - x.card) (s - a)

theorem Rx_nonneg (x : Finset (Fin m)) (a s : ℤ) : 0 ≤ Rx M m x a s :=
  mul_nonneg (lawS_nonneg _ _ _) (lawS_nonneg _ _ _)

theorem prW_split (hM : 0 < M) (x : Finset (Fin m)) (a b : ℤ) :
    prW M m (fun w => SJ x w = a ∧ SJ xᶜ w = b) = lawS M x.card a * lawS M (m - x.card) b := by
  rw [prW_and hM disjoint_compl_right _ _ (dependsOn_SJ x (· = a)) (dependsOn_SJ xᶜ (· = b)),
    prW_SJ hM, prW_SJ hM, card_compl, Fintype.card_fin]

/-- The diagonal pairs `y = x`. -/
theorem pairP_diag (hM : 0 < M) (x : Finset (Fin m)) (a s : ℤ) :
    pairP M m x x a s = Rx M m x a s := by
  unfold pairP Rx
  rw [← prW_split hM]
  apply prW_congr; intro w
  have := Sw_eq w x
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h1, by omega⟩

/-- The complementary pairs `y = E ∖ x`, for `u = 0` (`a = s − a`). -/
theorem pairP_compl_eq (hM : 0 < M) (x : Finset (Fin m)) {a s : ℤ} (h : a = s - a) :
    pairP M m x xᶜ a s = Rx M m x a s := by
  unfold pairP Rx
  rw [← prW_split hM]
  apply prW_congr; intro w
  have := Sw_eq w x
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩

/-- The complementary pairs vanish for `u ≠ 0`. -/
theorem pairP_compl_zero (x : Finset (Fin m)) {a s : ℤ} (h : a ≠ s - a) :
    pairP M m x xᶜ a s = 0 := by
  unfold pairP prW
  rw [div_eq_zero_iff]; left
  refine sum_eq_zero fun w _ => ?_
  have := Sw_eq w x
  rw [if_neg]; rintro ⟨h1, h2, h3⟩; omega

theorem lawS_le_inv' (hM : 0 < M) {k : ℕ} (hk : 1 ≤ k) (v : ℤ) : lawS M k v ≤ 1 / M := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact lawS_le_inv hM v

/-- **Atypical pairs** (paper §6.3, proof of Lemma B(2)): for `y ≠ x` and `y ≠ E ∖ x`,
`Pr(S_x = S_y = a, S_E = s) ≤ M⁻³`. If exactly one of `A, B` is empty the pair is impossible;
otherwise two factors are at most `1/M` and `Σ_c Pr(S_C = c) Pr(S_D = c − u) ≤ 1/M`. -/
theorem pairP_le_inv3 (hM : 0 < M) {x y : Finset (Fin m)} (h1 : x ≠ y) (h2 : y ≠ xᶜ) (a s : ℤ) :
    pairP M m x y a s ≤ 1 / (M : ℝ) ^ 3 := by
  rw [pairP_eq hM]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hAB : 1 ≤ (x \ y).card ∨ 1 ≤ (y \ x).card := by
    by_contra h
    push Not at h
    have e1 : x \ y = ∅ := card_eq_zero.mp (by omega)
    have e2 : y \ x = ∅ := card_eq_zero.mp (by omega)
    exact h1 (Subset.antisymm (sdiff_eq_empty_iff_subset.mp e1) (sdiff_eq_empty_iff_subset.mp e2))
  have hCD : 1 ≤ (x ∩ y).card ∨ 1 ≤ (x ∪ y)ᶜ.card := by
    by_contra h
    push Not at h
    have e1 : x ∩ y = ∅ := card_eq_zero.mp (by omega)
    have e2 : (x ∪ y)ᶜ = ∅ := card_eq_zero.mp (by omega)
    apply h2; ext i
    have h3 : i ∉ x ∩ y := by rw [e1]; simp
    have h4 : i ∉ (x ∪ y)ᶜ := by rw [e2]; simp
    simp only [mem_inter, mem_compl, mem_union, not_and, not_not] at h3 h4 ⊢
    tauto
  set α := (x \ y).card; set β := (y \ x).card; set γ := (x ∩ y).card; set δ := (x ∪ y)ᶜ.card
  have hzero : ∀ {k l : ℕ}, k = 0 → 1 ≤ l → ∀ v : ℤ, lawS M k v * lawS M l v = 0 := by
    intro k l hk hl v
    by_cases hv : v = 0
    · obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
      rw [hv, lawS_succ_zero]; ring
    · rw [hk, lawS_zero_ne hv]; ring
  by_cases hα : α = 0
  · have hβ : 1 ≤ β := by omega
    rw [sum_eq_zero fun c _ => by rw [mul_assoc (lawS M γ c), hzero hα hβ]; ring]
    positivity
  by_cases hβ : β = 0
  · have hα1 : 1 ≤ α := by omega
    rw [sum_eq_zero fun c _ => by
      rw [mul_assoc (lawS M γ c), mul_comm (lawS M α _), hzero hβ hα1]; ring]
    positivity
  have hα1 : 1 ≤ α := by omega
  have hβ1 : 1 ≤ β := by omega
  have hinj : Function.Injective fun c : ℤ => s - 2 * a + c := fun c d h => by simp only at h; omega
  have hCDs : ∑ c ∈ I0 m M, lawS M γ c * lawS M δ (s - 2 * a + c) ≤ 1 / M := by
    rcases hCD with hγ | hδ
    · calc ∑ c ∈ I0 m M, lawS M γ c * lawS M δ (s - 2 * a + c)
          ≤ ∑ c ∈ I0 m M, 1 / (M : ℝ) * lawS M δ (s - 2 * a + c) :=
            sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (lawS_le_inv' hM hγ c) (lawS_nonneg _ _ _)
        _ = 1 / M * ∑ c ∈ I0 m M, lawS M δ (s - 2 * a + c) := by rw [mul_sum]
        _ ≤ 1 / M * 1 := mul_le_mul_of_nonneg_left
            (sum_lawS_le (f := fun c => s - 2 * a + c) hM δ _ hinj) (by positivity)
        _ = 1 / M := mul_one _
    · calc ∑ c ∈ I0 m M, lawS M γ c * lawS M δ (s - 2 * a + c)
          ≤ ∑ c ∈ I0 m M, lawS M γ c * (1 / (M : ℝ)) :=
            sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (lawS_le_inv' hM hδ _) (lawS_nonneg _ _ _)
        _ = (∑ c ∈ I0 m M, lawS M γ (id c)) * (1 / M) := by rw [sum_mul]; rfl
        _ ≤ 1 * (1 / M) := mul_le_mul_of_nonneg_right
            (sum_lawS_le hM γ _ Function.injective_id) (by positivity)
        _ = 1 / M := one_mul _
  calc ∑ c ∈ I0 m M, lawS M γ c * lawS M α (a - c) * lawS M β (a - c) * lawS M δ (s - 2 * a + c)
      ≤ ∑ c ∈ I0 m M, (1 / (M : ℝ)) ^ 2 * (lawS M γ c * lawS M δ (s - 2 * a + c)) := by
        refine sum_le_sum fun c _ => ?_
        have e1 := lawS_le_inv' hM hα1 (a - c)
        have e2 := lawS_le_inv' hM hβ1 (a - c)
        have p2 := lawS_nonneg M β (a - c)
        have p3 := mul_nonneg (lawS_nonneg M γ c) (lawS_nonneg M δ (s - 2 * a + c))
        have : lawS M α (a - c) * lawS M β (a - c) ≤ (1 / (M : ℝ)) ^ 2 := by
          rw [sq]; exact mul_le_mul e1 e2 p2 (by positivity)
        calc lawS M γ c * lawS M α (a - c) * lawS M β (a - c) * lawS M δ (s - 2 * a + c)
            = (lawS M α (a - c) * lawS M β (a - c)) * (lawS M γ c * lawS M δ (s - 2 * a + c)) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right this p3
    _ = (1 / (M : ℝ)) ^ 2 * ∑ c ∈ I0 m M, lawS M γ c * lawS M δ (s - 2 * a + c) := by rw [mul_sum]
    _ ≤ (1 / (M : ℝ)) ^ 2 * (1 / M) := mul_le_mul_of_nonneg_left hCDs (by positivity)
    _ = 1 / (M : ℝ) ^ 3 := by field_simp

/-- The four class sizes add up to `m`. -/
theorem card_four (x y : Finset (Fin m)) :
    (x \ y).card + (y \ x).card + (x ∩ y).card + (x ∪ y)ᶜ.card = m ∧
      (x \ y).card + (x ∩ y).card = x.card ∧ (y \ x).card + (x ∩ y).card = y.card := by
  have h1 := card_sdiff_add_card_inter x y
  have h2 := card_sdiff_add_card_inter y x
  have h3 := card_union_add_card_inter x y
  have h4 := card_compl_add_card (x ∪ y)
  rw [inter_comm y x] at h2
  simp only [Fintype.card_fin] at h4
  refine ⟨by omega, h1, h2⟩

end ArcsAlgo.LLT
