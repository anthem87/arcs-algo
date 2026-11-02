module

public import ArcsAlgo.LocalLimit.Fourier
set_option autoImplicit false

/-!
# Independence of the sums over disjoint index sets (paper §6.3)

For weights uniform in `{1, …, M}^m`, `prW` is the probability of an event. Events that depend
on disjoint sets of weights are independent (`prW_and`), and the law of `S_J = Σ_{i∈J} w_i`
depends only on `|J|` (`prW_SJ`): `Pr(S_J = v) = Pr(S_{|J|} = v)`.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- The probability of an event for weights uniform in `{1, …, M}^m`. -/
noncomputable def prW (M m : ℕ) (E : (Fin m → Fin M) → Prop) [DecidablePred E] : ℝ :=
  (∑ w, if E w then (1 : ℝ) else 0) / (M : ℝ) ^ m

/-- `E` depends only on the weights indexed by `J`. -/
def DependsOn (J : Finset (Fin m)) (E : (Fin m → Fin M) → Prop) : Prop :=
  ∀ w w' : Fin m → Fin M, (∀ i ∈ J, w i = w' i) → (E w ↔ E w')

/-- `S_J = Σ_{i ∈ J} w_i`. -/
def SJ (J : Finset (Fin m)) (w : Fin m → Fin M) : ℤ := ∑ i ∈ J, ((w i : ℤ) + 1)

theorem dependsOn_SJ (J : Finset (Fin m)) (P : ℤ → Prop) :
    DependsOn (M := M) J (fun w => P (SJ J w)) := by
  intro w w' h
  have : SJ J w = SJ J w' := sum_congr rfl fun i hi => by rw [h i hi]
  show P (SJ J w) ↔ P (SJ J w'); rw [this]

private noncomputable def eJ (J : Finset (Fin m)) (M : ℕ) :
    (Fin m → Fin M) ≃ (({i // i ∈ J} → Fin M) × ({i // i ∉ J} → Fin M)) :=
  Equiv.piEquivPiSubtypeProd (· ∈ J) (fun _ => Fin M)

private theorem card_split (J : Finset (Fin m)) :
    (Fintype.card ({i // i ∈ J} → Fin M) : ℝ) * Fintype.card ({i // i ∉ J} → Fin M) =
      (M : ℝ) ^ m := by
  have := Fintype.card_congr (eJ J M)
  rw [Fintype.card_prod] at this
  simp only [Fintype.card_fun, Fintype.card_fin] at this ⊢
  exact_mod_cast this.symm

/-- **Independence** of events depending on disjoint sets of weights. -/
theorem prW_and (hM : 0 < M) {J K : Finset (Fin m)} (hJK : Disjoint J K)
    (E₁ E₂ : (Fin m → Fin M) → Prop) [DecidablePred E₁] [DecidablePred E₂]
    (h1 : DependsOn J E₁) (h2 : DependsOn K E₂) :
    prW M m (fun w => E₁ w ∧ E₂ w) = prW M m E₁ * prW M m E₂ := by
  set e := eJ J M
  let z : Fin M := ⟨0, hM⟩
  let A : ({i // i ∈ J} → Fin M) → Prop := fun f => E₁ (e.symm (f, fun _ => z))
  let B : ({i // i ∉ J} → Fin M) → Prop := fun g => E₂ (e.symm (fun _ => z, g))
  have hA : ∀ f g, E₁ (e.symm (f, g)) ↔ A f := fun f g => h1 _ _ fun i hi => by
    simp [e, eJ, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hB : ∀ f g, E₂ (e.symm (f, g)) ↔ B g := fun f g => h2 _ _ fun i hi => by
    have : i ∉ J := fun h => Finset.disjoint_left.mp hJK h hi
    simp [e, eJ, Equiv.piEquivPiSubtypeProd_symm_apply, this]
  classical
  have s12 : ∑ w, (if E₁ w ∧ E₂ w then (1 : ℝ) else 0) =
      (∑ f, if A f then (1 : ℝ) else 0) * ∑ g, if B g then (1 : ℝ) else 0 := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, sum_mul_sum]
    refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => ?_
    simp only [hA f g, hB f g]; split_ifs <;> simp_all
  have s1 : ∑ w, (if E₁ w then (1 : ℝ) else 0) =
      (∑ f, if A f then (1 : ℝ) else 0) * Fintype.card ({i // i ∉ J} → Fin M) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun f _ => ?_
    simp only [hA f]; simp
  have s2 : ∑ w, (if E₂ w then (1 : ℝ) else 0) =
      Fintype.card ({i // i ∈ J} → Fin M) * ∑ g, if B g then (1 : ℝ) else 0 := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hB]
    rw [sum_const, card_univ, nsmul_eq_mul]
  have hc := card_split (M := M) J
  have hMm : (M : ℝ) ^ m ≠ 0 := by positivity
  unfold prW
  rw [s12, s1, s2, ← hc]
  have h3 : (Fintype.card ({i // i ∈ J} → Fin M) : ℝ) ≠ 0 := by
    have : Nonempty ({i // i ∈ J} → Fin M) := ⟨fun _ => z⟩
    exact_mod_cast Fintype.card_pos.ne'
  have h4 : (Fintype.card ({i // i ∉ J} → Fin M) : ℝ) ≠ 0 := by
    have : Nonempty ({i // i ∉ J} → Fin M) := ⟨fun _ => z⟩
    exact_mod_cast Fintype.card_pos.ne'
  field_simp

/-- The law of `S_J` depends only on `|J|`: `Pr(S_J = v) = Pr(S_{|J|} = v)`. -/
theorem prW_SJ (hM : 0 < M) (J : Finset (Fin m)) (v : ℤ) :
    prW M m (fun w => SJ J w = v) = lawS M J.card v := by
  classical
  set e := eJ J M
  let z : Fin M := ⟨0, hM⟩
  have hS : ∀ f g, SJ J (e.symm (f, g)) = ∑ i : {i // i ∈ J}, ((f i : ℤ) + 1) := by
    intro f g
    unfold SJ
    rw [← sum_coe_sort J]
    refine Fintype.sum_congr _ _ fun i => ?_
    simp [e, eJ, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  have s1 : ∑ w : Fin m → Fin M, (if SJ J w = v then (1 : ℝ) else 0) =
      (∑ f : {i // i ∈ J} → Fin M, if ∑ i, ((f i : ℤ) + 1) = v then (1 : ℝ) else 0) *
        Fintype.card ({i // i ∉ J} → Fin M) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun f _ => ?_
    simp only [hS]; simp [mul_comm]
  set σ := J.equivFin
  have s2 : (∑ f : {i // i ∈ J} → Fin M, if ∑ i, ((f i : ℤ) + 1) = v then (1 : ℝ) else 0) =
      ∑ w' : Fin J.card → Fin M, if ∑ t, ((w' t : ℤ) + 1) = v then (1 : ℝ) else 0 := by
    refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ fun f => ?_
    have : ∑ t, (((Equiv.arrowCongr σ (Equiv.refl _) f) t : ℤ) + 1) = ∑ i, ((f i : ℤ) + 1) := by
      rw [← σ.sum_comp]; simp [Equiv.arrowCongr_apply]
    rw [this]
  have hc := card_split (M := M) J
  have h4 : (Fintype.card ({i // i ∉ J} → Fin M) : ℝ) ≠ 0 := by
    have : Nonempty ({i // i ∉ J} → Fin M) := ⟨fun _ => z⟩
    exact_mod_cast Fintype.card_pos.ne'
  have hF : (Fintype.card ({i // i ∈ J} → Fin M) : ℝ) = (M : ℝ) ^ J.card := by
    simp [Fintype.card_fun]
  unfold prW lawS
  rw [s1, s2, ← hc, hF, card_filter]
  push_cast
  field_simp

end ArcsAlgo.LLT
