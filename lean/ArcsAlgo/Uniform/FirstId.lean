module

public import ArcsAlgo.SecondMoment.LemmaB
public import ArcsAlgo.Uniform.Indep
set_option autoImplicit false

/-!
# The first moment as a sum over the size of the subset (paper §6.3, Lemma B(1))

`sumZ_eq`: with `2a = s + u`,
`Σ_{S_E = s} Z(u) / M^m = Σ_k C(m,k) Pr(S_k = a) Pr(S_{m−k} = s − a)`,
so `λ · Pr(S_E = s) = Σ_k C(m,k) Pr(S_k = a) Pr(S_{m−k} = s − a)`.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- Sign vectors are subsets: `ε ↦ {i : ε_i = +1}`. -/
def signEquiv (m : ℕ) : (Fin m → Bool) ≃ Finset (Fin m) where
  toFun ε := univ.filter fun i => ε i = true
  invFun P i := decide (i ∈ P)
  left_inv ε := by funext i; simp
  right_inv P := by ext i; simp

theorem Sw_eq (w : Fin m → Fin M) (P : Finset (Fin m)) : Sw w = SJ P w + SJ Pᶜ w := by
  unfold Sw SJ; rw [sum_add_sum_compl]

theorem Tsg_eq (w : Fin m → Fin M) (ε : Fin m → Bool) :
    Tsg w ε = SJ (signEquiv m ε) w - SJ (signEquiv m ε)ᶜ w := by
  unfold Tsg SJ signEquiv
  simp only [Equiv.coe_fn_mk]
  rw [← sum_filter_add_sum_filter_not univ (fun i => ε i = true), compl_filter]
  have h1 : ∑ x ∈ univ.filter (fun i => ε i = true), sg (ε x) * ((w x : ℤ) + 1) =
      ∑ x ∈ univ.filter (fun i => ε i = true), ((w x : ℤ) + 1) :=
    sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]; simp [sg]
  have h2 : ∑ x ∈ univ.filter (fun i => ¬ ε i = true), sg (ε x) * ((w x : ℤ) + 1) =
      -∑ x ∈ univ.filter (fun i => ¬ ε i = true), ((w x : ℤ) + 1) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x hx => by
      have := (mem_filter.mp hx).2; simp at this; simp [sg, this]
  rw [h1, h2]; ring

/-- **The first moment as a sum over the size of `x`** (paper §6.3, proof of Lemma B(1)):
`Σ_{S_E = s} Z(u) / M^m = Σ_k C(m,k) Pr(S_k = a) Pr(S_{m−k} = s − a)`, `2a = s + u`. -/
theorem sumZ_eq (hM : 0 < M) (s u a : ℤ) (ha : 2 * a = s + u) :
    (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ)) / (M : ℝ) ^ m =
      ∑ k ∈ range (m + 1), (m.choose k : ℝ) * (lawS M k a * lawS M (m - k) (s - a)) := by
  have h1 : ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) =
      ∑ ε : Fin m → Bool, ∑ w : Fin m → Fin M,
        (if SJ (signEquiv m ε) w = a ∧ SJ (signEquiv m ε)ᶜ w = s - a then (1 : ℝ) else 0) := by
    rw [sum_filter, sum_comm]
    refine sum_congr rfl fun w _ => ?_
    unfold Zc
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    split_ifs with hs
    · refine sum_congr rfl fun ε _ => ?_
      have e1 := Sw_eq w (signEquiv m ε)
      have e2 := Tsg_eq w ε
      by_cases h : Tsg w ε = u
      · rw [if_pos h, if_pos ⟨by omega, by omega⟩]; simp
      · rw [if_neg h, if_neg]; push_cast; omega
    · symm; refine sum_eq_zero fun ε _ => ?_
      have e1 := Sw_eq w (signEquiv m ε)
      rw [if_neg]; omega
  rw [h1, sum_div]
  have h2 : ∀ ε : Fin m → Bool, (∑ w : Fin m → Fin M,
      (if SJ (signEquiv m ε) w = a ∧ SJ (signEquiv m ε)ᶜ w = s - a then (1 : ℝ) else 0)) /
        (M : ℝ) ^ m = lawS M (signEquiv m ε).card a * lawS M (m - (signEquiv m ε).card) (s - a) := by
    intro ε
    have := prW_and hM (disjoint_compl_right (a := signEquiv m ε)) _ _
      (dependsOn_SJ (signEquiv m ε) (· = a)) (dependsOn_SJ (signEquiv m ε)ᶜ (· = s - a))
    unfold prW at this
    rw [this]
    have h3 := prW_SJ hM (signEquiv m ε) a
    have h4 := prW_SJ hM (signEquiv m ε)ᶜ (s - a)
    unfold prW at h3 h4
    rw [h3, h4, card_compl, Fintype.card_fin]
  simp only [h2]
  rw [← (signEquiv m).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  have := sum_powerset_apply_card (fun k => lawS M k a * lawS M (m - k) (s - a)) (x := (univ : Finset (Fin m)))
  rw [← powerset_univ, this, card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

end ArcsAlgo.LLT
