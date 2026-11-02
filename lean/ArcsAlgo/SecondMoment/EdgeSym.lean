module

public import ArcsAlgo.SecondMoment.EdgeExpand
set_option autoImplicit false

/-!
# Symmetric laws have vanishing odd cumulants

`cumL_refl_zero`: if a bijection of the parameter space preserves the law and flips the sign of the
`i`-th coordinate, every cumulant with an odd number of `i`'s vanishes.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {d : ℕ}

/-- The reflection of the `i`-th coordinate. -/
noncomputable def reflC (i : Fin d) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun j => if j = i then -ContinuousLinearMap.proj j else ContinuousLinearMap.proj j

theorem reflC_apply (i : Fin d) (t : Fin d → ℝ) (j : Fin d) :
    reflC i t j = if j = i then -t j else t j := by
  unfold reflC; by_cases h : j = i <;> simp [h]

theorem reflC_single (i j : Fin d) :
    reflC i (Pi.single j 1) = (if j = i then (-1 : ℝ) else 1) • Pi.single j 1 := by
  funext k
  rw [reflC_apply]
  by_cases hk : k = j
  · subst hk; split_ifs <;> simp_all
  · simp [Pi.single_apply, hk]

theorem reflC_zero (i : Fin d) : reflC i 0 = 0 := map_zero _

theorem pD_comp_refl {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i j : Fin d) :
    pD j (fun t => f (reflC i t)) = fun t => (if j = i then (-1 : ℝ) else 1) * pD j f (reflC i t) := by
  funext t
  unfold ArcsAlgo.LLT.pD
  have h := ((hf.differentiable) (reflC i t)).hasFDerivAt.comp t (reflC i).hasFDerivAt
  rw [show (fun t => f (reflC i t)) = f ∘ reflC i from rfl, h.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, reflC_single, map_smul, smul_eq_mul]

theorem DL_comp_refl {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i : Fin d) (l : List (Fin d)) :
    DL l (fun t => f (reflC i t)) = fun t => (-1 : ℝ) ^ (l.count i) * DL l f (reflC i t) := by
  induction l generalizing f with
  | nil => funext t; simp
  | cons j l ih =>
    rw [DL_cons, pD_comp_refl hf]
    by_cases hj : j = i
    · subst hj
      simp only [if_true]
      have := DL_const_mul (f := fun t => pD j f (reflC j t)) ((hf.pD j).comp (reflC j).contDiff) (-1) l
      rw [this, ih (hf.pD j)]
      funext t; rw [List.count_cons_self, pow_succ]; simp only [DL_cons]; ring
    · simp only [if_neg hj, one_mul]
      rw [ih (hf.pD j)]
      funext t; rw [List.count_cons_of_ne hj]; rfl

/-- **Symmetric laws**: if a bijection of `Ω` preserves `p` and flips the sign of the `i`-th
coordinate of `ξ`, every cumulant with an odd number of `i`'s vanishes. -/
theorem cumL_refl_zero {Ω : Type} [Fintype Ω] {p : Ω → ℝ} {ξ : Ω → Fin d → ℤ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (i : Fin d) (σ : Ω ≃ Ω) (hσp : ∀ a, p (σ a) = p a)
    (hσξ : ∀ a j, ξ (σ a) j = if j = i then -ξ a j else ξ a j) (l : List (Fin d))
    (hl : Odd (l.count i)) : cumL p ξ l = 0 := by
  have hsym : (fun t => cgf p ξ (reflC i t)) = cgf p ξ := by
    funext t
    unfold cgf
    congr 1
    rw [← σ.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσp]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [reflC_apply, hσξ]
    split_ifs <;> push_cast <;> ring
  have h := congrFun (DL_comp_refl (cgf_smooth ξ hp hs) i l) 0
  rw [hsym, reflC_zero, hl.neg_one_pow] at h
  unfold cumL
  linarith

end ArcsAlgo.LLT
