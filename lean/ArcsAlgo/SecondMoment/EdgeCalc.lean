module

public import ArcsAlgo.SecondMoment.BREdge
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false

/-!
# Derivatives along lists of directions; moments and cumulants of a finite law

`DL l f` (derivatives along a list), `DL_perm` (they commute, for smooth `f`), `Dα_eq_DL`, the Leibniz
rule `DL_mul` over the splittings of the list, the moments of exponential sums `DL_expS`, and the
moment–cumulant recursion `mom_cum`: `μ(j :: l) = Σ μ(l₁) κ(j :: l₂)` over the splittings of `l`.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {d : ℕ}

/-- Smooth functions on `ℝ^d`. -/
abbrev Sm (f : (Fin d → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

theorem Sm.differentiable {f : (Fin d → ℝ) → ℝ} (hf : Sm f) : Differentiable ℝ f :=
  ContDiff.differentiable hf (by simp)

theorem Sm.pD {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (j : Fin d) : Sm (pD j f) := by
  unfold ArcsAlgo.LLT.pD
  have h : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact h.clm_apply contDiff_const

/-- Derivatives along a list of directions, the head applied first. -/
noncomputable def DL : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], f => f
  | j :: l, f => DL l (pD j f)

@[simp] theorem DL_nil (f : (Fin d → ℝ) → ℝ) : DL [] f = f := rfl
@[simp] theorem DL_cons (j : Fin d) (l : List (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    DL (j :: l) f = DL l (pD j f) := rfl

theorem DL_append (l₁ l₂ : List (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    DL (l₁ ++ l₂) f = DL l₂ (DL l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons j l ih => simp [ih]

theorem Sm.DL {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (l : List (Fin d)) : Sm (DL l f) := by
  induction l generalizing f with
  | nil => exact hf
  | cons j l ih => exact ih (hf.pD j)

/-- Partial derivatives of a `C²` function commute. -/
theorem pD_comm {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (i j : Fin d) : pD i (pD j f) = pD j (pD i f) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have e : ∀ (a b : Fin d), pD a (pD b f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    unfold ArcsAlgo.LLT.pD
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [e, e]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Derivatives along a list depend only on the multiset of directions. -/
theorem DL_perm {l l' : List (Fin d)} (h : l.Perm l') {f : (Fin d → ℝ) → ℝ} (hf : Sm f) :
    DL l f = DL l' f := by
  induction h generalizing f with
  | nil => rfl
  | cons j _ ih => exact ih (hf.pD j)
  | swap i j l => simp only [DL_cons]; rw [pD_comm hf]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

/-- The list of directions of a multi-index, in the order in which `Dα` applies them. -/
def alist (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).reverse.flatMap fun j => List.replicate (α j) j

theorem iterate_pD_eq (j : Fin d) (n : ℕ) (f : (Fin d → ℝ) → ℝ) :
    (pD j)^[n] f = DL (List.replicate n j) f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, List.replicate_succ]; rfl

theorem foldr_pD_eq (α : Fin d → ℕ) (L : List (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    L.foldr (fun j g => (pD j)^[α j] g) f = DL (L.reverse.flatMap fun j => List.replicate (α j) j) f := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    rw [List.foldr_cons, ih, iterate_pD_eq, List.reverse_cons, List.flatMap_append, DL_append]
    simp

theorem Dα_eq_DL (α : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) : Dα α f = DL (alist α) f :=
  foldr_pD_eq α _ f

/-! ### Linearity and the Leibniz rule -/

theorem pD_add {f g : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin d) :
    pD j (fun x => f x + g x) = fun x => pD j f x + pD j g x := by
  funext x; unfold ArcsAlgo.LLT.pD
  rw [fderiv_fun_add (hf x) (hg x)]; rfl

theorem pD_mul {f g : (Fin d → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin d) :
    pD j (fun x => f x * g x) = fun x => pD j f x * g x + f x * pD j g x := by
  funext x; unfold ArcsAlgo.LLT.pD
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem DL_add {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (l : List (Fin d)) :
    DL l (fun x => f x + g x) = fun x => DL l f x + DL l g x := by
  induction l generalizing f g with
  | nil => rfl
  | cons j l ih =>
    simp only [DL_cons]
    rw [pD_add hf.differentiable hg.differentiable, ih (hf.pD j) (hg.pD j)]

/-- The splittings of a list into two complementary sublists (order kept). -/
def splits : List (Fin d) → List (List (Fin d) × List (Fin d))
  | [] => [([], [])]
  | j :: l => (splits l).map (fun q => (j :: q.1, q.2)) ++ (splits l).map (fun q => (q.1, j :: q.2))

/-- **The Leibniz rule along a list.** -/
theorem DL_mul {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (l : List (Fin d)) (x : Fin d → ℝ) :
    DL l (fun x => f x * g x) x = ((splits l).map fun q => DL q.1 f x * DL q.2 g x).sum := by
  induction l generalizing f g with
  | nil => simp [splits]
  | cons j l ih =>
    simp only [DL_cons, splits, List.map_append, List.map_map, List.sum_append]
    rw [pD_mul hf.differentiable hg.differentiable,
      DL_add ((hf.pD j).mul hg) (hf.mul (hg.pD j))]
    beta_reduce
    rw [ih (hf.pD j) hg, ih hf (hg.pD j)]
    rfl

/-! ### Exponential sums and their logarithm -/

/-- `G(t) = Σ_a c_a e^{⟨t, v_a⟩}`. -/
noncomputable def expS {Ω : Type} [Fintype Ω] (c : Ω → ℝ) (v : Ω → Fin d → ℝ) (t : Fin d → ℝ) : ℝ :=
  ∑ a, c a * Real.exp (∑ j, t j * v a j)

theorem expS_smooth {Ω : Type} [Fintype Ω] (c : Ω → ℝ) (v : Ω → Fin d → ℝ) : Sm (expS c v) := by
  show ContDiff ℝ (⊤ : ℕ∞) _
  unfold expS
  refine ContDiff.sum fun a _ => contDiff_const.mul (Real.contDiff_exp.comp ?_)
  exact ContDiff.sum fun k _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) k).mul contDiff_const

theorem pD_expS {Ω : Type} [Fintype Ω] (c : Ω → ℝ) (v : Ω → Fin d → ℝ) (j : Fin d) :
    pD j (expS c v) = expS (fun a => c a * v a j) v := by
  funext x
  have hL : ∀ a, HasFDerivAt (fun t : Fin d → ℝ => ∑ k, t k * v a k)
      (∑ k, v a k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x := by
    intro a
    have : (fun t : Fin d → ℝ => ∑ k, t k * v a k) =
        (∑ k, v a k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) := by
      funext t; simp [mul_comm]
    rw [this]; exact ContinuousLinearMap.hasFDerivAt _
  have hG : HasFDerivAt (expS c v) (∑ a, c a • (Real.exp (∑ k, x k * v a k) •
      (∑ k, v a k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k))) x := by
    unfold expS
    exact HasFDerivAt.fun_sum fun a _ => ((hL a).exp).const_mul (c a)
  unfold ArcsAlgo.LLT.pD
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, expS]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [show (∑ k, x k * v a k) = ∑ k, v a k * x k from Finset.sum_congr rfl fun k _ => mul_comm _ _]
  ring

/-- **Moments**: `D_l G = Σ_a c_a (Π_{i ∈ l} v_{a,i}) e^{⟨t, v_a⟩}`. -/
theorem DL_expS {Ω : Type} [Fintype Ω] (c : Ω → ℝ) (v : Ω → Fin d → ℝ) (l : List (Fin d)) :
    DL l (expS c v) = expS (fun a => c a * (l.map (v a)).prod) v := by
  induction l generalizing c with
  | nil => simp
  | cons j l ih =>
    rw [DL_cons, pD_expS, ih]
    congr 1; funext a; simp [mul_assoc]

theorem expS_zero {Ω : Type} [Fintype Ω] (c : Ω → ℝ) (v : Ω → Fin d → ℝ) :
    expS c v 0 = ∑ a, c a := by simp [expS]

/-! ### Moments and cumulants of a finite law -/

section Law

variable {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ)

/-- The moment `E Π_{i ∈ l} X_i`. -/
noncomputable def momL (l : List (Fin d)) : ℝ := ∑ a, p a * (l.map fun i => (ξ a i : ℝ)).prod

/-- The cumulant along a list, `D_l log E e^{⟨t, X⟩}|_{t=0}`. -/
noncomputable def cumL (l : List (Fin d)) : ℝ := DL l (cgf p ξ) 0

theorem cgf_eq : cgf p ξ = fun t => Real.log (expS p (fun a j => (ξ a j : ℝ)) t) := rfl

variable {p}

theorem expS_pos (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (t : Fin d → ℝ) :
    0 < expS p (fun a j => (ξ a j : ℝ)) t := by
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < p a := by
    by_contra h; simp only [not_exists, not_lt] at h
    have : ∑ a, p a ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith
  unfold expS
  exact Finset.sum_pos' (fun a _ => mul_nonneg (hp a) (Real.exp_pos _).le)
    ⟨a₀, Finset.mem_univ _, mul_pos ha₀ (Real.exp_pos _)⟩

theorem cgf_smooth (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) : Sm (cgf p ξ) := by
  rw [cgf_eq]
  exact (expS_smooth p _).log fun t => (expS_pos ξ hp hs t).ne'

theorem pD_cgf (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (j : Fin d) :
    pD j (expS p (fun a j => (ξ a j : ℝ))) =
      fun t => expS p (fun a j => (ξ a j : ℝ)) t * pD j (cgf p ξ) t := by
  funext t
  set G := expS p (fun a j => (ξ a j : ℝ))
  have hG : HasFDerivAt G (fderiv ℝ G t) t := ((expS_smooth p _).differentiable t).hasFDerivAt
  have hL := hG.log (expS_pos ξ hp hs t).ne'
  unfold ArcsAlgo.LLT.pD
  rw [cgf_eq, hL.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hG0 : G t ≠ 0 := (expS_pos ξ hp hs t).ne'
  field_simp


theorem momL_eq (l : List (Fin d)) : momL p ξ l = DL l (expS p (fun a j => (ξ a j : ℝ))) 0 := by
  rw [DL_expS, expS_zero]
  unfold momL; rfl

/-- **The moment–cumulant recursion**: `μ(j :: l) = Σ_{(l₁, l₂) splitting l} μ(l₁) κ(j :: l₂)`. -/
theorem mom_cum (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (j : Fin d) (l : List (Fin d)) :
    momL p ξ (j :: l) = ((splits l).map fun q => momL p ξ q.1 * cumL p ξ (j :: q.2)).sum := by
  rw [momL_eq, DL_cons, pD_cgf ξ hp hs,
    DL_mul (expS_smooth p _) ((cgf_smooth ξ hp hs).pD j)]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  rw [momL_eq]; rfl

theorem cumL_perm (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) {l l' : List (Fin d)} (h : l.Perm l') :
    cumL p ξ l = cumL p ξ l' := by
  unfold cumL; rw [DL_perm h (cgf_smooth ξ hp hs)]

theorem cumul_eq (α : Fin d → ℕ) : cumul p ξ α = cumL p ξ (alist α) := by
  unfold cumul cumL; rw [Dα_eq_DL]

theorem momL_nil (hs : ∑ a, p a = 1) : momL p ξ [] = 1 := by simp [momL, hs]

end Law

end ArcsAlgo.LLT
