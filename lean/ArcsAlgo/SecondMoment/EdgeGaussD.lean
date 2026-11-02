module

public import ArcsAlgo.SecondMoment.EdgeCalc
public import ArcsAlgo.SecondMoment.Vectors
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Analysis.Calculus.Deriv.CompMul
set_option autoImplicit false

/-!
# Derivatives of the diagonal Gaussian

`DL_prodF`: `D_l Π_k h_k(x_k) = Π_k h_k^{(#k in l)}(x_k)`; `gaussDens_diag_prod`: for a diagonal covariance
the Gaussian density is a product of one-dimensional ones; `iter_deriv_gauss1`:
`g_D^{(n)}(t) = (−1)^n D^{−n/2} He_n(t/√D) g_D(t)` (from Mathlib's `deriv_gaussian_eq_hermite_mul_gaussian`).
-/

open Finset Matrix Polynomial

@[expose] public section

namespace ArcsAlgo.LLT

variable {d : ℕ}

/-- `x ↦ Π_k h_k(x_k)`. -/
noncomputable def prodF (h : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : ℝ := ∏ k, h k (x k)

theorem pD_prodF {h : Fin d → ℝ → ℝ} (hh : ∀ k, Differentiable ℝ (h k)) (j : Fin d) :
    pD j (prodF h) = prodF (Function.update h j (deriv (h j))) := by
  funext x
  have hg : ∀ k ∈ (univ : Finset (Fin d)), HasFDerivAt (fun y : Fin d → ℝ => h k (y k))
      (deriv (h k) (x k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x := by
    intro k _
    have h1 := ((hh k) (x k)).hasDerivAt.hasFDerivAt
    have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).hasFDerivAt (x := x)
    refine (h1.comp x h2).congr_fderiv ?_
    ext v; simp [mul_comm]
  unfold ArcsAlgo.LLT.pD prodF
  rw [(HasFDerivAt.finsetProd hg).fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- **Derivatives of a product of coordinate functions**: `D_l Π_k h_k(x_k) = Π_k h_k^{(#k in l)}(x_k)`. -/
theorem DL_prodF {h : Fin d → ℝ → ℝ} (hh : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (h k)) (l : List (Fin d)) :
    DL l (prodF h) = prodF (fun k => deriv^[l.count k] (h k)) := by
  induction l generalizing h with
  | nil => rfl
  | cons j l ih =>
    rw [DL_cons, pD_prodF (fun k => (hh k).differentiable (by simp))]
    have hh' : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Function.update h j (deriv (h j)) k) := by
      intro k
      by_cases hk : k = j
      · subst hk; simp only [Function.update_self]
        exact (contDiff_infty_iff_deriv.mp (hh k)).2
      · rw [Function.update_of_ne hk]; exact hh k
    rw [ih hh']
    congr 1; funext k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self, List.count_cons_self]
      rw [Function.iterate_succ_apply]
    · rw [Function.update_of_ne hk, List.count_cons_of_ne (Ne.symm hk)]

/-- The one-dimensional centred Gaussian density of variance `D`. -/
noncomputable def gauss1 (D : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-((t / √D) ^ 2 / 2)) / (√(2 * Real.pi) * √D)

theorem gauss1_smooth (D : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gauss1 D) := by
  unfold gauss1; fun_prop

theorem gaussDens_diag_prod (D : Fin d → ℝ) (hD : ∀ i, 0 < D i) :
    gaussDens (diagonal D) = prodF (fun k => gauss1 (D k)) := by
  funext y
  rw [gaussDens_diag D hD]
  unfold prodF gauss1
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.sqrt_prod _ (fun i _ => (hD i).le)]
  congr 2
  rw [Finset.mul_sum]
  exact Fintype.sum_congr _ _ fun i => by rw [div_pow, Real.sq_sqrt (hD i).le]; ring

/-- `g_D^{(n)}(t) = (−1)^n D^{−n/2} He_n(t/√D) g_D(t)`. -/
theorem iter_deriv_gauss1 {D : ℝ} (hD : 0 < D) (n : ℕ) (t : ℝ) :
    deriv^[n] (gauss1 D) t =
      (-1) ^ n * (1 / √D) ^ n * aeval (t / √D) (hermite n) * gauss1 D t := by
  set a := 1 / √D
  have hga : gauss1 D = fun t => (1 / (√(2 * Real.pi) * √D)) * (fun y => Real.exp (-(y ^ 2 / 2))) (a * t) := by
    funext t; unfold gauss1; simp only [a]; rw [div_eq_inv_mul, one_div_mul_eq_div]
    rw [div_eq_mul_inv, mul_comm]; congr 3; field_simp
  have key : ∀ (n : ℕ) (f : ℝ → ℝ) (c : ℝ),
      deriv^[n] (fun t => c * f (a * t)) = fun t => c * a ^ n * deriv^[n] f (a * t) := by
    intro n
    induction n with
    | zero => intro f c; funext t; simp
    | succ n ih =>
      intro f c; funext t
      rw [Function.iterate_succ_apply', ih]
      rw [deriv_const_mul_field]
      rw [show (fun t => deriv^[n] f (a * t)) = (fun t => (deriv^[n] f) (a * t)) from rfl,
        deriv_comp_mul_left]
      rw [smul_eq_mul, Function.iterate_succ_apply']; ring
  have hk := congrFun (key n (fun y => Real.exp (-(y ^ 2 / 2))) (1 / (√(2 * Real.pi) * √D))) t
  rw [hga, hk, deriv_gaussian_eq_hermite_mul_gaussian]
  simp only [a]
  have : (1 / √D) * t = t / √D := by ring
  rw [this]
  ring

end ArcsAlgo.LLT
