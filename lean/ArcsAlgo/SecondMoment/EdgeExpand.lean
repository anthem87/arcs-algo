module

public import ArcsAlgo.SecondMoment.EdgeGaussD
set_option autoImplicit false

/-!
# The Edgeworth polynomials of [BR] for a diagonal covariance

`edgeP_diag`: for `V = diag(D)`, `P_r(−φ_V) = Σ_{compositions of r} (1/k!) evB(blocks, 0)`, where `evB`
applies the operators `χ_{j+2}(−D)/(j+2)!` to `T_0 = φ_V`, and `T_γ = D^γ φ_V`
= `Π_k (−1)^{γ_k} D_k^{−γ_k/2} He_{γ_k}(x_k/√D_k) · φ_V` (`Tg_eval`). `edgeP_odd`: if every cumulant of
odd order vanishes, `P_r = 0` for odd `r`.
-/

open Finset Matrix Polynomial

@[expose] public section

namespace ArcsAlgo.LLT

variable {d : ℕ}

/-! ### Linearity of `DL` -/

theorem DL_const_mul {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) (l : List (Fin d)) :
    DL l (fun x => c * f x) = fun x => c * DL l f x := by
  induction l generalizing f with
  | nil => rfl
  | cons j l ih =>
    simp only [DL_cons]
    have : pD j (fun x => c * f x) = fun x => c * pD j f x := by
      funext x; unfold ArcsAlgo.LLT.pD
      rw [fderiv_const_mul (hf.differentiable x)]; rfl
    rw [this, ih (hf.pD j)]

theorem DL_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin d → ℝ) → ℝ} (hF : ∀ i, Sm (F i))
    (l : List (Fin d)) : DL l (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, DL l (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext x; simp only [Finset.sum_empty]
    have : DL l (fun _ : Fin d → ℝ => (0 : ℝ)) = fun _ => 0 := by
      have h := DL_const_mul (f := fun _ : Fin d → ℝ => (1 : ℝ)) contDiff_const 0 l
      simpa using h
    rw [this]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : Sm (fun x => ∑ i ∈ s, F i x) := ContDiff.sum fun i _ => hF i
    rw [DL_add (hF a) hs, ih]

theorem count_alist (α : Fin d → ℕ) (k : Fin d) : (alist α).count k = α k := by
  unfold alist
  simp only [List.count_flatMap, List.map_reverse, List.sum_reverse]
  rw [← Fin.sum_univ_def]
  simp [List.count_replicate]

/-! ### Gaussian derivatives -/

/-- `T_β(x) = Π_k g_{D_k}^{(β_k)}(x_k) = D^β φ_D(x)`. -/
noncomputable def Tg (D : Fin d → ℝ) (β : Fin d → ℕ) : (Fin d → ℝ) → ℝ :=
  prodF (fun k => deriv^[β k] (gauss1 (D k)))

theorem Tg_smooth (D : Fin d → ℝ) (β : Fin d → ℕ) : Sm (Tg D β) := by
  unfold Tg prodF
  exact contDiff_prod fun k _ => ((gauss1_smooth _).iterate_deriv _).comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) k)

theorem DL_Tg (D : Fin d → ℝ) (β : Fin d → ℕ) (l : List (Fin d)) :
    DL l (Tg D β) = Tg D (fun k => β k + l.count k) := by
  unfold Tg
  rw [DL_prodF fun k => (gauss1_smooth _).iterate_deriv _]
  congr 1; funext k
  show _ = deriv^[β k + l.count k] _
  rw [← Function.iterate_add_apply, add_comm]

theorem Dα_Tg (D : Fin d → ℝ) (α β : Fin d → ℕ) : Dα α (Tg D β) = Tg D (β + α) := by
  rw [Dα_eq_DL, DL_Tg]
  congr 1; funext k; rw [count_alist]; rfl

theorem Tg_eval {D : Fin d → ℝ} (hD : ∀ i, 0 < D i) (γ : Fin d → ℕ) (x : Fin d → ℝ) :
    Tg D γ x = (∏ k, ((-1) ^ (γ k) * (1 / √(D k)) ^ (γ k) * aeval (x k / √(D k)) (hermite (γ k)))) *
      gaussDens (diagonal D) x := by
  rw [gaussDens_diag_prod D hD]
  unfold Tg prodF
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => iter_deriv_gauss1 (hD k) _ _

/-! ### The Edgeworth polynomials for a diagonal covariance -/

section Expand

variable {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (ξ : Ω → Fin d → ℤ) (D : Fin d → ℝ)

/-- The operators `χ_{j+2}(−D)/(j+2)!` of a list of blocks, applied to `T_β`. -/
noncomputable def evB : List ℕ → (Fin d → ℕ) → (Fin d → ℝ) → ℝ
  | [], β => Tg D β
  | j :: B, β => fun x => (1 / ((j + 2).factorial : ℝ)) *
      ∑ α ∈ Finset.Nat.antidiagonalTuple d (j + 2),
        (((j + 2).factorial : ℝ) / mfact α) * cumul p ξ α * (-1) ^ (j + 2) * evB B (β + α) x

theorem evB_smooth (B : List ℕ) (β : Fin d → ℕ) : Sm (evB p ξ D B β) := by
  induction B generalizing β with
  | nil => exact Tg_smooth D β
  | cons j B ih =>
    show ContDiff ℝ (⊤ : ℕ∞) fun x => _
    exact contDiff_const.mul (ContDiff.sum fun α _ => contDiff_const.mul (ih _))

theorem Dα_evB (α : Fin d → ℕ) (B : List ℕ) (β : Fin d → ℕ) :
    Dα α (evB p ξ D B β) = evB p ξ D B (β + α) := by
  induction B generalizing β with
  | nil => exact Dα_Tg D α β
  | cons j B ih =>
    rw [Dα_eq_DL]
    show DL (alist α) (fun x => (1 / ((j + 2).factorial : ℝ)) * ∑ α' ∈ Finset.Nat.antidiagonalTuple d (j + 2),
      (((j + 2).factorial : ℝ) / mfact α') * cumul p ξ α' * (-1) ^ (j + 2) * evB p ξ D B (β + α') x) = _
    rw [DL_const_mul (ContDiff.sum fun α' _ => contDiff_const.mul (evB_smooth p ξ D B _)),
      DL_sum _ (fun α' => contDiff_const.mul (evB_smooth p ξ D B _))]
    funext x
    show _ = (1 / ((j + 2).factorial : ℝ)) * ∑ α' ∈ Finset.Nat.antidiagonalTuple d (j + 2),
      (((j + 2).factorial : ℝ) / mfact α') * cumul p ξ α' * (-1) ^ (j + 2) * evB p ξ D B (β + α + α') x
    congr 1
    refine Finset.sum_congr rfl fun α' _ => ?_
    rw [DL_const_mul (evB_smooth p ξ D B _), ← Dα_eq_DL, ih, add_right_comm]

theorem foldr_eq_evB (B : List ℕ) (β : Fin d → ℕ) :
    B.foldr (fun j g => fun y => (1 / ((j + 2).factorial : ℝ)) * chiOp p ξ (j + 2) g y) (Tg D β) =
      evB p ξ D B β := by
  induction B generalizing β with
  | nil => rfl
  | cons j B ih =>
    rw [List.foldr_cons, ih]
    funext x
    unfold chiOp
    simp only [evB]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Dα_evB]

/-- **`P_r(−φ_V)` for a diagonal covariance**: `P_r = Σ_{compositions} (1/k!) evB(blocks, 0)`, where
`evB` applies the operators `χ_{j+2}(−D)/(j+2)!` to `φ_V = T_0`. -/
theorem edgeP_diag (hV : vcov p ξ = diagonal D) (hD : ∀ i, 0 < D i) (r : ℕ) (x : Fin d → ℝ) :
    edgeP p ξ r x = ∑ c : Composition r, (1 / (c.length.factorial : ℝ)) * evB p ξ D c.blocks 0 x := by
  unfold edgeP
  refine Finset.sum_congr rfl fun c _ => ?_
  have h0 : gaussDens (vcov p ξ) = Tg D 0 := by
    rw [hV, gaussDens_diag_prod D hD]; rfl
  rw [h0, foldr_eq_evB]

theorem evB_odd (hodd : ∀ α : Fin d → ℕ, Odd (∑ i, α i) → cumul p ξ α = 0) (B : List ℕ)
    (hB : ∃ j ∈ B, Odd j) (β : Fin d → ℕ) : evB p ξ D B β = 0 := by
  induction B generalizing β with
  | nil => obtain ⟨j, hj, _⟩ := hB; simp at hj
  | cons j B ih =>
    funext x
    simp only [evB, Pi.zero_apply]
    by_cases hj : Odd j
    · have : ∀ α ∈ Finset.Nat.antidiagonalTuple d (j + 2), cumul p ξ α = 0 := by
        intro α hα
        rw [Finset.Nat.mem_antidiagonalTuple] at hα
        exact hodd α (by rw [hα]; exact hj.add_even even_two)
      rw [Finset.sum_eq_zero fun α hα => by rw [this α hα]; ring, mul_zero]
    · obtain ⟨j', hj', hodd'⟩ := hB
      have hB' : ∃ j ∈ B, Odd j := by
        rcases List.mem_cons.mp hj' with h | h
        · exact absurd (h ▸ hodd') hj
        · exact ⟨j', h, hodd'⟩
      rw [Finset.sum_eq_zero fun α _ => by rw [ih hB' (β + α)]; simp, mul_zero]

theorem even_sum_of_even (l : List ℕ) (h : ∀ j ∈ l, Even j) : Even l.sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.sum_cons]
    exact (h j (by simp)).add (ih fun k hk => h k (List.mem_cons_of_mem _ hk))

/-- **Symmetry**: if every cumulant of odd order vanishes, `P_r = 0` for odd `r`. -/
theorem edgeP_odd (hV : vcov p ξ = diagonal D) (hD : ∀ i, 0 < D i)
    (hodd : ∀ α : Fin d → ℕ, Odd (∑ i, α i) → cumul p ξ α = 0) {r : ℕ} (hr : Odd r) :
    edgeP p ξ r = 0 := by
  funext x
  rw [edgeP_diag p ξ D hV hD, Pi.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hB : ∃ j ∈ c.blocks, Odd j := by
    by_contra h
    push_neg at h
    have := even_sum_of_even c.blocks fun j hj => Nat.not_odd_iff_even.mp (h j hj)
    rw [c.blocks_sum] at this
    exact (Nat.not_even_iff_odd.mpr hr) this
  rw [evB_odd p ξ D hodd _ hB, Pi.zero_apply, mul_zero]

end Expand

end ArcsAlgo.LLT
