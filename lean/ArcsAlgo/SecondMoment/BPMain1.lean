module

public import ArcsAlgo.SecondMoment.BPConst
public import ArcsAlgo.LocalLimit.LemmaB0
set_option autoImplicit false

/-!
# Proposition B′: the local expansions of the laws and the algebra of the ratio

`gen_cond`, `gen_uncond` (the generic identities, from the vanishing low coefficients), `bound_on_box`,
`ratio_err`; `brX5`, `brY5`, `brS5` (the hypothesis `BR22Edge` at order 5 for `X`, `Y`, `S`, in the decomposed
form); `gauss_cancel` (`φ_X φ_S = φ_Y²`); `ratio_laws`, `lamB_laws`; `cont_coefs`.
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

/-! ### Algebra and bounds for the ratio -/

theorem gen_cond (a1 a2 a3 bX b1 b2 b3 bY c1 c2 c3 bS K2 K3 h : ℝ)
    (e1 : a1 - 2*b1 + c1 = 0) (e2 : -K2 + a1*c1 + a2 - b1 ^ 2 - 2*b2 + c2 = 0) (e3 : -2*K2*b1 - K3 + a1*c2 + a2*c1 + a3 - 2*b1*b2 - 2*b3 + c3 = 0) :
    (1 + h * a1 + h ^ 2 * a2 + h ^ 3 * a3 + h ^ 4 * bX) * (1 + h * c1 + h ^ 2 * c2 + h ^ 3 * c3 + h ^ 4 * bS) -
      (1 + K2 * h ^ 2 + K3 * h ^ 3) * (1 + h * b1 + h ^ 2 * b2 + h ^ 3 * b3 + h ^ 4 * bY) ^ 2 =
      h ^ 4 * (-K2*b1 ^ 2 - 2*K2*b1*b2*h - 2*K2*b1*b3*h ^ 2 - 2*K2*b1*bY*h ^ 3 - K2*b2 ^ 2*h ^ 2 - 2*K2*b2*b3*h ^ 3 - 2*K2*b2*bY*h ^ 4 - 2*K2*b2 - K2*b3 ^ 2*h ^ 4 - 2*K2*b3*bY*h ^ 5 - 2*K2*b3*h - K2*bY ^ 2*h ^ 6 - 2*K2*bY*h ^ 2 - K3*b1 ^ 2*h - 2*K3*b1*b2*h ^ 2 - 2*K3*b1*b3*h ^ 3 - 2*K3*b1*bY*h ^ 4 - 2*K3*b1 - K3*b2 ^ 2*h ^ 3 - 2*K3*b2*b3*h ^ 4 - 2*K3*b2*bY*h ^ 5 - 2*K3*b2*h - K3*b3 ^ 2*h ^ 5 - 2*K3*b3*bY*h ^ 6 - 2*K3*b3*h ^ 2 - K3*bY ^ 2*h ^ 7 - 2*K3*bY*h ^ 3 + a1*bS*h + a1*c3 + a2*bS*h ^ 2 + a2*c2 + a2*c3*h + a3*bS*h ^ 3 + a3*c1 + a3*c2*h + a3*c3*h ^ 2 - 2*b1*b3 - 2*b1*bY*h - b2 ^ 2 - 2*b2*b3*h - 2*b2*bY*h ^ 2 - b3 ^ 2*h ^ 2 - 2*b3*bY*h ^ 3 + bS*bX*h ^ 4 + bS + bX*c1*h + bX*c2*h ^ 2 + bX*c3*h ^ 3 + bX - bY ^ 2*h ^ 4 - 2*bY) := by
  linear_combination h * e1 + h ^ 2 * e2 + h ^ 3 * e3

theorem gen_uncond (p2 p4 BX q2 q4 BY kk cc h : ℝ) (e2 : -kk + p2 - 2*q2 = 0) (e4 : -cc - 2*kk*q2 + p4 - q2 ^ 2 - 2*q4 = 0) :
    (1 + h ^ 2 * p2 + h ^ 4 * p4 + h ^ 6 * BX) - (1 + kk * h ^ 2 + cc * h ^ 4) * (1 + h ^ 2 * q2 + h ^ 4 * q4 + h ^ 6 * BY) ^ 2 =
      h ^ 6 * (BX - BY ^ 2*cc*h ^ 10 - BY ^ 2*h ^ 8*kk - BY ^ 2*h ^ 6 - 2*BY*cc*h ^ 8*q4 - 2*BY*cc*h ^ 6*q2 - 2*BY*cc*h ^ 4 - 2*BY*h ^ 6*kk*q4 - 2*BY*h ^ 4*kk*q2 - 2*BY*h ^ 4*q4 - 2*BY*h ^ 2*kk - 2*BY*h ^ 2*q2 - 2*BY - cc*h ^ 6*q4 ^ 2 - 2*cc*h ^ 4*q2*q4 - cc*h ^ 2*q2 ^ 2 - 2*cc*h ^ 2*q4 - 2*cc*q2 - h ^ 4*kk*q4 ^ 2 - 2*h ^ 2*kk*q2*q4 - h ^ 2*q4 ^ 2 - kk*q2 ^ 2 - 2*kk*q4 - 2*q2*q4) := by
  linear_combination h ^ 2 * e2 + h ^ 4 * e4



/-- A continuous function is bounded on the box `[0,1] × [−g,g] × [−K,K]`. -/
theorem bound_on_box {f : ℝ → ℝ → ℝ → ℝ} (hf : Continuous fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2)
    (g K : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h z u : ℝ, 0 ≤ h → h ≤ 1 → |z| ≤ g → |u| ≤ K → |f h z u| ≤ C := by
  have hS : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (-g) g ×ˢ Set.Icc (-K) K)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun h z u h0 h1 hz hu => ?_⟩
  have := hC (h, z, u) ⟨⟨h0, h1⟩, ⟨abs_le.mp hz, abs_le.mp hu⟩⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- **The ratio with errors**: if `F_X F_S − K F_Y² = h⁴ G`, all of `F_X, F_S, F_Y, K, G` are bounded
by `A`, the errors are `≤ A h⁴` and `F_Y + δ_Y ≥ 1/2`, then the ratio is `K + O(h⁴)`. -/
theorem ratio_err {FX FS FY K G dX dS dY h A : ℝ} (hE : FX * FS - K * FY ^ 2 = h ^ 4 * G)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hA : 0 ≤ A) (hFX : |FX| ≤ A) (hFS : |FS| ≤ A) (hFY : |FY| ≤ A)
    (hK : |K| ≤ A) (hG : |G| ≤ A) (hdX : |dX| ≤ A * h ^ 4) (hdS : |dS| ≤ A * h ^ 4) (hdY : |dY| ≤ A * h ^ 4)
    (hY : 1 / 2 ≤ FY + dY) :
    |(FX + dX) * (FS + dS) / (FY + dY) ^ 2 - K| ≤ 4 * (A + 3 * A ^ 2 + 3 * A ^ 3) * h ^ 4 := by
  have hh4 : 0 ≤ h ^ 4 := by positivity
  have hh41 : h ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have hd : 0 < (FY + dY) ^ 2 := by nlinarith
  have hd4 : 1 / 4 ≤ (FY + dY) ^ 2 := by nlinarith
  have eN : (FX + dX) * (FS + dS) - (FY + dY) ^ 2 * K =
      h ^ 4 * G + (dX * FS + FX * dS + dX * dS - K * (2 * FY * dY + dY ^ 2)) := by
    linear_combination hE
  rw [div_sub' (ne_of_gt hd), abs_div, abs_of_pos hd, eN]
  have b1 : |h ^ 4 * G| ≤ A * h ^ 4 := by rw [abs_mul, abs_of_nonneg hh4]; nlinarith [abs_nonneg G]
  have bXS : |dX * FS| ≤ A ^ 2 * h ^ 4 := by
    rw [abs_mul]; nlinarith [abs_nonneg dX, abs_nonneg FS]
  have bSX : |FX * dS| ≤ A ^ 2 * h ^ 4 := by
    rw [abs_mul]; nlinarith [abs_nonneg FX, abs_nonneg dS]
  have bdd : |dX * dS| ≤ A ^ 2 * h ^ 4 := by
    rw [abs_mul]
    have : |dS| ≤ A := by nlinarith
    nlinarith [abs_nonneg dX, abs_nonneg dS]
  have bK : |K * (2 * FY * dY + dY ^ 2)| ≤ 3 * A ^ 3 * h ^ 4 := by
    rw [abs_mul]
    have hdY1 : |dY| ≤ A := by nlinarith
    have : |2 * FY * dY + dY ^ 2| ≤ 3 * A ^ 2 * h ^ 4 := by
      calc |2 * FY * dY + dY ^ 2| ≤ |2 * FY * dY| + |dY ^ 2| := abs_add_le _ _
        _ = 2 * |FY| * |dY| + |dY| * |dY| := by rw [abs_mul, abs_mul, abs_two, sq, abs_mul]
        _ ≤ 2 * A * (A * h ^ 4) + A * (A * h ^ 4) := by
            gcongr
        _ = 3 * A ^ 2 * h ^ 4 := by ring
    calc |K| * |2 * FY * dY + dY ^ 2| ≤ A * (3 * A ^ 2 * h ^ 4) :=
          mul_le_mul hK this (abs_nonneg _) hA
      _ = 3 * A ^ 3 * h ^ 4 := by ring
  have hN : |h ^ 4 * G + (dX * FS + FX * dS + dX * dS - K * (2 * FY * dY + dY ^ 2))| ≤
      (A + 3 * A ^ 2 + 3 * A ^ 3) * h ^ 4 := by
    calc _ ≤ |h ^ 4 * G| + (|dX * FS| + |FX * dS| + |dX * dS| + |K * (2 * FY * dY + dY ^ 2)|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans le_rfl) le_rfl)
      _ ≤ A * h ^ 4 + (A ^ 2 * h ^ 4 + A ^ 2 * h ^ 4 + A ^ 2 * h ^ 4 + 3 * A ^ 3 * h ^ 4) := by gcongr
      _ = (A + 3 * A ^ 2 + 3 * A ^ 3) * h ^ 4 := by ring
  rw [div_le_iff₀ hd]
  have hc : 0 ≤ (A + 3 * A ^ 2 + 3 * A ^ 3) * h ^ 4 := by positivity
  nlinarith

/-! ### The local expansions of the three laws at order 5 -/

section BR

variable {M : ℕ}

theorem sig_zB (hM : 2 ≤ M) {m : ℕ} (hm : 1 ≤ m) (s : ℤ) :
    √(sig2 M) * zB M m s = ((s : ℝ) - m * (((M : ℝ) + 1) / 2)) / √(m : ℝ) := by
  have hσ : √(sig2 M) ≠ 0 := (Real.sqrt_pos.mpr (sig2_pos' hM)).ne'
  have hm0 : √(m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
  unfold zB tB muW; field_simp

set_option maxHeartbeats 4000000 in
theorem brX5 (hBR : BR22Edge) (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ s u : ℤ, (2 : ℤ) ∣ u - s →
    |√(m : ℝ) ^ 3 * lawPow (pX M) (xiX M) m ![s, u, u] -
      4 * (gaussDens (vcov (pX M) (xiX M)) ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] *
        (1 + (1 / √(m : ℝ)) ^ (1 : ℕ) * FXt1 M (zB M m s) u + (1 / √(m : ℝ)) ^ (2 : ℕ) * FXt2 M (zB M m s) u +
          (1 / √(m : ℝ)) ^ (3 : ℕ) * FXt3 M (zB M m s) u +
          (1 / √(m : ℝ)) ^ (4 : ℕ) * FXB M (1 / √(m : ℝ)) (zB M m s) u))| ≤ C * (1 / √(m : ℝ)) ^ 4 := by
  have i0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool × Bool) 3 (pX M) (xiX M) pX_nonneg (pX_sum hM1) (posDef_X hM)
    (⟨0, i0⟩, true, true) (by positivity) 5 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun m hm s u hsu => ?_⟩
  have hmem : ![s, u, u] - m • xiX M (⟨0, i0⟩, true, true) ∈ minLat (pX M) (xiX M) := by
    rw [minLat_X hM, mem_ker_parX]
    simp [xiX, sg]
    exact hsu
  have h := hC m hm _ hmem
  have hpt : (fun j => ((((![s, u, u] : Fin 3 → ℤ) j : ℤ) : ℝ) - m * vmean (pX M) (xiX M) j) / √(m : ℝ)) =
      ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] := by
    rw [vmean_X hM1, sig_zB hM hm]
    funext j; fin_cases j <;> simp <;> ring
  rw [hpt, minLat_X hM, index_parX] at h
  have hsum : ∑ r ∈ range (5 - 1), edgeP (pX M) (xiX M) r
      ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] / √(m : ℝ) ^ r =
      ∑ r ∈ range 4, edgeP (pX M) (xiX M) r
      ![√(sig2 M) * zB M m s, (u : ℝ) * (1 / √(m : ℝ)), (u : ℝ) * (1 / √(m : ℝ))] * (1 / √(m : ℝ)) ^ r := by
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hsum, FX_decomp hM (1 / √(m : ℝ)) (zB M m s) u] at h
  push_cast at h ⊢
  refine h.trans ?_
  rw [div_eq_mul_one_div, _root_.one_div_pow]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

set_option maxHeartbeats 4000000 in
theorem brY5 (hBR : BR22Edge) (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ s u : ℤ, (2 : ℤ) ∣ u - s →
    |√(m : ℝ) ^ 2 * lawPow (pY M) (xiY M) m ![s, u] -
      2 * (gaussDens (vcov (pY M) (xiY M)) ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ))] *
        (1 + (1 / √(m : ℝ)) ^ (1 : ℕ) * FYt1 M (zB M m s) u + (1 / √(m : ℝ)) ^ (2 : ℕ) * FYt2 M (zB M m s) u +
          (1 / √(m : ℝ)) ^ (3 : ℕ) * FYt3 M (zB M m s) u +
          (1 / √(m : ℝ)) ^ (4 : ℕ) * FYB M (1 / √(m : ℝ)) (zB M m s) u))| ≤ C * (1 / √(m : ℝ)) ^ 4 := by
  have i0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool) 2 (pY M) (xiY M) pY_nonneg (pY_sum hM1) (posDef_Y hM)
    (⟨0, i0⟩, true) (by positivity) 5 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun m hm s u hsu => ?_⟩
  have hmem : ![s, u] - m • xiY M (⟨0, i0⟩, true) ∈ minLat (pY M) (xiY M) := by
    rw [minLat_Y hM, mem_ker_parY]
    simp [xiY, sg]
    exact hsu
  have h := hC m hm _ hmem
  have hpt : (fun j => ((((![s, u] : Fin 2 → ℤ) j : ℤ) : ℝ) - m * vmean (pY M) (xiY M) j) / √(m : ℝ)) =
      ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ))] := by
    rw [vmean_Y hM1, sig_zB hM hm]
    funext j; fin_cases j <;> simp <;> ring
  rw [hpt, minLat_Y hM, index_parY] at h
  have hsum : ∑ r ∈ range (5 - 1), edgeP (pY M) (xiY M) r
      ![√(sig2 M) * zB M m s, u * (1 / √(m : ℝ))] / √(m : ℝ) ^ r =
      ∑ r ∈ range 4, edgeP (pY M) (xiY M) r
      ![√(sig2 M) * zB M m s, (u : ℝ) * (1 / √(m : ℝ))] * (1 / √(m : ℝ)) ^ r := by
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hsum, FY_decomp hM (1 / √(m : ℝ)) (zB M m s) u] at h
  push_cast at h ⊢
  refine h.trans ?_
  rw [div_eq_mul_one_div, _root_.one_div_pow]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

set_option maxHeartbeats 4000000 in
theorem brS5 (hBR : BR22Edge) (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ s : ℤ,
    |√(m : ℝ) ^ 1 * lawPow (pS M) (xi1 M) m ![s] -
      1 * (gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * zB M m s] *
        (1 + (1 / √(m : ℝ)) ^ (1 : ℕ) * FSt1 M (zB M m s) 0 + (1 / √(m : ℝ)) ^ (2 : ℕ) * FSt2 M (zB M m s) 0 +
          (1 / √(m : ℝ)) ^ (3 : ℕ) * FSt3 M (zB M m s) 0 +
          (1 / √(m : ℝ)) ^ (4 : ℕ) * FSB M (1 / √(m : ℝ)) (zB M m s) 0))| ≤ C * (1 / √(m : ℝ)) ^ 4 := by
  have i0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C, hC⟩ := hBR (Fin M) 1 (pS M) (xi1 M) pS_nonneg (pS_sum hM1) (posDef_1 hM)
    ⟨0, i0⟩ (by positivity) 5 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun m hm s => ?_⟩
  have hmem : ![s] - m • xi1 M ⟨0, i0⟩ ∈ minLat (pS M) (xi1 M) := by
    rw [minLat_1 hM]; exact AddSubgroup.mem_top _
  have h := hC m hm _ hmem
  have hpt : (fun j => ((((![s] : Fin 1 → ℤ) j : ℤ) : ℝ) - m * vmean (pS M) (xi1 M) j) / √(m : ℝ)) =
      ![√(sig2 M) * zB M m s] := by
    rw [vmean_1 hM1, sig_zB hM hm]
    funext j; fin_cases j; simp
  rw [hpt, minLat_1 hM, AddSubgroup.index_top] at h
  have hsum : ∑ r ∈ range (5 - 1), edgeP (pS M) (xi1 M) r ![√(sig2 M) * zB M m s] / √(m : ℝ) ^ r =
      ∑ r ∈ range 4, edgeP (pS M) (xi1 M) r ![√(sig2 M) * zB M m s] * (1 / √(m : ℝ)) ^ r := by
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hsum, FS_decomp hM (1 / √(m : ℝ)) (zB M m s) 0] at h
  push_cast at h ⊢
  refine h.trans ?_
  rw [div_eq_mul_one_div, _root_.one_div_pow]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end BR

/-- The remainder of the conditional expansion. -/
noncomputable def GC (M : ℕ) (h z u : ℝ) : ℝ := -(KK2 M)*(FYt1 M z u) ^ 2 - 2*(KK2 M)*(FYt1 M z u)*(FYt2 M z u)*h - 2*(KK2 M)*(FYt1 M z u)*(FYt3 M z u)*h ^ 2 - 2*(KK2 M)*(FYt1 M z u)*(FYB M h z u)*h ^ 3 - (KK2 M)*(FYt2 M z u) ^ 2*h ^ 2 - 2*(KK2 M)*(FYt2 M z u)*(FYt3 M z u)*h ^ 3 - 2*(KK2 M)*(FYt2 M z u)*(FYB M h z u)*h ^ 4 - 2*(KK2 M)*(FYt2 M z u) - (KK2 M)*(FYt3 M z u) ^ 2*h ^ 4 - 2*(KK2 M)*(FYt3 M z u)*(FYB M h z u)*h ^ 5 - 2*(KK2 M)*(FYt3 M z u)*h - (KK2 M)*(FYB M h z u) ^ 2*h ^ 6 - 2*(KK2 M)*(FYB M h z u)*h ^ 2 - (KK3 M * z)*(FYt1 M z u) ^ 2*h - 2*(KK3 M * z)*(FYt1 M z u)*(FYt2 M z u)*h ^ 2 - 2*(KK3 M * z)*(FYt1 M z u)*(FYt3 M z u)*h ^ 3 - 2*(KK3 M * z)*(FYt1 M z u)*(FYB M h z u)*h ^ 4 - 2*(KK3 M * z)*(FYt1 M z u) - (KK3 M * z)*(FYt2 M z u) ^ 2*h ^ 3 - 2*(KK3 M * z)*(FYt2 M z u)*(FYt3 M z u)*h ^ 4 - 2*(KK3 M * z)*(FYt2 M z u)*(FYB M h z u)*h ^ 5 - 2*(KK3 M * z)*(FYt2 M z u)*h - (KK3 M * z)*(FYt3 M z u) ^ 2*h ^ 5 - 2*(KK3 M * z)*(FYt3 M z u)*(FYB M h z u)*h ^ 6 - 2*(KK3 M * z)*(FYt3 M z u)*h ^ 2 - (KK3 M * z)*(FYB M h z u) ^ 2*h ^ 7 - 2*(KK3 M * z)*(FYB M h z u)*h ^ 3 + (FXt1 M z u)*(FSB M h z 0)*h + (FXt1 M z u)*(FSt3 M z 0) + (FXt2 M z u)*(FSB M h z 0)*h ^ 2 + (FXt2 M z u)*(FSt2 M z 0) + (FXt2 M z u)*(FSt3 M z 0)*h + (FXt3 M z u)*(FSB M h z 0)*h ^ 3 + (FXt3 M z u)*(FSt1 M z 0) + (FXt3 M z u)*(FSt2 M z 0)*h + (FXt3 M z u)*(FSt3 M z 0)*h ^ 2 - 2*(FYt1 M z u)*(FYt3 M z u) - 2*(FYt1 M z u)*(FYB M h z u)*h - (FYt2 M z u) ^ 2 - 2*(FYt2 M z u)*(FYt3 M z u)*h - 2*(FYt2 M z u)*(FYB M h z u)*h ^ 2 - (FYt3 M z u) ^ 2*h ^ 2 - 2*(FYt3 M z u)*(FYB M h z u)*h ^ 3 + (FSB M h z 0)*(FXB M h z u)*h ^ 4 + (FSB M h z 0) + (FXB M h z u)*(FSt1 M z 0)*h + (FXB M h z u)*(FSt2 M z 0)*h ^ 2 + (FXB M h z u)*(FSt3 M z 0)*h ^ 3 + (FXB M h z u) - (FYB M h z u) ^ 2*h ^ 4 - 2*(FYB M h z u)

/-- The remainder of the unconditional expansion. -/
noncomputable def GU (M : ℕ) (h u : ℝ) : ℝ := (FXuB M h u) - (FYuB M h u) ^ 2*(CCu M u)*h ^ 10 - (FYuB M h u) ^ 2*h ^ 8*(KKu M) - (FYuB M h u) ^ 2*h ^ 6 - 2*(FYuB M h u)*(CCu M u)*h ^ 8*(FYut4 M u) - 2*(FYuB M h u)*(CCu M u)*h ^ 6*(FYut2 M u) - 2*(FYuB M h u)*(CCu M u)*h ^ 4 - 2*(FYuB M h u)*h ^ 6*(KKu M)*(FYut4 M u) - 2*(FYuB M h u)*h ^ 4*(KKu M)*(FYut2 M u) - 2*(FYuB M h u)*h ^ 4*(FYut4 M u) - 2*(FYuB M h u)*h ^ 2*(KKu M) - 2*(FYuB M h u)*h ^ 2*(FYut2 M u) - 2*(FYuB M h u) - (CCu M u)*h ^ 6*(FYut4 M u) ^ 2 - 2*(CCu M u)*h ^ 4*(FYut2 M u)*(FYut4 M u) - (CCu M u)*h ^ 2*(FYut2 M u) ^ 2 - 2*(CCu M u)*h ^ 2*(FYut4 M u) - 2*(CCu M u)*(FYut2 M u) - h ^ 4*(KKu M)*(FYut4 M u) ^ 2 - 2*h ^ 2*(KKu M)*(FYut2 M u)*(FYut4 M u) - h ^ 2*(FYut4 M u) ^ 2 - (KKu M)*(FYut2 M u) ^ 2 - 2*(KKu M)*(FYut4 M u) - 2*(FYut2 M u)*(FYut4 M u)

section Cond

variable {M : ℕ}

theorem gaussX_val (hM : 2 ≤ M) (z y : ℝ) :
    gaussDens (vcov (pX M) (xiX M)) ![√(sig2 M) * z, y, y] =
      Real.exp (-(1 / 2) * (z ^ 2 + 2 * (y ^ 2 / ew2 M))) / (√(2 * Real.pi) ^ 3 * (√(sig2 M) * ew2 M)) := by
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  rw [vcov_X (by omega), gaussDens_diag _ (fun i => by fin_cases i <;> simp [hs2, he])]
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h1 : √(sig2 M * ew2 M * ew2 M) = √(sig2 M) * ew2 M := by
    rw [mul_assoc, Real.sqrt_mul hs2.le, Real.sqrt_mul_self he.le]
  rw [h1, mul_pow, Real.sq_sqrt hs2.le]
  congr 2; field_simp; ring

theorem gaussY_val (hM : 2 ≤ M) (z y : ℝ) :
    gaussDens (vcov (pY M) (xiY M)) ![√(sig2 M) * z, y] =
      Real.exp (-(1 / 2) * (z ^ 2 + y ^ 2 / ew2 M)) / (√(2 * Real.pi) ^ 2 * (√(sig2 M) * √(ew2 M))) := by
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  rw [vcov_Y (by omega), gaussDens_diag _ (fun i => by fin_cases i <;> simp [hs2, he])]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Real.sqrt_mul hs2.le, mul_pow, Real.sq_sqrt hs2.le]
  congr 2; field_simp

theorem gaussS_val (hM : 2 ≤ M) (z : ℝ) :
    gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * z] =
      Real.exp (-(1 / 2) * z ^ 2) / (√(2 * Real.pi) ^ 1 * √(sig2 M)) := by
  have hs2 := sig2_pos' hM
  rw [vcov_1 (by omega), gaussDens_diag _ (fun i => by fin_cases i; simp [hs2])]
  simp only [Fin.sum_univ_one, Fin.prod_univ_one, Matrix.cons_val_zero]
  rw [mul_pow, Real.sq_sqrt hs2.le]
  congr 2; field_simp

/-- The Gaussian factors cancel: `φ_X φ_S = φ_Y²`. -/
theorem gauss_cancel (hM : 2 ≤ M) (z y : ℝ) :
    gaussDens (vcov (pX M) (xiX M)) ![√(sig2 M) * z, y, y] * gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * z] =
      gaussDens (vcov (pY M) (xiY M)) ![√(sig2 M) * z, y] ^ 2 := by
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  have hπ : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hσ := Real.sqrt_pos.mpr hs2
  have hse := Real.sqrt_pos.mpr he
  rw [gaussX_val hM, gaussS_val hM, gaussY_val hM, div_pow, ← Real.exp_nat_mul, div_mul_div_comm,
    ← Real.exp_add, mul_pow, mul_pow, Real.sq_sqrt he.le]
  congr 1
  · congr 1; push_cast; ring
  · ring

theorem two_pow_ge_cube (m : ℕ) (hm : 10 ≤ m) : (m : ℝ) ^ 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    push_cast
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [h2]
    have h10 : (10 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have h3 : 10 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
      rw [pow_succ]; nlinarith
    have : ((n : ℝ) + 1) ^ 3 ≤ 2 * (n : ℝ) ^ 3 := by nlinarith
    linarith

end Cond

section CondMain

variable {M : ℕ}

theorem ratio_laws (hM : 2 ≤ M) (m : ℕ) (s u : ℤ)
    (hY : lawPow (pY M) (xiY M) m ![s, u] ≠ 0) (h1 : lawPow (pS M) (xi1 M) m ![s] ≠ 0) :
    m2B M m s u / lamB M m s u ^ 2 =
      lawPow (pX M) (xiX M) m ![s, u, u] * lawPow (pS M) (xi1 M) m ![s] / lawPow (pY M) (xiY M) m ![s, u] ^ 2 := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have eX := lawX_eq M m s u
  have eY := lawY_eq M m s u
  have e1 := law1_eq M m s
  change lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] ≠ 0 at hY
  change lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] ≠ 0 at h1
  change _ = lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiX M) m ![s, u, u] * lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] /
    lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] ^ 2
  rw [eX, eY, e1] at *
  have hZ : (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ)) ≠ 0 := by
    intro h; apply hY; rw [h, mul_zero]
  have hc : (cntS M m s : ℝ) ≠ 0 := by intro h; apply h1; rw [h, mul_zero]
  unfold m2B lamB
  field_simp
  have hp : ((1 / ((M : ℝ) * 2)) ^ m) ^ 2 = (1 / (4 * (M : ℝ))) ^ m * (1 / (M : ℝ)) ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]; congr 1; field_simp; ring
  rw [hp]; ring

theorem lamB_laws (hM : 2 ≤ M) (m : ℕ) (s u : ℤ) (h1 : lawPow (pS M) (xi1 M) m ![s] ≠ 0) :
    lamB M m s u = 2 ^ m * lawPow (pY M) (xiY M) m ![s, u] / lawPow (pS M) (xi1 M) m ![s] := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have eY := lawY_eq M m s u
  have e1 := law1_eq M m s
  change lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] ≠ 0 at h1
  change _ = 2 ^ m * lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] / lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s]
  rw [eY, e1] at *
  have hc : (cntS M m s : ℝ) ≠ 0 := by intro h; apply h1; rw [h, mul_zero]
  unfold lamB
  field_simp
  rw [mul_assoc, ← mul_pow]
  congr 2; field_simp

end CondMain

section CondThm

variable {M : ℕ}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cont_coefs (M : ℕ) : Continuous fun q : ℝ × ℝ × ℝ =>
    |FXt1 M q.2.1 q.2.2| + |FXt2 M q.2.1 q.2.2| + |FXt3 M q.2.1 q.2.2| + |FXB M q.1 q.2.1 q.2.2| +
    |FYt1 M q.2.1 q.2.2| + |FYt2 M q.2.1 q.2.2| + |FYt3 M q.2.1 q.2.2| + |FYB M q.1 q.2.1 q.2.2| +
    |FSt2 M q.2.1 0| + |GC M q.1 q.2.1 q.2.2| := by
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => FXt1 M q.2.1 q.2.2 := by unfold FXt1; fun_prop
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => FXt2 M q.2.1 q.2.2 := by unfold FXt2; fun_prop
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => FXt3 M q.2.1 q.2.2 := by unfold FXt3; fun_prop
  have c4 : Continuous fun q : ℝ × ℝ × ℝ => FXB M q.1 q.2.1 q.2.2 := by unfold FXB; fun_prop
  have c5 : Continuous fun q : ℝ × ℝ × ℝ => FYt1 M q.2.1 q.2.2 := by unfold FYt1; fun_prop
  have c6 : Continuous fun q : ℝ × ℝ × ℝ => FYt2 M q.2.1 q.2.2 := by unfold FYt2; fun_prop
  have c7 : Continuous fun q : ℝ × ℝ × ℝ => FYt3 M q.2.1 q.2.2 := by unfold FYt3; fun_prop
  have c8 : Continuous fun q : ℝ × ℝ × ℝ => FYB M q.1 q.2.1 q.2.2 := by unfold FYB; fun_prop
  have c9 : Continuous fun q : ℝ × ℝ × ℝ => FSt2 M q.2.1 0 := by unfold FSt2; fun_prop
  have c10 : Continuous fun q : ℝ × ℝ × ℝ => FSt1 M q.2.1 0 := by unfold FSt1; fun_prop
  have c11 : Continuous fun q : ℝ × ℝ × ℝ => FSt3 M q.2.1 0 := by unfold FSt3; fun_prop
  have c12 : Continuous fun q : ℝ × ℝ × ℝ => FSB M q.1 q.2.1 0 := by unfold FSB; fun_prop
  have cG : Continuous fun q : ℝ × ℝ × ℝ => GC M q.1 q.2.1 q.2.2 := by unfold GC; fun_prop
  fun_prop

end CondThm

end ArcsAlgo.LLT
