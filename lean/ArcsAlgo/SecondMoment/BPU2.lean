module

public import ArcsAlgo.SecondMoment.BPU1
set_option autoImplicit false

/-!
# Proposition B′, unconditional part: the local expansions at order 7

`brXu7`, `brYu7` (`BR22Edge` at order 7 for `X′ = (εw, ε′w)` and `Y′ = εw`), `gauss_cancelU` (`φ_{X′} = φ_{Y′}²`),
`coef_boundsU`, `ratio_lawsU`, `lamU_laws`.
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

set_option maxHeartbeats 4000000 in
theorem brXu7 (hBR : BR22Edge) (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ u : ℤ,
    |√(m : ℝ) ^ 2 * lawPow (pX M) (xiXu M) m ![u, u] -
      2 * (gaussDens (vcov (pX M) (xiXu M)) ![u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] *
        (1 + (1 / √(m : ℝ)) ^ (2 : ℕ) * FXut2 M u + (1 / √(m : ℝ)) ^ (4 : ℕ) * FXut4 M u +
          (1 / √(m : ℝ)) ^ (6 : ℕ) * FXuB M (1 / √(m : ℝ)) u))| ≤ C * (1 / √(m : ℝ)) ^ 6 := by
  have i0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool × Bool) 2 (pX M) (xiXu M) pX_nonneg (pX_sum hM1) (posDef_Xu hM)
    (⟨0, i0⟩, true, true) (by positivity) 7 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun m hm u => ?_⟩
  have hmem : ![u, u] - m • xiXu M (⟨0, i0⟩, true, true) ∈ minLat (pX M) (xiXu M) := by
    rw [minLat_Xu hM, mem_ker_parY]
    simp [xiXu, sg]
  have h := hC m hm _ hmem
  have hpt : (fun j => ((((![u, u] : Fin 2 → ℤ) j : ℤ) : ℝ) - m * vmean (pX M) (xiXu M) j) / √(m : ℝ)) =
      ![u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] := by
    rw [vmean_Xu hM1]
    funext j; fin_cases j <;> simp <;> ring
  rw [hpt, minLat_Xu hM, index_parY] at h
  have hsum : ∑ r ∈ range (7 - 1), edgeP (pX M) (xiXu M) r
      ![u * (1 / √(m : ℝ)), u * (1 / √(m : ℝ))] / √(m : ℝ) ^ r =
      ∑ r ∈ range 6, edgeP (pX M) (xiXu M) r
      ![(u : ℝ) * (1 / √(m : ℝ)), (u : ℝ) * (1 / √(m : ℝ))] * (1 / √(m : ℝ)) ^ r := by
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hsum, FXu_decomp hM (1 / √(m : ℝ)) u] at h
  push_cast at h ⊢
  refine h.trans ?_
  rw [div_eq_mul_one_div, _root_.one_div_pow]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

set_option maxHeartbeats 4000000 in
theorem brYu7 (hBR : BR22Edge) (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ u : ℤ,
    |√(m : ℝ) ^ 1 * lawPow (pY M) (xiYu M) m ![u] -
      1 * (gaussDens (vcov (pY M) (xiYu M)) ![u * (1 / √(m : ℝ))] *
        (1 + (1 / √(m : ℝ)) ^ (2 : ℕ) * FYut2 M u + (1 / √(m : ℝ)) ^ (4 : ℕ) * FYut4 M u +
          (1 / √(m : ℝ)) ^ (6 : ℕ) * FYuB M (1 / √(m : ℝ)) u))| ≤ C * (1 / √(m : ℝ)) ^ 6 := by
  have i0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool) 1 (pY M) (xiYu M) pY_nonneg (pY_sum hM1) (posDef_Yu hM)
    (⟨0, i0⟩, true) (by positivity) 7 (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun m hm u => ?_⟩
  have hmem : ![u] - m • xiYu M (⟨0, i0⟩, true) ∈ minLat (pY M) (xiYu M) := by
    rw [minLat_Yu hM]; exact AddSubgroup.mem_top _
  have h := hC m hm _ hmem
  have hpt : (fun j => ((((![u] : Fin 1 → ℤ) j : ℤ) : ℝ) - m * vmean (pY M) (xiYu M) j) / √(m : ℝ)) =
      ![u * (1 / √(m : ℝ))] := by
    rw [vmean_Yu hM1]
    funext j; fin_cases j; simp; ring
  rw [hpt, minLat_Yu hM, AddSubgroup.index_top] at h
  have hsum : ∑ r ∈ range (7 - 1), edgeP (pY M) (xiYu M) r ![u * (1 / √(m : ℝ))] / √(m : ℝ) ^ r =
      ∑ r ∈ range 6, edgeP (pY M) (xiYu M) r ![(u : ℝ) * (1 / √(m : ℝ))] * (1 / √(m : ℝ)) ^ r := by
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hsum, FYu_decomp hM (1 / √(m : ℝ)) u] at h
  push_cast at h ⊢
  refine h.trans ?_
  rw [div_eq_mul_one_div, _root_.one_div_pow]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem gaussXu_val (hM : 2 ≤ M) (y : ℝ) :
    gaussDens (vcov (pX M) (xiXu M)) ![y, y] =
      Real.exp (-(1 / 2) * (2 * (y ^ 2 / ew2 M))) / (√(2 * Real.pi) ^ 2 * ew2 M) := by
  have he := ew2_pos M
  rw [vcov_Xu (by omega), gaussDens_diag _ (fun i => by fin_cases i <;> simp [he])]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Real.sqrt_mul_self he.le]
  congr 2; ring

theorem gaussYu_val (hM : 2 ≤ M) (y : ℝ) :
    gaussDens (vcov (pY M) (xiYu M)) ![y] =
      Real.exp (-(1 / 2) * (y ^ 2 / ew2 M)) / (√(2 * Real.pi) ^ 1 * √(ew2 M)) := by
  have he := ew2_pos M
  rw [vcov_Yu (by omega), gaussDens_diag _ (fun i => by fin_cases i; simp [he])]
  simp only [Fin.sum_univ_one, Fin.prod_univ_one, Matrix.cons_val_zero]

theorem gauss_cancelU (hM : 2 ≤ M) (y : ℝ) :
    gaussDens (vcov (pX M) (xiXu M)) ![y, y] = gaussDens (vcov (pY M) (xiYu M)) ![y] ^ 2 := by
  have he := ew2_pos M
  have hπ : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussXu_val hM, gaussYu_val hM, div_pow, ← Real.exp_nat_mul, mul_pow, Real.sq_sqrt he.le]
  congr 1
  · congr 1; push_cast; ring
  · ring

theorem gaussYu_lb (hM : 2 ≤ M) {K y : ℝ} (hy : y ^ 2 ≤ K ^ 2) :
    Real.exp (-(1 / 2) * (K ^ 2 / ew2 M)) / (√(2 * Real.pi) ^ 1 * √(ew2 M)) ≤
      gaussDens (vcov (pY M) (xiYu M)) ![y] := by
  have he := ew2_pos M
  rw [gaussYu_val hM]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : y ^ 2 / ew2 M ≤ K ^ 2 / ew2 M := div_le_div_of_nonneg_right hy he.le
  linarith

theorem gaussXu_lb (hM : 2 ≤ M) {K y : ℝ} (hy : y ^ 2 ≤ K ^ 2) :
    (Real.exp (-(1 / 2) * (K ^ 2 / ew2 M)) / (√(2 * Real.pi) ^ 1 * √(ew2 M))) ^ 2 ≤
      gaussDens (vcov (pX M) (xiXu M)) ![y, y] := by
  rw [gauss_cancelU hM]
  exact pow_le_pow_left₀ (by positivity) (gaussYu_lb hM hy) 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem coef_boundsU (M : ℕ) (K : ℝ) : ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ h u : ℝ, 0 ≤ h → h ≤ 1 → |u| ≤ K →
    |FXut2 M u| ≤ A0 ∧ |FXut4 M u| ≤ A0 ∧ |FXuB M h u| ≤ A0 ∧
    |FYut2 M u| ≤ A0 ∧ |FYut4 M u| ≤ A0 ∧ |FYuB M h u| ≤ A0 ∧ |GU M h u| ≤ A0 := by
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => FXut2 M q.2.2 := by unfold FXut2; fun_prop
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => FXut4 M q.2.2 := by unfold FXut4; fun_prop
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => FXuB M q.1 q.2.2 := by unfold FXuB; fun_prop
  have c4 : Continuous fun q : ℝ × ℝ × ℝ => FYut2 M q.2.2 := by unfold FYut2; fun_prop
  have c5 : Continuous fun q : ℝ × ℝ × ℝ => FYut4 M q.2.2 := by unfold FYut4; fun_prop
  have c6 : Continuous fun q : ℝ × ℝ × ℝ => FYuB M q.1 q.2.2 := by unfold FYuB; fun_prop
  have c7 : Continuous fun q : ℝ × ℝ × ℝ => KKu M := continuous_const
  have c8 : Continuous fun q : ℝ × ℝ × ℝ => CCu M q.2.2 := by
    unfold CCu KKu; fun_prop
  have cG : Continuous fun q : ℝ × ℝ × ℝ => GU M q.1 q.2.2 := by unfold GU; fun_prop
  obtain ⟨A0, hA0, hΦ⟩ := bound_on_box (f := fun h (_ : ℝ) u =>
    |FXut2 M u| + |FXut4 M u| + |FXuB M h u| + |FYut2 M u| + |FYut4 M u| + |FYuB M h u| + |GU M h u|)
    (by fun_prop) 0 K
  refine ⟨A0, hA0, fun h u h0 h1 hu => ?_⟩
  have hb := hΦ h 0 u h0 h1 (by simp) hu
  rw [abs_of_nonneg (by positivity)] at hb
  have := abs_nonneg (FXut2 M u); have := abs_nonneg (FXut4 M u); have := abs_nonneg (FXuB M h u)
  have := abs_nonneg (FYut2 M u); have := abs_nonneg (FYut4 M u); have := abs_nonneg (FYuB M h u)
  have := abs_nonneg (GU M h u)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem ratio_lawsU (hM : 2 ≤ M) (m : ℕ) (u : ℤ) (hY : lawPow (pY M) (xiYu M) m ![u] ≠ 0) (hp : parE M m u ≠ 0) :
    m2U M m u / lamU M m u ^ 2 =
      parE M m u * (lawPow (pX M) (xiXu M) m ![u, u] / lawPow (pY M) (xiYu M) m ![u] ^ 2) := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMm : (M : ℝ) ^ m ≠ 0 := pow_ne_zero _ hM0
  rw [lawYu_eq] at hY
  have hZ : (∑ w : Fin m → Fin M, (Zc w u : ℝ)) ≠ 0 := by intro h; apply hY; rw [h, mul_zero]
  have key : (1 / (4 * (M : ℝ))) ^ m = ((1 / (2 * (M : ℝ))) ^ m) ^ 2 * (M : ℝ) ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]; congr 1; field_simp; ring
  have hc2 : (1 / (2 * (M : ℝ))) ^ m ≠ 0 := pow_ne_zero _ (by positivity)
  unfold m2U lamU
  rw [sum_filter_par u (fun w hw => by rw [hw]; simp), sum_filter_par u (fun w hw => by rw [hw]; simp),
    lawXu_eq, lawYu_eq, key]
  field_simp

theorem lamU_laws (hM : 2 ≤ M) (m : ℕ) (u : ℤ) :
    lamU M m u = 2 ^ m * lawPow (pY M) (xiYu M) m ![u] / parE M m u := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold lamU
  rw [sum_filter_par u (fun w hw => by rw [hw]; simp), lawYu_eq]
  rw [show (2 : ℝ) ^ m * ((1 / (2 * (M : ℝ))) ^ m * ∑ w : Fin m → Fin M, (Zc w u : ℝ)) =
    (∑ w : Fin m → Fin M, (Zc w u : ℝ)) / (M : ℝ) ^ m by
      rw [← mul_assoc, ← mul_pow, show (2 : ℝ) * (1 / (2 * (M : ℝ))) = 1 / M by field_simp]
      rw [div_pow, one_pow]; ring]

end ArcsAlgo.LLT
