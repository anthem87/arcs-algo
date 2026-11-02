module

public import ArcsAlgo.SecondMoment.BPConst
set_option autoImplicit false

/-!
# Proposition B′: the limits of the constants as `M → ∞`

For `w` uniform on `{1, …, M}`: `κ_M → 1/5` (`kapB_tendsto`), `κ_{c,M} → 1/80` (`kapcB_tendsto`) and
`γ_M → −√3/80` (`gamB_tendsto`). By symmetry `Cov(w², w)/Var(w) = M + 1`, so `R = (w − μ)² − σ²` and
`B = 0` (`BB_eq_zero`); each constant is then a function of `x = 1/M` continuous at `0`.
-/

open Finset Filter Topology

@[expose] public section

namespace ArcsAlgo.LLT

theorem covW_div_varW {M : ℕ} (hM : 2 ≤ M) : covW M / varW M = M + 1 := by
  have h1 : (1 : ℕ) ≤ M := by omega
  have hv := varW_pos hM
  rw [div_eq_iff hv.ne']
  rw [covW, varW, mw1 h1, mw2 h1, mw3 h1]; ring

/-- `B = 0`: for `w` uniform on `{1, …, M}`, `R = (w − μ)² − σ²` and `R²(w − μ)` is odd about `μ`. -/
theorem BB_eq_zero {M : ℕ} (hM : 2 ≤ M) : BB M = 0 := by
  have h1 : (1 : ℕ) ≤ M := by omega
  have hc := covW_div_varW hM
  set g : ℝ → ℝ := fun w => RB M w ^ 2 * (w - mw M 1) with hg
  have hodd : ∀ w : ℝ, g ((M : ℝ) + 1 - w) = -g w := by
    intro w; simp only [hg, RB, hc, mw1 h1]; ring
  have hS : ∑ a : Fin M, g (((a : ℕ) : ℝ) + 1) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g ((i : ℝ) + 1)) M]
    have hr := Finset.sum_range_reflect (fun i => g ((i : ℝ) + 1)) M
    have hr' : ∑ j ∈ range M, g (((M - 1 - j : ℕ) : ℝ) + 1) = -∑ j ∈ range M, g ((j : ℝ) + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < M := Finset.mem_range.1 hj
      rw [show ((M - 1 - j : ℕ) : ℝ) + 1 = (M : ℝ) + 1 - ((j : ℝ) + 1) by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring, hodd]
    linarith
  unfold BB
  rw [show (∑ a : Fin M, RB M (((a : ℕ) : ℝ) + 1) ^ 2 * (((a : ℕ) : ℝ) + 1 - mw M 1)) =
    ∑ a : Fin M, g (((a : ℕ) : ℝ) + 1) from rfl, hS]
  simp

theorem varW_closed {M : ℕ} (hM : 1 ≤ M) : varW M = ((M : ℝ) ^ 2 - 1) / 12 := by
  rw [varW, mw1 hM, mw2 hM]; ring

theorem covW_closed {M : ℕ} (hM : 1 ≤ M) : covW M = ((M : ℝ) + 1) * ((M : ℝ) ^ 2 - 1) / 12 := by
  rw [covW, mw1 hM, mw2 hM, mw3 hM]; ring

theorem varW2_closed {M : ℕ} (hM : 1 ≤ M) :
    varW2 M = ((M : ℝ) + 1) * (2 * M + 1) * (3 * M ^ 2 + 3 * M - 1) / 30 - (((M : ℝ) + 1) * (2 * M + 1) / 6) ^ 2 := by
  rw [varW2, mw2 hM, mw4 hM]

theorem tendsto_inv_nat : Tendsto (fun M : ℕ => ((M : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- `κ_M` in the variable `x = 1/M`. -/
noncomputable def kapX (x : ℝ) : ℝ := 3 * (3 + 3 * x - x ^ 2) / (10 * (1 + x) * (2 + x)) - 1 / 4

theorem kapB_eq {M : ℕ} (hM : 1 ≤ M) : kapB M = kapX ((M : ℝ)⁻¹) := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hM2 : 2 * (M : ℝ) + 1 ≠ 0 := by positivity
  rw [kapB, varW2, mw2 hM, mw4 hM, kapX]
  field_simp
  ring

/-- **Proposition B′, the limit of `κ`**: `κ_M → 1/5` as `M → ∞`. -/
theorem kapB_tendsto : Tendsto kapB atTop (𝓝 (1 / 5)) := by
  have hc : ContinuousAt kapX 0 := by unfold kapX; fun_prop (disch := norm_num)
  have h0 : kapX 0 = 1 / 5 := by norm_num [kapX]
  rw [← h0]
  refine (hc.tendsto.comp tendsto_inv_nat).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (kapB_eq hM).symm

/-- The correction `κ − κ_c = Cov(w², w)²/(Var(w)·4(E w²)²)` in the variable `x = 1/M`. -/
noncomputable def kapcX (x : ℝ) : ℝ := kapX x - 3 * (1 - x ^ 2) / (4 * (2 + x) ^ 2)

theorem kapcB_eq {M : ℕ} (hM : 2 ≤ M) : kapcB M = kapcX ((M : ℝ)⁻¹) := by
  have h1 : (1 : ℕ) ≤ M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hM2 : 2 * (M : ℝ) + 1 ≠ 0 := by positivity
  have hv : (M : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  rw [kapcX, kapX, kapcB, AB, covW_closed h1, varW_closed h1, varW2_closed h1, mw2 h1]
  field_simp
  ring

/-- **Proposition B′, the limit of `κ_c`**: `κ_{c,M} → 1/80` as `M → ∞`. -/
theorem kapcB_tendsto : Tendsto kapcB atTop (𝓝 (1 / 80)) := by
  have hc : ContinuousAt kapcX 0 := by unfold kapcX kapX; fun_prop (disch := norm_num)
  have h0 : kapcX 0 = 1 / 80 := by norm_num [kapcX, kapX]
  rw [← h0]
  refine (hc.tendsto.comp tendsto_inv_nat).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  exact (kapcB_eq hM).symm

/-- `A/M⁴` in the variable `x = 1/M`. -/
noncomputable def aX (x : ℝ) : ℝ :=
  (1 + x) * (2 + x) * (3 + 3 * x - x ^ 2) / 30 - ((1 + x) * (2 + x) / 6) ^ 2 - (1 + x) ^ 2 * (1 - x ^ 2) / 12

/-- `γ_M` in the variable `x = 1/M`. -/
noncomputable def gamX (x : ℝ) : ℝ :=
  -(√((1 - x ^ 2) / 12) * (108 * aX x / ((2 + x) ^ 3 * (1 + x) ^ 2)))

theorem gamB_eq {M : ℕ} (hM : 2 ≤ M) : gamB M = gamX ((M : ℝ)⁻¹) := by
  have h1 : (1 : ℕ) ≤ M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hMp : (0 : ℝ) < M := by positivity
  have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hM2 : 2 * (M : ℝ) + 1 ≠ 0 := by positivity
  have hv : (M : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hsig : sig2 M = (M : ℝ) ^ 2 * ((1 - ((M : ℝ)⁻¹) ^ 2) / 12) := by
    rw [sig2]; field_simp
  have hsq : √(sig2 M) = (M : ℝ) * √((1 - ((M : ℝ)⁻¹) ^ 2) / 12) := by
    rw [hsig, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMp.le]
  rw [gamB, BB_eq_zero hM, hsq, gamX, aX, betaB, AB, covW_closed h1, varW_closed h1, varW2_closed h1, mw2 h1]
  generalize √((1 - ((M : ℝ)⁻¹) ^ 2) / 12) = s
  field_simp
  ring

/-- **Proposition B′, the limit of `γ`**: `γ_M → −√3/80` as `M → ∞`. -/
theorem gamB_tendsto : Tendsto gamB atTop (𝓝 (-(√3 / 80))) := by
  have hc : ContinuousAt gamX 0 := by unfold gamX aX; fun_prop (disch := norm_num)
  have hs : √((1 - (0 : ℝ) ^ 2) / 12) = √3 / 6 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h0 : gamX 0 = -(√3 / 80) := by
    rw [gamX, hs]; norm_num [aX]; ring
  rw [← h0]
  refine (hc.tendsto.comp tendsto_inv_nat).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  exact (gamB_eq hM).symm

end ArcsAlgo.LLT
