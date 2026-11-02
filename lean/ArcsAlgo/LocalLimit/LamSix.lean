module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false

/-!
# The sixth-order remainder of `log(sin t / t)` (paper §6.2, proof of Lemma B0′)

`Λ(t) = log(sin t / t) + t²/6 = −t⁴/180 + Λ₆(t)`. Euler's product `sin πx / πx = Π (1 − x²/n²)`
gives `Λ₆(πx) = Σ_n ψ(x²/n²)` with `ψ(u) = log(1 − u) + u + u²/2`, and Taylor's bound for the
logarithm gives `|ψ(u)| ≤ 0.4128 u³` for `u ≤ 1/4` and `|ψ(u)| ≤ 0.3532 u³` for `u ≤ 1/16`. Hence
(`abs_lam6_le`) `|Λ₆(t)| ≤ 4.4·10⁻⁴ t⁶` on `(0, π/2]`. The paper uses `4.35·10⁻⁴`; the margin
is absorbed in its constant `0.19`.
-/

open Real Filter Topology Finset

@[expose] public section

namespace ArcsAlgo.LLT

noncomputable def psi (u : ℝ) : ℝ := Real.log (1 - u) + u + u ^ 2 / 2

lemma abs_psi_le_small {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 16) :
    |psi u| ≤ 0.3532 * u ^ 3 := by
  have hu : |u| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  norm_num at h
  have h5 : u ^ 5 / (1 - u) ≤ u ^ 3 / 240 := by
    rw [div_le_iff₀ (by linarith)]
    have : u ^ 2 ≤ (1 - u) / 240 := by nlinarith
    nlinarith [pow_nonneg h0 3]
  have e : psi u = (u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + Real.log (1 - u)) - u ^ 3 / 3
      - u ^ 4 / 4 := by unfold psi; ring
  rw [e]
  have h4 : u ^ 4 ≤ u ^ 3 / 16 := by nlinarith [pow_nonneg h0 3]
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [pow_nonneg h0 3, pow_nonneg h0 4]

lemma abs_psi_le_quarter {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) :
    |psi u| ≤ 0.4128 * u ^ 3 := by
  have hu : |u| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  norm_num at h
  have h3 := pow_nonneg h0 3
  have h4 : u ^ 4 ≤ u ^ 3 / 4 := by nlinarith
  have h5' : u ^ 5 ≤ u ^ 3 / 16 := by nlinarith
  have h6 : u ^ 6 ≤ u ^ 3 / 64 := by nlinarith
  have h7 : u ^ 7 ≤ u ^ 3 / 256 := by nlinarith
  have h8 : u ^ 8 / (1 - u) ≤ u ^ 3 / 768 := by
    rw [div_le_iff₀ (by linarith)]
    have : u ^ 8 ≤ u ^ 3 / 1024 := by nlinarith
    nlinarith
  have e : psi u = (u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 + u ^ 6 / 6 + u ^ 7 / 7
      + Real.log (1 - u)) - u ^ 3 / 3 - u ^ 4 / 4 - u ^ 5 / 5 - u ^ 6 / 6 - u ^ 7 / 7 := by
    unfold psi; ring
  rw [e]
  rw [abs_le] at h ⊢
  have h5n := pow_nonneg h0 5
  have h6n := pow_nonneg h0 6
  have h7n := pow_nonneg h0 7
  have h4n := pow_nonneg h0 4
  constructor <;> nlinarith

/-- `Σ_{j<N} 1/(j+2)⁶ ≤ 1/64 + (π²/6 − 5/4)/81`. -/
lemma sum_inv_pow_six_le (N : ℕ) :
    ∑ j ∈ range N, 1 / ((j : ℝ) + 2) ^ 6 ≤ 1 / 64 + (π ^ 2 / 6 - 5 / 4) / 81 := by
  have hs : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ, add_assoc, one_add_one_eq_two] using this
  have hpt : ∀ j ∈ range N, 1 / ((j : ℝ) + 2) ^ 6 ≤
      (1 / 81) * (1 / ((j : ℝ) + 2) ^ 2) + (if j = 0 then 1 / 64 - 1 / 324 else 0) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hj.ne'), add_zero]
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have h3 : (3 : ℝ) ≤ j + 2 := by linarith
      have h81 : (81 : ℝ) ≤ ((j : ℝ) + 2) ^ 4 := by
        nlinarith [pow_le_pow_left₀ (by norm_num) h3 4]
      have hp2 : (0 : ℝ) < ((j : ℝ) + 2) ^ 2 := by positivity
      have h4 : 1 / ((j : ℝ) + 2) ^ 4 ≤ 1 / 81 := one_div_le_one_div_of_le (by norm_num) h81
      calc 1 / ((j : ℝ) + 2) ^ 6 = 1 / ((j : ℝ) + 2) ^ 4 * (1 / ((j : ℝ) + 2) ^ 2) := by
            rw [one_div_mul_one_div]; ring_nf
        _ ≤ 1 / 81 * (1 / ((j : ℝ) + 2) ^ 2) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h1 : ∑ j ∈ range N, 1 / ((j : ℝ) + 2) ^ 2 ≤ π ^ 2 / 6 - 1 :=
    sum_le_hasSum _ (fun _ _ => by positivity) hs
  have h2 : ∑ j ∈ range N, (if j = 0 then (1 / 64 - 1 / 324 : ℝ) else 0) ≤ 1 / 64 - 1 / 324 := by
    rw [sum_ite_eq']; split_ifs <;> norm_num
  linarith

/-- `Λ₆(t) = log(sin t / t) + t²/6 + t⁴/180`, the remainder after the first two terms of
`log(sin t / t) = −t²/6 − t⁴/180 − t⁶/2835 − …`. -/
noncomputable def lam6 (t : ℝ) : ℝ := Real.log (Real.sin t / t) + t ^ 2 / 6 + t ^ 4 / 180

/-- `|Λ₆(t)| ≤ 4.4·10⁻⁴ t⁶` on `(0, π/2]`, from Euler's product
`sin πx / πx = Π (1 − x²/n²)`: `Λ₆(πx) = Σ_n ψ(x²/n²)` with `ψ(u) = log(1−u) + u + u²/2`. -/
theorem abs_lam6_le {t : ℝ} (ht0 : 0 < t) (ht : t ≤ π / 2) : |lam6 t| ≤ 0.00044 * t ^ 6 := by
  have hπ := Real.pi_pos
  set x := t / π with hx
  have hx0 : 0 < x := div_pos ht0 hπ
  have hx1 : x ≤ 1 / 2 := by rw [hx, div_le_iff₀ hπ]; linarith
  have htx : t = π * x := by rw [hx]; field_simp
  set u : ℕ → ℝ := fun j => x ^ 2 / ((j : ℝ) + 1) ^ 2 with hu
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hu0 : ∀ j, 0 ≤ u j := fun j => by positivity
  have hu1 : ∀ j, u j ≤ 1 / 4 := fun j => by
    simp only [hu]; rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    nlinarith
  have hsin : 0 < Real.sin t / t :=
    div_pos (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith)) ht0
  have hprod : Tendsto (fun n : ℕ => ∏ j ∈ range n, (1 - u j)) atTop
      (𝓝 (Real.sin t / t)) := by
    have h := (Real.tendsto_euler_sin_prod x).mul_const (1 / (π * x))
    rw [← htx] at h
    convert h using 1
    · funext n; rw [mul_one_div, mul_div_cancel_left₀ _ ht0.ne']
    · rw [mul_one_div]
  have hlog : Tendsto (fun n => ∑ j ∈ range n, Real.log (1 - u j)) atTop
      (𝓝 (Real.log (Real.sin t / t))) := by
    refine (((Real.continuousAt_log hsin.ne').tendsto).comp hprod).congr (fun n => ?_)
    simp only [Function.comp]
    exact Real.log_prod (fun j _ => ne_of_gt (by linarith [hu1 j]))
  have h2 : Tendsto (fun n => ∑ j ∈ range n, u j) atTop (𝓝 (t ^ 2 / 6)) := by
    have hs : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    have := (hs.mul_left (x ^ 2)).tendsto_sum_nat
    convert this using 1
    · funext n; apply sum_congr rfl; intro j _; simp only [hu]; ring
    · rw [htx]; ring_nf
  have h4 : Tendsto (fun n => ∑ j ∈ range n, u j ^ 2 / 2) atTop (𝓝 (t ^ 4 / 180)) := by
    have hs : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
    have := (hs.mul_left (x ^ 4 / 2)).tendsto_sum_nat
    convert this using 1
    · funext n; apply sum_congr rfl; intro j _; simp only [hu, div_pow, ← pow_mul]; ring
    · rw [htx]; ring_nf
  have hpsi : Tendsto (fun n => ∑ j ∈ range n, psi (u j)) atTop (𝓝 (lam6 t)) := by
    have := (hlog.add h2).add h4
    convert this using 1
    · funext n; simp only [psi, ← sum_add_distrib]
    · rfl
  set K : ℝ := 0.4128 + 0.3532 * (1 / 64 + (π ^ 2 / 6 - 5 / 4) / 81) with hK
  have hbd : ∀ n, |∑ j ∈ range n, psi (u j)| ≤ x ^ 6 * K := by
    have hK0 : 0 ≤ K := by
      have := Real.pi_gt_three
      have : (9 : ℝ) ≤ π ^ 2 := by nlinarith
      rw [hK]; nlinarith
    intro n
    rcases n with _ | m
    · simp; positivity
    rw [sum_range_succ']
    refine (abs_add_le _ _).trans ?_
    have h0 : |psi (u 0)| ≤ 0.4128 * x ^ 6 := by
      have := abs_psi_le_quarter (hu0 0) (hu1 0)
      simpa [hu, ← pow_mul] using this
    have hj : ∀ j ∈ range m, |psi (u (j + 1))| ≤ 0.3532 * (x ^ 6 * (1 / ((j : ℝ) + 2) ^ 6)) := by
      intro j _
      have e : u (j + 1) = x ^ 2 / ((j : ℝ) + 2) ^ 2 := by
        simp only [hu]; push_cast; ring
      have hsm : u (j + 1) ≤ 1 / 16 := by
        rw [e, div_le_iff₀ (by positivity)]
        have : (4 : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        nlinarith
      have := abs_psi_le_small (hu0 _) hsm
      rw [e] at this ⊢
      refine this.trans (le_of_eq ?_)
      rw [div_pow, ← pow_mul]; ring
    have hs := sum_inv_pow_six_le m
    calc |∑ j ∈ range m, psi (u (j + 1))| + |psi (u 0)|
        ≤ ∑ j ∈ range m, |psi (u (j + 1))| + |psi (u 0)| := by
          gcongr; exact abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range m, 0.3532 * (x ^ 6 * (1 / ((j : ℝ) + 2) ^ 6)) + 0.4128 * x ^ 6 := by
          gcongr with j hj'; exact hj j hj'
      _ = x ^ 6 * (0.4128 + 0.3532 * ∑ j ∈ range m, 1 / ((j : ℝ) + 2) ^ 6) := by
          rw [← mul_sum, ← mul_sum]; ring
      _ ≤ x ^ 6 * K := by
          rw [hK]; gcongr
  have hlim : |lam6 t| ≤ x ^ 6 * K :=
    le_of_tendsto' ((continuous_abs.tendsto _).comp hpsi) hbd
  refine hlim.trans ?_
  have hp6 : (3.1415 : ℝ) ^ 6 ≤ π ^ 6 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 6
  have hp2 : π ^ 2 ≤ (3.1416 : ℝ) ^ 2 := pow_le_pow_left₀ hπ.le Real.pi_lt_d4.le 2
  have hKle : K ≤ 0.00044 * π ^ 6 := by rw [hK]; norm_num at hp6 hp2 ⊢; linarith
  rw [htx, mul_pow]
  have : 0 ≤ x ^ 6 := by positivity
  nlinarith

end ArcsAlgo.LLT
