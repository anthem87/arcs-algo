module

public import ArcsAlgo.EdgeShoulder
set_option autoImplicit false

/-!
# The shoulder of an arc around its centre (paper §3.5, Remark (the formula of Proposition C))

* `thmC_shoulder`: for `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}` the peak `t*` lies within `τ₀/2` of `0`, and each range
  `τ₀ < |t| < π/(qN)` contributes `≤ 2|G(a/q)|e^{4ν²/S₂}e^{−N^{2ε}/(2048 log N)}`, uniformly in `T`.

Hypotheses: `SiegelWalfisz`; the bound on `ν_{a/q}` is an explicit antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

set_option maxHeartbeats 8000000 in
/-- **The shoulder at the centre** (Remark (the formula of Proposition C)): fix `B > 0`, `0 < ε < 1/8`,
`C_ν > 0`, `τ₀ = N^{−3/2+ε}`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}` and every
`T`, the two ranges `τ₀ < |t|`, `|t| < π/(qN)` (`t = 2π(θ − a/q)`) each contribute
`≤ 2|G(a/q)|e^{4ν²/S₂}e^{−N^{2ε}/(2048 log N)}`: the peak `t*` of Lemma W lies within `τ₀/2` of `0`. -/
theorem thmC_shoulder (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) → ∀ T : ℝ,
        let τ₀ := (N : ℝ) ^ (-(3 / 2 : ℝ) + ε)
        let δθ := 1 / (2 * q * (N : ℝ))
        let Gc := ‖Gw (WN N) q a ((a : ℝ) / q)‖ * Real.exp (4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a)
        (a : ℝ) / q + τ₀ / (2 * π) ≤ (a : ℝ) / q + δθ ∧ (a : ℝ) / q - δθ ≤ (a : ℝ) / q - τ₀ / (2 * π) ∧
        ‖∫ θ in ((a : ℝ) / q + τ₀ / (2 * π))..((a : ℝ) / q + δθ), FW (WN N) θ * ee (-(T * θ))‖ ≤
          2 * Gc * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N)) ∧
        ‖∫ θ in ((a : ℝ) / q - δθ)..((a : ℝ) / q - τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))‖ ≤
          2 * Gc * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N)) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp 1 (by positivity : 0 < ε / 2) (512 * Cν)
  set Kmax := max K₂ K₃
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha hnu T => ?_⟩
  obtain ⟨-, hS2pos, hwin, -, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  intro τ₀ δθ Gc
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL2 : K₂ ≤ L := le_trans (le_max_left _ _) hKL
  have hL3 : K₃ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₂ hL2
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hpi := Real.pi_pos
  have h2pi := Real.two_le_pi
  have hq1 : 1 ≤ q := by omega
  have hWN : ∀ w ∈ WN N, w ≤ N := fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)
  -- the peak
  obtain ⟨ts, hts, hF, -, -, hFts⟩ := peak (W := WN N) (a := a) hq1 (by omega) hWN hS2pos hwin
  -- `τ₀ ≤ 1/(qN)`
  have hτe : τ₀ = Real.exp ((-(3 / 2) + ε) * L) := hrp _
  have hτ0 : 0 < τ₀ := by rw [hτe]; exact Real.exp_pos _
  have hτq : τ₀ ≤ 1 / (q * Nr) := by
    have h := hk2 L hL2
    have h' : 16 * (q : ℝ) ≤ Real.exp ((1 / 2 - ε) * L) :=
      (by nlinarith : 16 * (q : ℝ) ≤ 16 * L ^ B).trans (h.trans (Real.exp_le_exp.mpr (by nlinarith)))
    have e : Nr * τ₀ = Real.exp ((-(1 / 2) + ε) * L) := by
      rw [hτe, ← hexpL, ← Real.exp_add]; congr 1; ring
    have he : Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have : q * (Nr * τ₀) ≤ 1 := by
      rw [e]; nlinarith [Real.exp_pos ((-(1 / 2) + ε) * L)]
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- `|t*| ≤ τ₀/2`
  have htsτ : |ts| ≤ τ₀ / 2 := by
    refine hts.trans ?_
    have hS : Real.exp (3 * L) / (64 * L) ≤ S2W (WN N) q a := by
      have e : Nr ^ 3 = Real.exp (3 * L) := by rw [← hexpL, ← Real.exp_nat_mul]; norm_num
      rw [← e]; exact hS2lo
    have hnu' : |nuW (WN N) q a| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L) := by rw [← hrp]; exact hnu
    have h3 := hk3 L hL3; rw [Real.rpow_one] at h3
    have h3' : 512 * Cν * L ≤ Real.exp (ε / 2 * L) := h3.trans (Real.exp_le_exp.mpr (by nlinarith))
    rw [div_le_iff₀ (by positivity : 0 < S2W (WN N) q a)]
    have hS' : τ₀ / 2 * (Real.exp (3 * L) / (64 * L)) ≤ τ₀ / 2 * S2W (WN N) q a :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have e2 : τ₀ / 2 * (Real.exp (3 * L) / (64 * L)) =
        Real.exp (ε / 2 * L) * Real.exp ((3 / 2 + ε / 2) * L) / (128 * L) := by
      rw [hτe, show Real.exp (ε / 2 * L) * Real.exp ((3 / 2 + ε / 2) * L) =
          Real.exp ((-(3 / 2) + ε) * L) * Real.exp (3 * L) by rw [← Real.exp_add, ← Real.exp_add]; ring_nf]
      field_simp; ring
    have h4 : 4 * (Cν * Real.exp ((3 / 2 + ε / 2) * L)) ≤
        Real.exp (ε / 2 * L) * Real.exp ((3 / 2 + ε / 2) * L) / (128 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right h3' (Real.exp_pos ((3 / 2 + ε / 2) * L)).le
      nlinarith [Real.exp_pos ((3 / 2 + ε / 2) * L)]
    nlinarith [abs_nonneg (nuW (WN N) q a)]
  have hwq : 2 / (q * Nr) ≤ π / (q * Nr) := div_le_div_of_nonneg_right h2pi (by positivity)
  have htsq : |ts| ≤ 1 / (q * Nr) := by linarith
  have htsw : |ts| < π / (q * Nr) := lt_of_le_of_lt htsq (lt_of_lt_of_le
    (by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num) hwq)
  -- `|G(θ*)| ≤ |G(a/q)|e^{4ν²/S₂}`
  have hGs : ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ ≤ Gc := by
    have h0 : |(0 : ℝ)| < π / (q * Nr) := by rw [abs_zero]; positivity
    have e0 := norm_Gw_eq (a := a) hq1 (by omega : 1 ≤ N) h0
    rw [zero_div, add_zero] at e0
    rw [norm_Gw_eq hq1 (by omega) htsw]
    simp only [Gc]; rw [e0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hFts
  -- `S₂(τ₀/2)²/8 ≥ N^{2ε}/(2048 L)`
  have hSτ : Nr ^ (2 * ε) / (2048 * L) ≤ S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8 := by
    have h1 := hS2lo
    have e : Nr ^ 3 / (64 * L) * (τ₀ / 2) ^ 2 / 8 = Nr ^ (2 * ε) / (2048 * L) := by
      rw [div_pow, hτe, hrp, ← Real.exp_nat_mul, show Nr ^ 3 = Real.exp (3 * L) by
        rw [← hexpL, ← Real.exp_nat_mul]; norm_num,
        show 2 * ε * L = 3 * L + ((2 : ℕ) : ℝ) * ((-(3 / 2) + ε) * L) by push_cast; ring, Real.exp_add]
      field_simp; ring
    rw [← e]
    gcongr
  have hdecay : 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ * Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) ≤
      2 * Gc * Real.exp (-(Nr ^ (2 * ε)) / (2048 * L)) := by
    gcongr
    rw [neg_div]; linarith
  -- the pointwise bound on both ranges
  have hpt : ∀ θ : ℝ, |θ - a / q| < δθ → τ₀ ≤ |2 * π * (θ - a / q)| →
      ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
        Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) := by
    intro θ hθ hd
    rw [norm_mul, norm_ee, mul_one]
    have hθe : θ = a / q + (2 * π * (θ - a / q)) / (2 * π) := by field_simp; ring
    have hw : |2 * π * (θ - a / q)| < π / (q * Nr) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have : 2 * π * δθ = π / (q * Nr) := by simp only [δθ]; field_simp
      rw [← this]; exact mul_lt_mul_of_pos_left hθ (by positivity)
    have hd' : τ₀ / 2 ≤ |2 * π * (θ - a / q) - ts| := by
      have := abs_sub_abs_le_abs_sub (2 * π * (θ - a / q)) ts
      linarith
    rw [hθe]
    exact shoulder_pt hq ha (by omega) htsw hF hw (by positivity) hd'
  have hδ1 : 2 * δθ ≤ 1 := by
    simp only [δθ]; rw [show 2 * (1 / (2 * q * Nr)) = 1 / (q * Nr) by field_simp, div_le_one (by positivity)]
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hδ0 : 0 < δθ := by simp only [δθ]; positivity
  have hk : τ₀ / (2 * π) ≤ δθ := by
    have e : δθ = (π / (q * Nr)) / (2 * π) := by simp only [δθ]; field_simp
    rw [e]
    have h12 : 1 / (q * Nr) ≤ 2 / (q * Nr) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have h1 : τ₀ ≤ π / (q * Nr) := by linarith
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hτ2 : 0 < τ₀ / (2 * π) := by positivity
  have hR1 : (a : ℝ) / q + τ₀ / (2 * π) ≤ a / q + δθ := by linarith
  have hL1' : (a : ℝ) / q - δθ ≤ a / q - τ₀ / (2 * π) := by linarith
  have hC0 : 0 ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
      Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) := by positivity
  refine ⟨hR1, hL1', ?_, ?_⟩
  · -- the right range
    have hb : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc ((a : ℝ) / q + τ₀ / (2 * π)) (a / q + δθ) →
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
          Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) := by
      filter_upwards [Measure.ae_ne volume ((a : ℝ) / q + δθ)] with θ hne hθ
      rw [Set.uIoc_of_le hR1] at hθ
      have hlt : θ < a / q + δθ := lt_of_le_of_ne hθ.2 hne
      refine hpt θ (abs_lt.mpr ⟨by linarith [hθ.1], by linarith⟩) ?_
      have h1 : τ₀ / (2 * π) < θ - a / q := by linarith [hθ.1]
      rw [div_lt_iff₀ (by positivity)] at h1
      have hpos : 0 < 2 * π * (θ - a / q) := by nlinarith
      rw [abs_of_pos hpos]; linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae hb).trans ?_
    refine le_trans ?_ hdecay
    have : |a / q + δθ - ((a : ℝ) / q + τ₀ / (2 * π))| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc _ ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
            Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) * 1 := mul_le_mul_of_nonneg_left this hC0
      _ = _ := mul_one _
  · -- the left range
    have hb : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc ((a : ℝ) / q - δθ) (a / q - τ₀ / (2 * π)) →
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
          Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) := by
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      rw [Set.uIoc_of_le hL1'] at hθ
      refine hpt θ (abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) ?_
      have h1 : θ - a / q ≤ -(τ₀ / (2 * π)) := by linarith [hθ.2]
      have h2 : 2 * π * (θ - a / q) ≤ 2 * π * (-(τ₀ / (2 * π))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      have e2 : 2 * π * (-(τ₀ / (2 * π))) = -τ₀ := by field_simp
      rw [abs_of_neg (by linarith)]; linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae hb).trans ?_
    refine le_trans ?_ hdecay
    have : |(a : ℝ) / q - τ₀ / (2 * π) - (a / q - δθ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc _ ≤ 2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
            Real.exp (-(S2W (WN N) q a * (τ₀ / 2) ^ 2 / 8)) * 1 := mul_le_mul_of_nonneg_left this hC0
      _ = _ := mul_one _

end ArcsAlgo.Core
