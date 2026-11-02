module

public import ArcsAlgo.ThmE3
set_option autoImplicit false

/-!
# Theorem E(2), the lobes (paper §3.5)

* `Aq_ge`: `A_q(X) ≥ −τ(q)κ/X` (each divisor term of the Möbius form is `≤ κ/(dX)` in absolute value).
* `ellq_nonneg`, `ellE_eq`: `ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q) ≥ 0`, so `ellE q = ℓ*_q`.
* `thmE2_lobes`: for `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1` and every `T`, each lobe range
  `1/(2q) ≤ |X| ≤ 𝔓/q` (`θ = a/q + X/N`, i.e. `|t| ≥ π/(qN)`) contributes
  `≤ 2^n exp((−log 2 + ℓ*_q + δ)π(N))`, by Lemma L; the range has measure `≤ 1`.

The only hypothesis is `SiegelWalfisz`.
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-- `A_q(X) ≥ −τ(q)κ/X`: each divisor term has `|X⁻¹∫₀^X G(dx + d/2)| ≤ κ/(dX)` (Lemma Q). -/
theorem Aq_ge {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 0 < X) :
    -((q.divisorsAntidiagonal.card : ℝ) * (kappa / X)) ≤ Aq q X := by
  rw [Aq_moebius hq0, ← neg_le_neg_iff, neg_neg, ← sum_neg_distrib]
  have hk := kappa_nonneg
  calc ∑ y ∈ q.divisorsAntidiagonal, -((μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X))
      ≤ ∑ _y ∈ q.divisorsAntidiagonal, kappa / X := by
        refine sum_le_sum fun y hy => ?_
        have hy2 : 0 < y.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hy)
        have hy2' : (1 : ℝ) ≤ y.2 := by exact_mod_cast hy2
        have h1 := abs_avg_Gs_le (by positivity : (0 : ℝ) < y.2) hX ((y.2 : ℝ) / 2)
        have h2 : kappa / (y.2 * X) ≤ kappa / X :=
          div_le_div_of_nonneg_left hk hX (by nlinarith)
        have hm : |(μ y.1 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        calc -((μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X))
            ≤ |(μ y.1 : ℝ) * ((∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X)| := neg_le_abs _
          _ = |(μ y.1 : ℝ)| * |(∫ x in (0 : ℝ)..X, Gs (y.2 * x + y.2 / 2)) / X| := abs_mul _ _
          _ ≤ 1 * (kappa / (y.2 * X)) := mul_le_mul hm h1 (abs_nonneg _) zero_le_one
          _ ≤ kappa / X := by rw [one_mul]; exact h2
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- `ℓ*_q = sup_{X ≥ X₀} A_q(X)/φ(q) ≥ 0`, since `A_q(X) → 0`. -/
theorem ellq_nonneg {q : ℕ} (hq0 : 0 < q) {X₀ : ℝ} (hX₀ : 0 < X₀) : 0 ≤ ellq q X₀ := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  set c : ℝ := q.divisorsAntidiagonal.card * kappa
  have hc : 0 ≤ c := mul_nonneg (by positivity) kappa_nonneg
  by_contra hneg
  push_neg at hneg
  set s := ellq q X₀ / 2
  have hs : s < 0 := by simp only [s]; linarith
  -- take `X ≥ X₀` with `c/X < −sφ`
  set X := max X₀ (c / (-s * q.totient) + 1)
  have hX0 : 0 < X := lt_of_lt_of_le hX₀ (le_max_left _ _)
  have hsφ : 0 < -s * q.totient := mul_pos (by linarith) hφ
  have hcX : c / X < -s * q.totient := by
    rw [div_lt_iff₀ hX0]
    have h1 : c / (-s * q.totient) + 1 ≤ X := le_max_right _ _
    have h2 : c < (c / (-s * q.totient) + 1) * (-s * q.totient) := by
      rw [add_mul, div_mul_cancel₀ _ hsφ.ne']; linarith
    nlinarith
  have hA := Aq_ge hq0 hX0
  have e : (q.divisorsAntidiagonal.card : ℝ) * (kappa / X) = c / X := by simp only [c]; ring
  rw [e] at hA
  have hle := le_ellq (Nat.pos_iff_ne_zero.mp hq0) hX₀ (le_max_left X₀ _ : X₀ ≤ X)
  have : s < Aq q X / q.totient := by
    rw [lt_div_iff₀ hφ]; linarith
  have : ellq q X₀ < s := by simp only [s]; linarith
  linarith

/-- `ellE q = ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q)`: the `max 0` is redundant. -/
theorem ellE_eq {q : ℕ} (hq0 : 0 < q) : ellE q = ellq q (1 / (2 * q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  exact max_eq_right (ellq_nonneg hq0 (by positivity))

set_option maxHeartbeats 4000000 in
/-- **Theorem E(2), the lobes** (paper §3.5): fix `B > 0` and `δ > 0`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`,
`(a, q) = 1` and every `T`, both lobe ranges `1/(2q) ≤ |X| ≤ 𝔓/q` (`θ = a/q + X/N`, i.e.
`π/(qN) ≤ |t| ≤ 2π𝔓/(qN)`) contribute `≤ 2^n exp((−log 2 + ℓ*_q + δ)π(N))`, with
`ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q)`. Lemma L; no condition on `q ∈ 𝔈` is needed. The only
hypothesis is Siegel–Walfisz. -/
theorem thmE2_lobes (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q → ∀ T : ℝ,
      let δθ := 1 / (2 * q * (N : ℝ))
      let ρ := PP B N / (q * N)
      let ℓs := ellq q (1 / (2 * q))
      δθ ≤ ρ ∧
      ‖∫ θ in ((a : ℝ) / q + δθ)..((a : ℝ) / q + ρ), FW (WN N) θ * ee (-(T * θ))‖ ≤
        2 ^ (WN N).card * Real.exp ((-Real.log 2 + ℓs + δ) * Nat.primeCounting N) ∧
      ‖∫ θ in ((a : ℝ) / q - ρ)..((a : ℝ) / q - δθ), FW (WN N) θ * ee (-(T * θ))‖ ≤
        2 ^ (WN N).card * Real.exp ((-Real.log 2 + ℓs + δ) * Nat.primeCounting N) := by
  have hl2 := log_two_pos'
  obtain ⟨N₁, hLL⟩ := lemmaL hSW hB
  obtain ⟨N₃, hup⟩ := pi_upper hSW (δ := δ / (8 * Real.log 2)) (by positivity)
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp B (by norm_num : (0 : ℝ) < 1 / 2) 2
  obtain ⟨K₄, hK₄, hk4⟩ := ev_poly_exp B one_pos 1
  obtain ⟨N₂, hlow⟩ := pi_lower hSW
  set K := max (max K₃ K₄) (24 / δ)
  refine ⟨N₁ + N₂ + N₃ + ⌈Real.exp K⌉₊ + 16, fun N hN q a hq hqP ha T => ?_⟩
  intro δθ ρ ℓs
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : K ≤ L := by
    have : Real.exp K ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp K⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKL
  have hL4 : K₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKL
  have hL5 : 24 / δ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₃ hL3
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set P := (Nat.primeCounting N : ℝ) with hPdef
  have hPup : P ≤ (1 + δ / (8 * Real.log 2)) * Nr / L := hup N (by omega)
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hℓ2 : ℓs ≤ Real.log 2 := ellq_le_log2 (by omega) (by positivity)
  have hℓ0 : 0 ≤ ℓs := ellq_nonneg (by omega) (by positivity)
  set n := (WN N).card
  have hLB : (q : ℝ) ≤ L ^ B := hqP
  set u := Nr / L with hu
  have hu0 : 0 ≤ u := by positivity
  -- `2 L^B ≤ √N`, hence `N^{−1/2} ≤ 1/(2q)`
  have hsqN : 2 * L ^ B ≤ Nr ^ (1 / 2 : ℝ) := by
    have h1 := hk3 L hL3
    have hr : Nr ^ (1 / 2 : ℝ) = Real.exp (L / 2) := by
      rw [Real.rpow_def_of_pos hNpos, ← hLdef]; ring_nf
    rw [hr]; exact h1.trans (Real.exp_le_exp.mpr (by linarith))
  have hNhalf : Nr ^ (-(1 / 2 : ℝ)) ≤ 1 / (2 * q) := by
    rw [Real.rpow_neg hNpos.le, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  have hδρ : δθ ≤ ρ := by
    simp only [δθ, ρ]; unfold PP; rw [← hNr, ← hLdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hq0 hNpos]
  -- the pointwise bound on the lobes (Lemma L)
  have hpt : ∀ θ : ℝ, δθ ≤ |θ - a / q| → |θ - a / q| ≤ ρ →
      ‖FW (WN N) θ‖ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓs + δ) * P) := by
    intro θ hθ1 hθ2
    set X := Nr * (θ - a / q) with hX
    have hθX : θ = a / q + X / Nr := by rw [hX]; field_simp; ring
    have hXabs : |X| = Nr * |θ - a / q| := by rw [hX, abs_mul, abs_of_pos hNpos]
    have hXle : |X| ≤ L ^ B / q := by
      rw [hXabs]
      have := mul_le_mul_of_nonneg_left hθ2 hNpos.le
      have e : Nr * ρ = L ^ B / q := by simp only [ρ]; unfold PP; rw [← hNr, ← hLdef]; field_simp
      linarith
    have hXge : 1 / (2 * q) ≤ |X| := by
      rw [hXabs]
      have := mul_le_mul_of_nonneg_left hθ1 hNpos.le
      have e : Nr * δθ = 1 / (2 * q) := by simp only [δθ]; rw [← hNr]; field_simp
      linarith
    have hXlo : Nr ^ (-(1 / 2 : ℝ)) ≤ |X| := hNhalf.trans hXge
    have h1 := hLL N (by omega) q a hq hqP ha X hXlo hXle
    rw [hθX]
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    have hA : Aq q |X| / q.totient ≤ ℓs :=
      le_ellq (by omega) (by positivity) hXge
    have s1 : Nr / L * (Aq q |X| / q.totient - Real.log 2) ≤ u * (ℓs - Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0
    set D := Real.log 2 - ℓs
    have hD0 : 0 ≤ D := by linarith
    have hPup' : P ≤ u + δ / (8 * Real.log 2) * u := by
      have : (1 + δ / (8 * Real.log 2)) * Nr / L = u + δ / (8 * Real.log 2) * u := by rw [hu]; ring
      linarith
    have hP0 : 0 ≤ P := by positivity
    have s2 : D * P ≤ D * u + D * (δ / (8 * Real.log 2) * u) := by
      have := mul_le_mul_of_nonneg_left hPup' hD0; linarith
    have s3 : D * (δ / (8 * Real.log 2) * u) ≤ δ / 8 * u := by
      have h1 : D * (δ / (8 * Real.log 2) * u) ≤ Real.log 2 * (δ / (8 * Real.log 2) * u) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h2 : Real.log 2 * (δ / (8 * Real.log 2) * u) = δ / 8 * u := by field_simp
      linarith
    have s4 : 3 * Nr / L ^ 2 ≤ δ / 8 * u := by
      have e : 3 * Nr / L ^ 2 = 3 / L * u := by rw [hu]; field_simp
      have h6 : 3 / L ≤ δ / 8 := by
        rw [div_le_iff₀ hL0]; rw [div_le_iff₀ hδ] at hL5; nlinarith
      rw [e]; exact mul_le_mul_of_nonneg_right h6 hu0
    -- `u ≤ P`-free form: `−Du + δu/4 ≤ (−D + δ)P` needs `u ≤ P(1 + …)`; use `D u ≥ D P − δu/8`
    have hupP : u ≤ 2 * P := by
      have h := hlow N (by omega)
      have : Nr / (2 * L) = u / 2 := by rw [hu]; field_simp
      rw [← hNr, ← hLdef, ← hPdef, this] at h; linarith
    have e : u * (ℓs - Real.log 2) = -(D * u) := by simp only [D]; ring
    nlinarith
  -- integrate over the two lobes
  have hlen : ρ - δθ ≤ 1 := by
    have : ρ ≤ 1 := by
      simp only [ρ]; unfold PP; rw [← hNr, ← hLdef, div_le_one (by positivity)]
      have hPN : L ^ B ≤ Nr := by
        have := hk4 L hL4; rw [one_mul] at this
        exact this.trans (by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
      nlinarith
    have : 0 < δθ := by simp only [δθ]; positivity
    linarith
  have hbd : 0 ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓs + δ) * P) := by positivity
  refine ⟨hδρ, ?_, ?_⟩
  · have hb : ∀ θ ∈ Set.uIoc ((a : ℝ) / q + δθ) ((a : ℝ) / q + ρ),
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓs + δ) * P) := by
      intro θ hθ
      rw [Set.uIoc_of_le (by linarith)] at hθ
      rw [norm_mul, norm_ee, mul_one]
      have hδ0 : 0 < δθ := by simp only [δθ]; positivity
      exact hpt θ (by rw [abs_of_pos (by linarith [hθ.1])]; linarith [hθ.1])
        (by rw [abs_of_pos (by linarith [hθ.1])]; linarith [hθ.2])
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [show (a : ℝ) / q + ρ - ((a : ℝ) / q + δθ) = ρ - δθ by ring, abs_of_nonneg (by linarith)]
    nlinarith
  · have hb : ∀ θ ∈ Set.uIoc ((a : ℝ) / q - ρ) ((a : ℝ) / q - δθ),
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓs + δ) * P) := by
      intro θ hθ
      rw [Set.uIoc_of_le (by linarith)] at hθ
      rw [norm_mul, norm_ee, mul_one]
      have hδ0 : 0 < δθ := by simp only [δθ]; positivity
      exact hpt θ (by rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.2])
        (by rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.1])
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [show (a : ℝ) / q - δθ - ((a : ℝ) / q - ρ) = ρ - δθ by ring, abs_of_nonneg (by linarith)]
    nlinarith

end ArcsAlgo.Core
