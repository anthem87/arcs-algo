module

public import ArcsAlgo.EdgeVanishC
public import ArcsAlgo.EdgeShoulderC
public import ArcsAlgo.EdgeE2
set_option autoImplicit false

/-!
# Remark (the formula of Proposition C), the vanishing factor (paper §3.5)

* `thmC2_vanish` (`𝒱(a/q) = {w₀}`, `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`): the absolute form of Theorem E(2) with the
  arc term `e(−Ta/q)·w₀·Ĥ′(T)` built at `a/q`: core (`thmC_vanish`), shoulders (`thmC_shoulder`), lobes
  (`thmE2_lobes`). No relative form is claimed in this case (the arc term vanishes as `z → 0`).

The only hypothesis is `SiegelWalfisz`; the bound on `ν_{a/q}` is an antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

set_option maxHeartbeats 4000000 in
/-- **Remark (the formula of Proposition C)**, case `𝒱(a/q) = {w₀}` (paper §3.5), the absolute form of
Theorem E(2): fix `B > 0`, `0 < ε < 1/8`, `C_ν > 0`, `δ > 0`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`,
`|ν_{a/q}| ≤ C_νN^{3/2+ε/2}` and every `T`, with the arc term `𝒜_{a/q}(T) = e(−Ta/q)·w₀·Ĥ′(T)` built from the
cumulants of `G̃` at `a/q`:
`|R_{a/q}(T) − 𝒜_{a/q}(T)| ≤ |G(a/q)|(w₀e^{ν²/(2s̃²)}N^{−3/2+7ε}/s̃² + w₀e^{−N^{2ε}/(16384 log N)}
  + 4e^{4ν²/S₂}e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`.
No relative form is claimed: the arc term `≈ −w₀zφ(z)/s̃²` vanishes as `z → 0`. -/
theorem thmC2_vanish (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ w₀ ∈ WN N, vanish q a w₀ → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) → ∀ T : ℝ,
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ 0 T) T)‖ ≤
          ‖Gw (WN N) q a ((a : ℝ) / q)‖ *
            (w₀ * (Real.exp (nuW (WN N) q a ^ 2 / (2 * sV N q a w₀ 0 ^ 2)) *
                ((N : ℝ) ^ (-(3 / 2 : ℝ) + 7 * ε) / sV N q a w₀ 0 ^ 2)) +
              w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
              4 * Real.exp (4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a) *
                Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  obtain ⟨N₁, hcore⟩ := thmC_vanish hSW hB hε0 hε hCν
  obtain ⟨N₃, hsh⟩ := thmC_shoulder hSW hB hε0 hε hCν
  obtain ⟨N₄, hlo⟩ := thmE2_lobes hSW hB hδ
  refine ⟨N₁ + N₃ + N₄ + 2, fun N hN q a hq hqP ha w₀ hw₀ hv hnu T => ?_⟩
  obtain ⟨-, -, hc⟩ := hcore N (by omega) q a hq hqP ha w₀ hw₀ hv hnu
  have hc0 := hc T
  have hs := hsh N (by omega) q a hq hqP ha hnu T
  have hl := hlo N (by omega) q a hq hqP ha T
  dsimp only at hs hl
  obtain ⟨-, -, hsR, hsL⟩ := hs
  obtain ⟨-, hlR, hlL⟩ := hl
  set θc := (a : ℝ) / q with hθc
  set τ₀ := (N : ℝ) ^ (-(3 / 2 : ℝ) + ε)
  set δθ := 1 / (2 * q * (N : ℝ))
  set G := ‖Gw (WN N) q a θc‖
  set Ev := Real.exp (4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a)
  set e2 := Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))
  set Lb := 2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)
  set Am := ee (-(T * θc)) * (w₀ * deriv (fun T => HhatV N q a w₀ 0 T) T)
  have hsplit := Rarc_split B N q a T (θc - δθ) (θc - τ₀ / (2 * π)) (θc + τ₀ / (2 * π)) (θc + δθ)
  have hRc : (∫ θ in (θc - τ₀ / (2 * π))..(θc + τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))) =
      Rcore N θc τ₀ T := rfl
  rw [hRc] at hsplit
  rw [hsplit]
  set I1 := ∫ θ in (θc - PP B N / (q * N))..(θc - δθ), FW (WN N) θ * ee (-(T * θ))
  set I2 := ∫ θ in (θc - δθ)..(θc - τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))
  set I4 := ∫ θ in (θc + τ₀ / (2 * π))..(θc + δθ), FW (WN N) θ * ee (-(T * θ))
  set I5 := ∫ θ in (θc + δθ)..(θc + PP B N / (q * N)), FW (WN N) θ * ee (-(T * θ))
  have e : I1 + I2 + Rcore N θc τ₀ T + I4 + I5 - Am = (Rcore N θc τ₀ T - Am) + I2 + I4 + I1 + I5 := by ring
  rw [e]
  have n1 := norm_add_le ((Rcore N θc τ₀ T - Am) + I2 + I4 + I1) I5
  have n2 := norm_add_le ((Rcore N θc τ₀ T - Am) + I2 + I4) I1
  have n3 := norm_add_le ((Rcore N θc τ₀ T - Am) + I2) I4
  have n4 := norm_add_le (Rcore N θc τ₀ T - Am) I2
  have hG0 : 0 ≤ G := norm_nonneg _
  nlinarith

end ArcsAlgo.Core
