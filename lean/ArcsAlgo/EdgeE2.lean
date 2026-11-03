module

public import ArcsAlgo.EdgeVanish
public import ArcsAlgo.EdgeLobes
public import ArcsAlgo.ThmE1
set_option autoImplicit false

/-!
# Theorem E(2) assembled, and Theorem E (paper §3.5)

* `Rarc_split`: `R_{a/q}` is the sum of the lobes, the shoulders and the core.
* `thmE2`: Theorem E(2) for both cases of `𝒱(a/q)`, from `thmE2_core`, `thmE2_vanish`, `thmE2_shoulder`,
  `thmE2_lobes`; the lobe exponent is `ℓ*_q = sup_{X≥1/(2q)} A_q(X)/φ(q)`.
* `thmE`: Theorem E, parts (1), (2), (3) with a common `N₀`, for every `B > 40`; the lobe exponent
  is `ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q)` (`ellq q (1/(2q))`) in (2) and (3), as in the paper.

Hypotheses: Siegel–Walfisz; Vinogradov–Vaughan and Jackson for (1).
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical ArcsAlgo.ArcM

theorem continuous_arc (N : ℕ) (T : ℝ) : Continuous fun θ : ℝ => FW (WN N) θ * ee (-(T * θ)) := by
  unfold FW ee; fun_prop

/-- `R_{a/q}` is the sum of the five ranges: left lobe, left shoulder, core, right shoulder, right lobe. -/
theorem Rarc_split (B : ℝ) (N q a : ℕ) (T x1 x2 x3 x4 : ℝ) :
    Rarc B N q a T =
      (∫ θ in ((a : ℝ) / q - PP B N / (q * N))..x1, FW (WN N) θ * ee (-(T * θ))) +
      (∫ θ in x1..x2, FW (WN N) θ * ee (-(T * θ))) + (∫ θ in x2..x3, FW (WN N) θ * ee (-(T * θ))) +
      (∫ θ in x3..x4, FW (WN N) θ * ee (-(T * θ))) +
      (∫ θ in x4..((a : ℝ) / q + PP B N / (q * N)), FW (WN N) θ * ee (-(T * θ))) := by
  have hc := continuous_arc N T
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun θ : ℝ => FW (WN N) θ * ee (-(T * θ))) volume u v :=
    fun u v => hc.intervalIntegrable u v
  unfold Rarc
  rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]

theorem Gw_eq_FW {N q a : ℕ} (hnv : ∀ w ∈ WN N, ¬ vanish q a w) (θ : ℝ) : Gw (WN N) q a θ = FW (WN N) θ := by
  unfold Gw FW; rw [filter_true_of_mem hnv]

set_option maxHeartbeats 4000000 in
/-- **Theorem E(2) (emerging arcs)** (paper §3.5): fix `B > 0`, `0 < ε < 1/8` and `δ > 0`. For `N ≥ N₀`,
`3 ≤ q ≤ 𝔓`, `q ∈ 𝔈`, `(a, q) = 1`, the peak `t*` of Lemma W and every `T`, with `θ* = a/q + t*/(2π)`
and `ℓ*_q = sup_{X≥1/(2q)} A_q(X)/φ(q)`:
* if `𝒱(a/q) = ∅`: `|R_{a/q}(T) − e(−Ta/q)Ĥ(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + 5e^{−N^{2ε}/(2048 log N)}) +
  2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`;
* if `𝒱(a/q) = {w₀}`: `|R_{a/q}(T) − e(−Ta/q)·w₀·Ĥ′(T)| ≤ |G(θ*)|(Ω N^{−3/2+2ε}/s̃* + w₀e^{−N^{2ε}/(16384 log N)} +
  4e^{−N^{2ε}/(512 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`, `Ω = w₀(|t*| + 1/s̃*)`, `Ĥ` built from `G̃`
  with its exact cumulants (`thmE2_vanish`).
The terms `e^{−cN^{2ε}/log N}|G(θ*)|` (Gaussian tail, shoulder) are the paper's, absorbed there in
`O(Ω|G(θ*)|N^{−3/2+2ε}/s*)`. The hypothesis `q ∈ 𝔈` is the paper's; the proof does not use it.
The only hypothesis is Siegel–Walfisz. -/
theorem thmE2 (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((∀ w ∈ WN N, ¬ vanish q a w) →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sS N ((a : ℝ) / q + ts / (2 * π)) +
                5 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))) ∧
        (∀ w₀ ∈ WN N, vanish q a w₀ →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              (w₀ * (|ts| + 1 / sV N q a w₀ ts) * ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sV N q a w₀ ts) +
                w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
                4 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))) := by
  obtain ⟨N₁, hcore⟩ := thmE2_core hSW hB hε0 hε
  obtain ⟨N₂, hvan⟩ := thmE2_vanish hSW hB hε0 hε
  obtain ⟨N₃, hsh⟩ := thmE2_shoulder hSW hB hε0 hε
  obtain ⟨N₄, hlo⟩ := thmE2_lobes hSW hB hδ
  refine ⟨N₁ + N₂ + N₃ + N₄ + 2, fun N hN q a hq hqP _he ha ts hts hF T => ?_⟩
  have hs := hsh N (by omega) q a hq hqP ha ts hts hF T
  have hl := hlo N (by omega) q a hq hqP ha T
  dsimp only at hs hl
  obtain ⟨-, -, hsR, hsL⟩ := hs
  obtain ⟨-, hlR, hlL⟩ := hl
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  set τ₀ := (N : ℝ) ^ (-(3 / 2 : ℝ) + ε)
  set G := ‖Gw (WN N) q a θs‖
  set E5 := Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N))
  set Lb := 2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)
  have hsplit := Rarc_split B N q a T ((a : ℝ) / q - 1 / (2 * q * (N : ℝ))) (θs - τ₀ / (2 * π))
    (θs + τ₀ / (2 * π)) ((a : ℝ) / q + 1 / (2 * q * (N : ℝ)))
  have hRc : (∫ θ in (θs - τ₀ / (2 * π))..(θs + τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))) = Rcore N θs τ₀ T := rfl
  rw [hRc] at hsplit
  -- the four outer ranges
  have hout : ∀ C : ℂ, ‖Rarc B N q a T - C‖ ≤ ‖Rcore N θs τ₀ T - C‖ + 2 * G * E5 + 2 * G * E5 + Lb + Lb := by
    intro C
    rw [hsplit]
    set I1 := ∫ θ in ((a : ℝ) / q - PP B N / (q * N))..((a : ℝ) / q - 1 / (2 * q * (N : ℝ))), FW (WN N) θ * ee (-(T * θ))
    set I2 := ∫ θ in ((a : ℝ) / q - 1 / (2 * q * (N : ℝ)))..(θs - τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))
    set I4 := ∫ θ in (θs + τ₀ / (2 * π))..((a : ℝ) / q + 1 / (2 * q * (N : ℝ))), FW (WN N) θ * ee (-(T * θ))
    set I5 := ∫ θ in ((a : ℝ) / q + 1 / (2 * q * (N : ℝ)))..((a : ℝ) / q + PP B N / (q * N)), FW (WN N) θ * ee (-(T * θ))
    have e : I1 + I2 + Rcore N θs τ₀ T + I4 + I5 - C = (Rcore N θs τ₀ T - C) + I2 + I4 + I1 + I5 := by ring
    rw [e]
    have n1 := norm_add_le ((Rcore N θs τ₀ T - C) + I2 + I4 + I1) I5
    have n2 := norm_add_le ((Rcore N θs τ₀ T - C) + I2 + I4) I1
    have n3 := norm_add_le ((Rcore N θs τ₀ T - C) + I2) I4
    have n4 := norm_add_le (Rcore N θs τ₀ T - C) I2
    linarith
  refine ⟨fun hnv => ?_, fun w₀ hw₀ hv => ?_⟩
  · have hc := hcore N (by omega) q a hq hqP ha hnv ts hts hF T
    rw [← hθs] at hc
    rw [← Gw_eq_FW hnv θs] at hc
    refine (hout _).trans ?_
    have h512 : E5 ≤ Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N)) := by
      apply Real.exp_le_exp.mpr
      have hN : (0 : ℝ) ≤ (N : ℝ) ^ (2 * ε) := by positivity
      have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hN (by positivity) (by linarith)
    have hG0 : 0 ≤ G := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h512 hG0]
  · have hc := (hvan N (by omega) q a hq hqP ha w₀ hw₀ hv ts hts hF).2.2.2.2.2 T
    rw [← hθs] at hc
    refine (hout _).trans ?_
    nlinarith [norm_nonneg (Gw (WN N) q a θs)]


/-- **Theorem E (arc expansion)** (paper §3.5), all three parts with one `N₀`: fix `B > 40`, `0 < ε < 1/8`,
`δ > 0`. For `N ≥ N₀`: (1) minor arcs, `sup_𝔪 |F_N| ≤ 2^n e^{(−log 2 + δ)π(N)}` (`thmE1_B40`); (2) emerging
arcs (`thmE2`, both cases of `𝒱(a/q)`); (3) other arcs, `|R_{a/q}(T)| ≤ 2^n e^{(−log 2 + ℓ_q + δ)π(N)}`
(`thmE3`). Hypotheses: Siegel–Walfisz, Vinogradov–Vaughan and Jackson (the last two for (1) only). -/
theorem thmE (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 40 < B)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ θ : ℝ, minorArc B N θ →
        ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 + δ) * Nat.primeCounting N)) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((∀ w ∈ WN N, ¬ vanish q a w) →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sS N ((a : ℝ) / q + ts / (2 * π)) +
                5 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))) ∧
        (∀ w₀ ∈ WN N, vanish q a w₀ →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              (w₀ * (|ts| + 1 / sV N q a w₀ ts) * ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sV N q a w₀ ts) +
                w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
                4 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)))) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q → ¬ emerging q → ∀ T : ℝ,
        ‖Rarc B N q a T‖ ≤
          2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨N₁, h1⟩ := thmE1_B40 hSW hVV hJ hB hδ
  obtain ⟨N₂, h2⟩ := thmE2 hSW hB0 hε0 hε hδ
  obtain ⟨N₃, h3⟩ := thmE3 hSW hB0 hδ
  refine ⟨N₁ + N₂ + N₃, fun N hN => ⟨h1 N (by omega), h2 N (by omega), fun q a hq hP ha hne T => ?_⟩⟩
  have h := h3 N (by omega) q a hq hP ha hne T
  rwa [ellE_eq (by omega : 0 < q)] at h

end ArcsAlgo.Core
