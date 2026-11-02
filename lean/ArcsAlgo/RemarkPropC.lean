module

public import ArcsAlgo.EdgeBracketC
public import ArcsAlgo.EdgeShoulderC
public import ArcsAlgo.EdgeE2
set_option autoImplicit false

/-!
# Remark (the formula of Proposition C) (paper §3.5)

The arc term of Proposition C, expanded at `a/q` with complex `z`, under the explicit antecedent
`|ν_{a/q}| ≤ C_νN^{3/2+ε/2}` (true under GRH for the odd characters mod `q`).

* `rel_arith`: the core error, its Gaussian tail and the two shoulders against `|𝒜| ≥ |F*|e^{ν²/(2s²)}N^{−1/2}/(2√(2π)s)`.
* `thmC2_rel` (`𝒱(a/q) = ∅`): uniformly for `|Re z| ≤ √(log N)`,
  `|R_{a/q}(T) − 𝒜_{a/q}(T)| ≤ 12N^{−1+6ε}|𝒜_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`.
* `thmC2_paper`: the paper's form, relative error `≤ N^{−1/2+3ε}` (for `ε < 1/8`).

The only hypothesis is `SiegelWalfisz`; the bound on `ν_{a/q}` is an antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

set_option maxHeartbeats 4000000 in
/-- The three error terms at the centre against the arc term: with `N = e^L`, the core error
`G·E·N^{−3/2+6ε}/s`, its Gaussian tail and the two shoulders are `≤ 12N^{−1+6ε}|𝒜|` when
`|𝒜| ≥ G·E·N^{−1/2}/(2√(2π)s)`. -/
theorem rel_arith {G E s L B ε S2 ν Cν nA : ℝ} (hG : 0 ≤ G) (hE : 1 ≤ E) (hs : 0 < s)
    (hsU : s ≤ 2 * L ^ B * Real.exp (3 / 2 * L)) (hL : 1 ≤ L) (hε0 : 0 < ε)
    (hS2 : Real.exp (3 * L) / (64 * L) ≤ S2) (hν : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L))
    (hka : 2 ^ 21 * Cν ^ 2 * L ^ 2 ≤ Real.exp (ε * L)) (hkb : 16384 * L ^ 2 ≤ Real.exp (2 * ε * L))
    (hkc : 20 * L ^ B ≤ Real.exp L)
    (hA : G * E * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s) ≤ nA) :
    G * (E * (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) + Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L)) +
        4 * (Real.exp (4 * ν ^ 2 / S2) * Real.exp (-(Real.exp (2 * ε * L)) / (2048 * L)))) ≤
      12 * Real.exp ((-1 + 6 * ε) * L) * nA := by
  have hL0 : 0 < L := by linarith
  set P := Real.exp (2 * ε * L) with hP
  set Q := Real.exp (ε * L) with hQ
  have hQ0 : 0 < Q := Real.exp_pos _
  have hPQ : P = Q * Q := by rw [hP, hQ, ← Real.exp_add]; ring_nf
  have hS20 : 0 < S2 := lt_of_lt_of_le (by positivity) hS2
  -- the Gaussian tail
  have h1 : Real.exp (-P / (4096 * L)) ≤ Real.exp (-(4 * L)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]; nlinarith
  -- `4ν²/S₂ ≤ 256C_ν²L e^{εL}`
  have hν2 : ν ^ 2 ≤ Cν ^ 2 * Real.exp ((3 + ε) * L) := by
    have h := pow_le_pow_left₀ (abs_nonneg ν) hν 2
    rw [sq_abs, mul_pow, ← Real.exp_nat_mul] at h
    calc ν ^ 2 ≤ Cν ^ 2 * Real.exp (((2 : ℕ) : ℝ) * ((3 / 2 + ε / 2) * L)) := h
      _ = _ := by congr 2; push_cast; ring
  have h2 : 4 * ν ^ 2 / S2 ≤ 256 * Cν ^ 2 * L * Q := by
    rw [div_le_iff₀ hS20]
    have e : Real.exp ((3 + ε) * L) = Q * Real.exp (3 * L) := by rw [hQ, ← Real.exp_add]; ring_nf
    have hS' : 256 * Cν ^ 2 * L * Q * (Real.exp (3 * L) / (64 * L)) ≤ 256 * Cν ^ 2 * L * Q * S2 :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have e2 : 256 * Cν ^ 2 * L * Q * (Real.exp (3 * L) / (64 * L)) = 4 * (Cν ^ 2 * Real.exp ((3 + ε) * L)) := by
      rw [e]; field_simp; ring
    nlinarith
  -- the shoulders
  have h3 : Real.exp (4 * ν ^ 2 / S2) * Real.exp (-P / (2048 * L)) ≤ Real.exp (-(4 * L)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : 256 * Cν ^ 2 * L * Q ≤ P / (8192 * L) := by
      rw [le_div_iff₀ (by positivity), hPQ]
      have := mul_le_mul_of_nonneg_right hka hQ0.le
      nlinarith
    have hb : 4 * L ≤ P / (4096 * L) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have hc : P / (8192 * L) + P / (4096 * L) ≤ P / (2048 * L) := by
      have hP0 : 0 < P := Real.exp_pos _
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hP0 hL0]
    rw [neg_div]; linarith
  -- `5e^{−4L} ≤ e^{(−3/2+6ε)L}/(2s)`
  have h4 : 5 * Real.exp (-(4 * L)) ≤ Real.exp ((-(3 / 2) + 6 * ε) * L) / s / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have hB0 : 0 ≤ L ^ B := by positivity
    have hs2 : s * 2 ≤ 4 * L ^ B * Real.exp (3 / 2 * L) := by linarith
    have he1 : Real.exp (-(3 / 2) * L) ≤ Real.exp ((-(3 / 2) + 6 * ε) * L) := Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (-(4 * L)) * Real.exp (3 / 2 * L) * Real.exp L = Real.exp (-(3 / 2) * L) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h5 : 5 * Real.exp (-(4 * L)) * (4 * L ^ B * Real.exp (3 / 2 * L)) ≤ Real.exp (-(3 / 2) * L) := by
      rw [← he2]
      have : 0 ≤ Real.exp (-(4 * L)) * Real.exp (3 / 2 * L) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkc this]
    have h6 : 5 * Real.exp (-(4 * L)) * (s * 2) ≤ 5 * Real.exp (-(4 * L)) * (4 * L ^ B * Real.exp (3 / 2 * L)) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    linarith
  -- assemble
  set X := Real.exp ((-(3 / 2) + 6 * ε) * L) / s with hX
  have hX0 : 0 < X := by positivity
  have hpi : Real.sqrt (2 * π) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_le_four]
  have hpi0 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hlhs : G * (E * X + Real.exp (-P / (4096 * L)) + 4 * (Real.exp (4 * ν ^ 2 / S2) *
      Real.exp (-P / (2048 * L)))) ≤ G * (3 / 2 * (E * X)) := by
    apply mul_le_mul_of_nonneg_left _ hG
    have : Real.exp (-P / (4096 * L)) + 4 * (Real.exp (4 * ν ^ 2 / S2) * Real.exp (-P / (2048 * L))) ≤ X / 2 := by
      rw [hX]; linarith
    have : X / 2 ≤ E * X / 2 := by nlinarith
    linarith
  have hrhs : G * (3 / 2 * (E * X)) ≤ 12 * Real.exp ((-1 + 6 * ε) * L) *
      (G * E * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s)) := by
    have e : Real.exp ((-1 + 6 * ε) * L) * Real.exp (-(1 / 2) * L) = Real.exp ((-(3 / 2) + 6 * ε) * L) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 12 * Real.exp ((-1 + 6 * ε) * L) * (G * E * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s)) =
        6 / Real.sqrt (2 * π) * (G * (E * X)) := by
      rw [hX, ← e]; field_simp; ring
    rw [e2]
    have h6 : 3 / 2 ≤ 6 / Real.sqrt (2 * π) := by rw [le_div_iff₀ hpi0]; linarith
    have : 0 ≤ G * (E * X) := by positivity
    nlinarith
  have hn : 0 ≤ 12 * Real.exp ((-1 + 6 * ε) * L) := by positivity
  calc _ = G * (E * X + Real.exp (-P / (4096 * L)) + 4 * (Real.exp (4 * ν ^ 2 / S2) *
        Real.exp (-P / (2048 * L)))) := by rw [hX, neg_div, neg_div]
    _ ≤ _ := hlhs.trans (hrhs.trans (mul_le_mul_of_nonneg_left hA hn))

set_option maxHeartbeats 8000000 in
/-- **Remark (the formula of Proposition C)**, case `𝒱(a/q) = ∅` (paper §3.5): fix `B > 0`, `0 < ε < 1/8`,
`C_ν > 0`, `δ > 0`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, `𝒱(a/q) = ∅` and `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`,
uniformly for `|Re z| ≤ √(log N)` (`z = (T − κ₁)/s` complex, cumulants of Proposition C at `a/q`):
`|R_{a/q}(T) − 𝒜_{a/q}(T)| ≤ 12N^{−1+6ε}|𝒜_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`,
`𝒜_{a/q}(T) = e(−Ta/q)Ĥ_{a/q}(T)`. The hypothesis on `ν` holds under GRH for the odd characters mod `q`;
it is an explicit antecedent here. The only other hypothesis is Siegel–Walfisz. -/
theorem thmC2_rel (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
      ∀ T : ℝ, |(((T : ℂ) - kS N ((a : ℝ) / q) 1) / (sS N ((a : ℝ) / q) : ℂ)).re| ≤ √(Real.log N) →
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ ≤
          12 * (N : ℝ) ^ (-1 + 6 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  obtain ⟨N₁, hcore⟩ := thmC_core hSW hB hε0 hε hCν
  obtain ⟨N₂, hbr⟩ := thmC_bracket hSW hB hε0 hε hCν
  obtain ⟨N₃, hsh⟩ := thmC_shoulder hSW hB hε0 hε hCν
  obtain ⟨N₄, hlo⟩ := thmE2_lobes hSW hB hδ
  obtain ⟨c, hc, N₅, hW2⟩ := lemmaW2 hSW hB
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp 2 hε0 (2 ^ 21 * Cν ^ 2)
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp 2 (by positivity : 0 < 2 * ε) 16384
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp B one_pos 20
  set Kmax := max K₁ (max K₂ K₃)
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha hnv hnu T hT => ?_⟩
  obtain ⟨-, hS2pos, -, -, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  obtain ⟨hs1, hs2, him, hge⟩ := hbr N (by omega) q a hq hqP ha hnv hnu
  have hc0 := hcore N (by omega) q a hq hqP ha hnv hnu T
  have hs := hsh N (by omega) q a hq hqP ha hnu T
  have hl := hlo N (by omega) q a hq hqP ha T
  dsimp only at hs hl
  obtain ⟨-, -, hsR, hsL⟩ := hs
  obtain ⟨-, hlR, hlL⟩ := hl
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_max_left _ _) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hq0 : (0 : ℝ) ≤ q := by positivity
  -- the split of the arc
  set θc := (a : ℝ) / q with hθc
  set τ₀ := Nr ^ (-(3 / 2 : ℝ) + ε)
  set δθ := 1 / (2 * q * Nr)
  set G := ‖FW (WN N) θc‖ with hGdef
  set S2 := S2W (WN N) q a
  set ν := nuW (WN N) q a with hν
  set s := sS N θc with hsdef
  set e2 := Real.exp (-(Nr ^ (2 * ε)) / (2048 * L))
  set Lb := 2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)
  have hGw : ‖Gw (WN N) q a θc‖ = G := by rw [Gw_eq_FW hnv]
  rw [hGw] at hsR hsL
  have hsplit := Rarc_split B N q a T (θc - δθ) (θc - τ₀ / (2 * π)) (θc + τ₀ / (2 * π)) (θc + δθ)
  have hRc : (∫ θ in (θc - τ₀ / (2 * π))..(θc + τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))) =
      Rcore N θc τ₀ T := rfl
  rw [hRc] at hsplit
  set Am := ee (-(T * θc)) * HhatC N θc T with hAm
  have hout : ‖Rarc B N q a T - Am‖ ≤ ‖Rcore N θc τ₀ T - Am‖ +
      2 * (G * Real.exp (4 * ν ^ 2 / S2)) * e2 + 2 * (G * Real.exp (4 * ν ^ 2 / S2)) * e2 + Lb + Lb := by
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
    linarith
  -- the arc term is not small
  have hAeq : ‖Am‖ = G * ‖mainEC (kS N θc 1) s (kS N θc 3) (kS N θc 4) T‖ := by
    rw [hAm, norm_mul, norm_ee, one_mul]; unfold HhatC; rw [norm_mul]
  set z := ((T : ℂ) - kS N θc 1) / (s : ℂ) with hz
  have hs0 : 0 < s := by linarith
  have hzim : z.im = -ν / s := by
    rw [hz, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, him]; ring
  have hzre : z.re ^ 2 ≤ L := by
    have := pow_le_pow_left₀ (abs_nonneg _) hT 2
    rwa [sq_abs, Real.sq_sqrt hL0.le] at this
  have hφ : Real.exp (ν ^ 2 / (2 * s ^ 2)) * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) ≤ ‖phiC z‖ := by
    rw [norm_phiC, ← Real.exp_add]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    rw [hzim, div_pow, neg_sq]
    have : ν ^ 2 / s ^ 2 / 2 = ν ^ 2 / (2 * s ^ 2) := by field_simp
    nlinarith
  have hA : G * Real.exp (ν ^ 2 / (2 * s ^ 2)) * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s) ≤ ‖Am‖ := by
    rw [hAeq]
    have h := hge T hT
    have hG0 : 0 ≤ G := norm_nonneg _
    calc G * Real.exp (ν ^ 2 / (2 * s ^ 2)) * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s)
        = G * (Real.exp (ν ^ 2 / (2 * s ^ 2)) * Real.exp (-(1 / 2) * L) / Real.sqrt (2 * π) / (2 * s)) := by ring
      _ ≤ G * (‖phiC z‖ / (2 * s)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left h hG0
  -- the sizes
  have hsU : s ≤ 2 * L ^ B * Real.exp (3 / 2 * L) := by
    have h3 : Nr ^ 3 = Real.exp (3 / 2 * L) ^ 2 := by
      rw [← Real.exp_nat_mul, ← hexpL, ← Real.exp_nat_mul]; norm_num; ring_nf
    have hq2 : (q : ℝ) ^ 2 ≤ (L ^ B) ^ 2 := pow_le_pow_left₀ hq0 hqL 2
    have : s ^ 2 ≤ (2 * L ^ B * Real.exp (3 / 2 * L)) ^ 2 := by
      rw [mul_pow, mul_pow, ← h3]
      have : 0 ≤ Nr ^ 3 := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ hs0.le (by positivity) (by norm_num)).mp this
  have hS2e : Real.exp (3 * L) / (64 * L) ≤ S2 := by
    have e : Nr ^ 3 = Real.exp (3 * L) := by rw [← hexpL, ← Real.exp_nat_mul]; norm_num
    rw [← e]; exact hS2lo
  have hνe : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L) := by rw [← hrp]; exact hnu
  have hka : 2 ^ 21 * Cν ^ 2 * L ^ 2 ≤ Real.exp (ε * L) := by
    have h := hk1 L hL1; rw [show L ^ (2 : ℝ) = L ^ 2 by norm_cast] at h
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hkb : 16384 * L ^ 2 ≤ Real.exp (2 * ε * L) := by
    have h := hk2 L hL2; rw [show L ^ (2 : ℝ) = L ^ 2 by norm_cast] at h
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hkc : 20 * L ^ B ≤ Real.exp L := (hk3 L hL3).trans (Real.exp_le_exp.mpr (by nlinarith))
  have hra := rel_arith (norm_nonneg _) (Real.one_le_exp (by positivity)) hs0 hsU hLone hε0 hS2e hνe hka hkb hkc hA
  -- conclude
  refine hout.trans ?_
  have hcore' : ‖Rcore N θc τ₀ T - Am‖ ≤ G * (Real.exp (ν ^ 2 / (2 * s ^ 2)) *
      (Real.exp ((-(3 / 2) + 6 * ε) * L) / s) + Real.exp (-(Real.exp (2 * ε * L)) / (4096 * L))) := by
    have := hc0; rw [hrp, hrp] at this; exact this
  have he2 : e2 = Real.exp (-(Real.exp (2 * ε * L)) / (2048 * L)) := by
    rw [show e2 = Real.exp (-(Nr ^ (2 * ε)) / (2048 * L)) from rfl, hrp]
  rw [hrp, he2]
  rw [he2] at hout
  have : ‖Rcore N θc τ₀ T - Am‖ + 2 * (G * Real.exp (4 * ν ^ 2 / S2)) * Real.exp (-(Real.exp (2 * ε * L)) / (2048 * L)) +
      2 * (G * Real.exp (4 * ν ^ 2 / S2)) * Real.exp (-(Real.exp (2 * ε * L)) / (2048 * L)) ≤
      12 * Real.exp ((-1 + 6 * ε) * L) * ‖Am‖ := by
    refine le_trans ?_ hra
    nlinarith [hcore']
  linarith

/-- **Remark (the formula of Proposition C)**, the paper's form (`𝒱(a/q) = ∅`): under the hypotheses of
`thmC2_rel`, for `N ≥ N₀`, `R_{a/q}(T) = 𝒜_{a/q}(T)(1 + O(N^{−1/2+3ε})) + O(2^n e^{(−log 2 + ℓ*_q + δ)π(N)})`
uniformly for `|Re z| ≤ √(log N)`; the constant in the first `O` is `1`. (`thmC2_rel` gives the
stronger exponent `−1 + 6ε`.) -/
theorem thmC2_paper (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
      ∀ T : ℝ, |(((T : ℂ) - kS N ((a : ℝ) / q) 1) / (sS N ((a : ℝ) / q) : ℂ)).re| ≤ √(Real.log N) →
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ ≤
          (N : ℝ) ^ (-(1 / 2) + 3 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  obtain ⟨N₁, h⟩ := thmC2_rel hSW hB hε0 hε hCν hδ
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  obtain ⟨K, hK, hk⟩ := ev_poly_exp 0 hε3 12
  refine ⟨N₁ + ⌈Real.exp K⌉₊ + 2, fun N hN q a hq hqP ha hnv hnu T hT => ?_⟩
  refine (h N (by omega) q a hq hqP ha hnv hnu T hT).trans ?_
  set Nr : ℝ := (N : ℝ) with hNr
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 2 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr
  have hKL : K ≤ L := by
    have : Real.exp K ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp K⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : 1 ≤ L := le_trans hK hKL
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have h12 : 12 * Nr ^ (-1 + 6 * ε) ≤ Nr ^ (-(1 / 2) + 3 * ε) := by
    rw [hrp, hrp]
    have h := hk L hKL
    rw [Real.rpow_zero, mul_one] at h
    have h' : 12 ≤ Real.exp ((1 / 2 - 3 * ε) * L) := h.trans (Real.exp_le_exp.mpr (by nlinarith))
    have e : Real.exp ((-(1 / 2) + 3 * ε) * L) = Real.exp ((1 / 2 - 3 * ε) * L) * Real.exp ((-1 + 6 * ε) * L) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
  have hn := norm_nonneg (ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T)
  nlinarith

end ArcsAlgo.Core
