module

public import ArcsAlgo.EdgeCentre
public import ArcsAlgo.EdgeRelC
set_option autoImplicit false

/-!
# The arc term at the centre is not small (paper §3.5, Remark (the formula of Proposition C))

* `bracket_size`: the size condition of `mainEC_ge` at the centre.
* `thmC_bracket`: for `𝒱(a/q) = ∅` and `|ν_{a/q}| ≤ C_νN^{3/2+ε/2}`: `s ≥ 1`, `s² ≤ 2q²N³`, `Im κ₁ = ν`, and
  `|mainEC(T)| ≥ |φ(z)|/(2s)` whenever `|Re z| ≤ √(log N)` (`|Im z| = |ν|/s` may grow like `N^{ε/2}√(log N)`).

Hypotheses: `SiegelWalfisz`; the bound on `ν_{a/q}` is an explicit antecedent.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

set_option maxHeartbeats 4000000 in
/-- The size condition of `mainEC_ge` at the centre: with `R = √L + Λ`, `Λ = C_Λ√L e^{εL/2}`, `u = Mx`,
`52R⁶u ≤ 1/2` and `u ≤ 1`. -/
theorem bracket_size {q L B ε s A α3 α4 CΛ : ℝ} (hB : 0 < B) (hL0 : 0 < L) (hLone : 1 ≤ L) (hε0 : 0 < ε)
    (hε : ε < 1 / 8) (hq1 : 1 ≤ q) (hqL : q ≤ L ^ B) (hA : A = 4 * 8 ^ 6 * q ^ 6) (hCΛ : 32 ≤ CΛ)
    (hα3 : α3 ≤ A * Real.exp (4 * L)) (hα4 : α4 ≤ A * Real.exp (5 * L)) (hα30 : 0 ≤ α3) (hα40 : 0 ≤ α4)
    (hsD : Real.exp (3 / 2 * L) / (16 * √L) ≤ s)
    (hk : 6656 * CΛ ^ 6 * (4 * 8 ^ 6 * 16 ^ 6) * L ^ (6 * B + 6) ≤ Real.exp ((1 / 2 - 3 * ε) * √L)) :
    ∃ u : ℝ, α3 / s ^ 3 ≤ u ∧ α4 / s ^ 4 ≤ u ∧ u ≤ 1 ∧
      52 * (√L + CΛ * √L * Real.exp (ε / 2 * L)) ^ 6 * u ≤ 1 / 2 := by
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  set D := 16 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ q ^ 6 := one_le_pow₀ hq1; nlinarith
  set M := A * D ^ 6 with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [one_le_pow₀ (n := 6) hD1]
  have hM0 : 0 ≤ M := by linarith
  set x := Real.exp (-(1 / 2) * L) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hxk : ∀ k : ℕ, x ^ k = Real.exp (-(k / 2 : ℝ) * L) := fun k => by
    rw [hx, ← Real.exp_nat_mul]; congr 1; ring
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have b3 : α3 / s ^ 3 ≤ M * x := by
    have := norm_cum (k := 3) (by norm_num) (by linarith) hD1 hα3 hsD
    rw [hx]; convert this using 2; push_cast; ring_nf
  have b4 : α4 / s ^ 4 ≤ M * x ^ 2 := by
    have := norm_cum (k := 4) (by norm_num) (by linarith) hD1 hα4 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have hMle : M ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hM, hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : q ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  set Λ := CΛ * √L * Real.exp (ε / 2 * L) with hΛ
  have hexpε : 1 ≤ Real.exp (ε / 2 * L) := Real.one_le_exp (by positivity)
  have hΛL : √L ≤ Λ := by
    rw [hΛ]
    have : √L ≤ CΛ * √L := by nlinarith
    nlinarith
  have hR : (√L + Λ) ^ 6 ≤ 64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L) := by
    have h1 : √L + Λ ≤ 2 * Λ := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 6
    have e : (2 * Λ) ^ 6 = 64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L) := by
      rw [hΛ, mul_pow, mul_pow, mul_pow, show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le,
        ← Real.exp_nat_mul]
      rw [show ((6 : ℕ) : ℝ) * (ε / 2 * L) = 3 * ε * L by push_cast; ring]; ring
    linarith
  have hx2 : M * x ^ 2 ≤ M * x := by
    have : x ^ 2 ≤ x := by nlinarith
    exact mul_le_mul_of_nonneg_left this hM0
  have hpoly : 52 * (64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L)) * (M * x) ≤ 1 / 2 := by
    have hL63 : L ^ (6 * B) * L ^ 3 * L ^ 3 = L ^ (6 * B + 6) := by
      rw [mul_assoc, ← pow_add, Real.rpow_add hL0, show L ^ (6 : ℝ) = L ^ (3 + 3) by norm_cast]
    have h1 : 52 * 64 * CΛ ^ 6 * L ^ 3 * M ≤ 6656 * CΛ ^ 6 * K₀ * L ^ (6 * B + 6) / 2 := by
      rw [← hL63]
      have : (0 : ℝ) ≤ 52 * 64 * CΛ ^ 6 * L ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hMle this]
    have h2 : 6656 * CΛ ^ 6 * K₀ * L ^ (6 * B + 6) ≤ Real.exp ((1 / 2 - 3 * ε) * L) :=
      hk.trans (Real.exp_le_exp.mpr (by nlinarith))
    have he : Real.exp (3 * ε * L) * x * Real.exp ((1 / 2 - 3 * ε) * L) = 1 := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
    have hEx : 0 ≤ Real.exp (3 * ε * L) * x := by positivity
    calc 52 * (64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L)) * (M * x)
        = (52 * 64 * CΛ ^ 6 * L ^ 3 * M) * (Real.exp (3 * ε * L) * x) := by ring
      _ ≤ (6656 * CΛ ^ 6 * K₀ * L ^ (6 * B + 6) / 2) * (Real.exp (3 * ε * L) * x) :=
          mul_le_mul_of_nonneg_right h1 hEx
      _ ≤ (Real.exp ((1 / 2 - 3 * ε) * L) / 2) * (Real.exp (3 * ε * L) * x) := by gcongr
      _ = 1 / 2 := by rw [show Real.exp ((1 / 2 - 3 * ε) * L) / 2 * (Real.exp (3 * ε * L) * x) =
            (Real.exp (3 * ε * L) * x * Real.exp ((1 / 2 - 3 * ε) * L)) / 2 by ring, he]
  refine ⟨M * x, b3, b4.trans hx2, ?_, ?_⟩
  · have h64 : 1 ≤ 64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L) := by
      have : 1 ≤ CΛ ^ 6 := one_le_pow₀ (by linarith)
      have : 1 ≤ L ^ 3 := one_le_pow₀ hLone
      have : 1 ≤ Real.exp (3 * ε * L) := Real.one_le_exp (by positivity)
      have : 1 ≤ CΛ ^ 6 * L ^ 3 := by nlinarith
      nlinarith
    have hMx0 : 0 ≤ M * x := by positivity
    nlinarith
  · have hMx0 : 0 ≤ M * x := by positivity
    calc 52 * (√L + Λ) ^ 6 * (M * x) ≤ 52 * (64 * CΛ ^ 6 * L ^ 3 * Real.exp (3 * ε * L)) * (M * x) := by gcongr
      _ ≤ 1 / 2 := hpoly

set_option maxHeartbeats 16000000 in
/-- **The bracket at the centre** (Remark (the formula of Proposition C), `𝒱(a/q) = ∅`): for `N ≥ N₀`,
`3 ≤ q ≤ 𝔓`, `(a, q) = 1`, `|ν| ≤ C_νN^{3/2+ε/2}`: `1 ≤ s`, `s² ≤ 2q²N³`, and for every `T` with
`|Re z| ≤ √(log N)` (`z = (T − κ₁)/s` complex), `|mainEC(T)| ≥ |φ(z)|/(2s)`. -/
theorem thmC_bracket (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
      1 ≤ sS N ((a : ℝ) / q) ∧ sS N ((a : ℝ) / q) ^ 2 ≤ 2 * (q : ℝ) ^ 2 * (N : ℝ) ^ 3 ∧
      (kS N ((a : ℝ) / q) 1).im = nuW (WN N) q a ∧
      ∀ T : ℝ, |(((T : ℂ) - kS N ((a : ℝ) / q) 1) / (sS N ((a : ℝ) / q) : ℂ)).re| ≤ √(Real.log N) →
        ‖phiC (((T : ℂ) - kS N ((a : ℝ) / q) 1) / (sS N ((a : ℝ) / q) : ℂ))‖ / (2 * sS N ((a : ℝ) / q)) ≤
          ‖mainEC (kS N ((a : ℝ) / q) 1) (sS N ((a : ℝ) / q)) (kS N ((a : ℝ) / q) 3) (kS N ((a : ℝ) / q) 4) T‖ := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  set CΛ : ℝ := (Cν + 2) * 16 with hCΛ
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp (6 * B + 6) hε3 (6656 * CΛ ^ 6 * K₀)
  obtain ⟨K₇, hK₇, hk7⟩ := ev_poly_exp 1 one_pos 16
  set Kmax := max K₁ K₇
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha hnv hnu => ?_⟩
  obtain ⟨-, hS2pos, -, -, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_max_left _ _) hKL
  have hL7 : K₇ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqL1 : 1 ≤ √L := by rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hnp : ∀ k : ℕ, Nr ^ k = Real.exp (k * L) := fun k => by rw [← hexpL, ← Real.exp_nat_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  -- the centre, written as `a/q + 0/(2π)`
  have hθ0 : (a : ℝ) / q = (a : ℝ) / q + 0 / (2 * π) := by simp
  rw [hθ0]
  set ts : ℝ := 0 with hts0
  have hts' : Nr * |ts| ≤ 1 / q := by rw [hts0]; simp
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  have hpar := fun w (hw : w ∈ WN N) => pStar_le hq hnv hts' hw
  have hne : ∀ w ∈ WN N, 1 + ee (w * θs) ≠ 0 := fun w hw => (hpar w hw).1
  have hpq : ∀ w ∈ WN N, ‖pStar θs w‖ ≤ q := fun w hw => (hpar w hw).2
  -- the cumulants
  set ν := nuW (WN N) q a with hν
  set k1 : ℂ := ((∑ w ∈ WN N, (w : ℝ) / 2 : ℝ) : ℂ) + I * (ν : ℂ) with hk1d
  have h1 : kap (WN N) (pStar θs) 1 = k1 := kS_one_c hq hnv
  have hk1im : k1.im = ν := by rw [hk1d]; simp
  set X : ℝ := ∑ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) with hX
  have h2X : kap (WN N) (pStar θs) 2 = (X : ℂ) := kS_two hq hnv hts'
  have hfilt : (WN N).filter (fun w => ¬ vanish q a w) = WN N := filter_true_of_mem hnv
  have htsw : |ts| < π / (q * Nr) := by rw [hts0, abs_zero]; positivity
  have hXge : S2W (WN N) q a / 4 ≤ X := by
    have := kappa2_ge (W := WN N) (q := q) (a := a) (by omega) (by omega)
      (fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)) htsw
    rwa [hfilt] at this
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXge
  set s := sS N θs with hsdef
  have hsX : s = √X := by rw [hsdef]; unfold sS kS; rw [h2X, Complex.ofReal_re]
  have hs0 : 0 < s := by rw [hsX]; exact Real.sqrt_pos.mpr hX0
  have hs2 : s ^ 2 = X := by rw [hsX, Real.sq_sqrt hX0.le]
  have h2 : kap (WN N) (pStar θs) 2 = ((s ^ 2 : ℝ) : ℂ) := by rw [hs2]; exact h2X
  -- `s ≥ N^{3/2}/D`, `D = 16√L`
  set D := 16 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hsD : Real.exp (3 / 2 * L) / D ≤ s := by
    rw [hsX, Real.le_sqrt (by positivity) hX0.le]
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 = Nr ^ 3 / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hnp 3]
      congr 1; push_cast; ring_nf; ring
    rw [e]
    have := hS2lo
    have e2 : Nr ^ 3 / (256 * L) = Nr ^ 3 / (64 * L) / 4 := by field_simp; ring
    linarith
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ hsD
    rw [le_div_iff₀ (by positivity), one_mul, hD]
    have h7 := hk7 L hL7; rw [Real.rpow_one, one_mul] at h7
    calc 16 * √L ≤ 16 * L := by linarith
      _ ≤ Real.exp (√L) := h7
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  -- the size of the cumulants
  set A : ℝ := 4 * 8 ^ 6 * (q : ℝ) ^ 6 with hA
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℝ) ≤ (q : ℝ) ^ 6 := one_le_pow₀ hq1; nlinarith
  have hWN : ∀ w ∈ WN N, (w : ℝ) ≤ Nr := fun w hw => WN_le hw
  have hα : ∀ j : ℕ, 3 ≤ j → j ≤ 5 → ‖kap (WN N) (pStar θs) j‖ / (Nat.factorial j : ℝ) ≤
      A * Real.exp ((j + 1) * L) := by
    intro j hj3 hj5
    have h := kap_le (WN N) (pStar θs) hq1 hpq j
    have hsum := sum_pow_WN (N := N) (by omega) j
    have hf : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
    rw [div_le_iff₀ hf]
    have hqj : (q : ℝ) ^ j ≤ (q : ℝ) ^ 6 := pow_le_pow_right₀ hq1 (by omega)
    have hNj : Nr ^ (j + 1) = Real.exp ((j + 1) * L) := by rw [hnp]; push_cast; ring_nf
    rw [← hNr] at hsum
    calc ‖kap (WN N) (pStar θs) j‖ ≤ (Nat.factorial j : ℝ) * 25 * (q : ℝ) ^ j * (2 * Nr ^ (j + 1)) :=
          h.trans (by gcongr)
      _ ≤ (Nat.factorial j : ℝ) * 25 * (q : ℝ) ^ 6 * (2 * Nr ^ (j + 1)) := by gcongr
      _ ≤ A * Nr ^ (j + 1) * (Nat.factorial j : ℝ) := by
          rw [hA]; have : (0 : ℝ) ≤ (q : ℝ) ^ 6 * Nr ^ (j + 1) * (Nat.factorial j : ℝ) := by positivity
          nlinarith
      _ = A * Real.exp ((j + 1) * L) * (Nat.factorial j : ℝ) := by rw [hNj]
  set α3 := ‖kap (WN N) (pStar θs) 3‖ / 6
  set α4 := ‖kap (WN N) (pStar θs) 4‖ / 24
  set α5 := ‖kap (WN N) (pStar θs) 5‖ / 120
  set ρ := 2 * 8 ^ 6 * (q : ℝ) ^ 6 * ∑ w ∈ WN N, (w : ℝ) ^ 6 with hρ
  have hα3 : α3 ≤ A * Real.exp (4 * L) := by
    have := hα 3 le_rfl (by norm_num); norm_num [Nat.factorial] at this; exact this
  have hα4 : α4 ≤ A * Real.exp (5 * L) := by
    have := hα 4 (by norm_num) (by norm_num); norm_num [Nat.factorial] at this; exact this
  have hα5 : α5 ≤ A * Real.exp (6 * L) := by
    have := hα 5 (by norm_num) le_rfl; norm_num [Nat.factorial] at this; exact this
  have hρb : ρ ≤ A * Real.exp (7 * L) := by
    have hsum := sum_pow_WN (N := N) (by omega) 6
    rw [← hNr, show (6 + 1 : ℕ) = 7 from rfl, hnp] at hsum
    rw [hρ, hA]; push_cast at hsum
    have : (0 : ℝ) ≤ 2 * 8 ^ 6 * (q : ℝ) ^ 6 := by positivity
    nlinarith
  have hα30 : 0 ≤ α3 := by positivity
  have hα40 : 0 ≤ α4 := by positivity
  have hα50 : 0 ≤ α5 := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  -- the upper bound on `s`
  have hXle : X ≤ 2 * (q : ℝ) ^ 2 * Nr ^ 3 := by
    rw [hX]
    have hsum := sum_pow_WN (N := N) (by omega) 2
    rw [← hNr] at hsum
    calc ∑ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2)
        ≤ ∑ w ∈ WN N, (q : ℝ) ^ 2 * (w : ℝ) ^ 2 := by
          refine sum_le_sum fun w hw => ?_
          have hc := cos_star_ge hq hnv hts' hw
          have e : π * (w * ((a : ℝ) / q + ts / (2 * π))) = alw q a w + w * ts / 2 := by
            unfold alw; rw [hts0]; ring
          rw [e] at hc
          have hc2 : 1 / (4 * (q : ℝ) ^ 2) ≤ Real.cos (alw q a w + w * ts / 2) ^ 2 := by
            have := pow_le_pow_left₀ (by positivity) hc 2
            rw [sq_abs] at this
            calc 1 / (4 * (q : ℝ) ^ 2) = (1 / (2 * (q : ℝ))) ^ 2 := by ring
              _ ≤ _ := this
          have hc0 : 0 < Real.cos (alw q a w + w * ts / 2) ^ 2 := lt_of_lt_of_le (by positivity) hc2
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) := by
            rw [div_le_iff₀ (by positivity)] at hc2; nlinarith
          nlinarith [sq_nonneg (w : ℝ)]
      _ = (q : ℝ) ^ 2 * ∑ w ∈ WN N, (w : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ (q : ℝ) ^ 2 * (2 * Nr ^ (2 + 1)) := by gcongr
      _ = 2 * (q : ℝ) ^ 2 * Nr ^ 3 := by ring
  -- the bracket
  obtain ⟨u, hu3, hu4, hu1, hu⟩ := bracket_size (q := (q : ℝ)) hB hL0 hLone hε0 hε hq1 hqL hA
    (by rw [hCΛ]; nlinarith) hα3 hα4 hα30 hα40 hsD (hk1 L hL1)
  have hR1 : 1 ≤ √L + CΛ * √L * Real.exp (ε / 2 * L) := by
    have : 0 ≤ CΛ * √L * Real.exp (ε / 2 * L) := by rw [hCΛ]; positivity
    linarith
  have hnu' : |ν| ≤ Cν * Real.exp ((3 / 2 + ε / 2) * L) := by rw [← hrp]; exact hnu
  have hνs : |ν| / s ≤ CΛ * √L * Real.exp (ε / 2 * L) := by
    rw [div_le_iff₀ hs0]
    have h1 : CΛ * √L * Real.exp (ε / 2 * L) * (Real.exp (3 / 2 * L) / D) =
        (Cν + 2) * Real.exp ((3 / 2 + ε / 2) * L) := by
      have hsq0 : 0 < √L := by positivity
      rw [hCΛ, hD, show (3 / 2 + ε / 2) * L = ε / 2 * L + 3 / 2 * L by ring, Real.exp_add]
      field_simp <;> ring_nf
    have h2 : CΛ * √L * Real.exp (ε / 2 * L) * (Real.exp (3 / 2 * L) / D) ≤
        CΛ * √L * Real.exp (ε / 2 * L) * s := mul_le_mul_of_nonneg_left hsD (by rw [hCΛ]; positivity)
    have h3 : Cν * Real.exp ((3 / 2 + ε / 2) * L) ≤ (Cν + 2) * Real.exp ((3 / 2 + ε / 2) * L) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith
  refine ⟨hs1, by rw [hs2]; exact hXle, by unfold kS; rw [h1, hk1im], fun T hT => ?_⟩
  have e1 : kS N θs 1 = k1 := h1
  rw [e1] at hT ⊢
  have hz : ‖((T : ℂ) - k1) / (s : ℂ)‖ ≤ √L + CΛ * √L * Real.exp (ε / 2 * L) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have him : (((T : ℂ) - k1) / (s : ℂ)).im = -ν / s := by
      rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, hk1im]; ring
    rw [him, abs_div, abs_neg, abs_of_pos hs0]
    linarith
  exact mainEC_ge hs0 hR1 T hz hu3 hu4 hu1 hu

end ArcsAlgo.Core
