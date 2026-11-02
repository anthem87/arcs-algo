module

public import ArcsAlgo.EdgeArc1
set_option autoImplicit false

/-!
# Theorem E(2), the core of an emerging arc without vanishing factor (paper §3.5)

* `kap_le`, `sum_pow_WN`: `|κ_j| ≤ j!·25K^jΣw^j`, `Σ_{w∈W_N} w^j ≤ 2N^{j+1}`.
* `norm_cum`: the normalized cumulants `κ_j/s^j`.
* `thmE2_core`: fix `B > 0`, `0 < ε < 1/8`, `τ₀ = N^{−3/2+ε}`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`,
  `𝒱(a/q) = ∅`, `t*` the peak of Lemma W (`F′(t*) = 0`, `|t*| ≤ 4|ν|/S₂`), uniformly in `T`:
  `|∫_{|θ−θ*|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)Ĥ(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + e^{−N^{2ε}/(2048 log N)})`.
  This is the core of the proof of Theorem E(2): `log(factor) = Σ_{j≤5}κ_{j,w}(iσ)^j/j! + O((qwσ)⁶)`, the
  expansion of `e^x` with every dropped product of cumulants, and the Gaussian integrals; the
  truncation of the Gaussian integrals to `|σ| ≤ τ₀` is the second error term.

The only hypothesis is `SiegelWalfisz` (through Lemma W).
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

theorem kap_le (W : Finset ℕ) (p : ℕ → ℂ) {K : ℝ} (hK : 1 ≤ K) (hp : ∀ w ∈ W, ‖p w‖ ≤ K) (j : ℕ) :
    ‖kap W p j‖ ≤ (Nat.factorial j : ℝ) * 25 * K ^ j * ∑ w ∈ W, (w : ℝ) ^ j := by
  unfold kap
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun w hw => ?_
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  have := norm_cB_le hK (hp w hw) j
  have h0 : (0 : ℝ) ≤ (w : ℝ) ^ j * (Nat.factorial j : ℝ) := by positivity
  calc (w : ℝ) ^ j * (Nat.factorial j : ℝ) * ‖cB (p w) j‖ ≤ (w : ℝ) ^ j * (Nat.factorial j : ℝ) * (25 * K ^ j) :=
        mul_le_mul_of_nonneg_left this h0
    _ = _ := by ring

theorem card_WN_le (N : ℕ) : ((WN N).card : ℝ) ≤ N + 1 := by
  have := card_filter_le (range (N + 1)) (fun w => w = 1 ∨ w.Prime)
  rw [card_range] at this; unfold WN; exact_mod_cast this

theorem WN_le {N w : ℕ} (hw : w ∈ WN N) : (w : ℝ) ≤ N := by
  have := (mem_filter.mp hw).1; exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp this)

theorem sum_pow_WN {N : ℕ} (hN : 1 ≤ N) (j : ℕ) : ∑ w ∈ WN N, (w : ℝ) ^ j ≤ 2 * (N : ℝ) ^ (j + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc ∑ w ∈ WN N, (w : ℝ) ^ j ≤ ∑ _w ∈ WN N, (N : ℝ) ^ j :=
        sum_le_sum fun w hw => pow_le_pow_left₀ (Nat.cast_nonneg w) (WN_le hw) j
    _ = (WN N).card * (N : ℝ) ^ j := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N + 1) * (N : ℝ) ^ j := mul_le_mul_of_nonneg_right (card_WN_le N) (by positivity)
    _ ≤ 2 * N * (N : ℝ) ^ j := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * (N : ℝ) ^ (j + 1) := by ring

/-- `u/s^k ≤ AD⁶e^{(a − 3k/2)L}` when `u ≤ Ae^{aL}`, `s ≥ e^{3L/2}/D`, `1 ≤ D`, `k ≤ 6`. -/
theorem norm_cum {u A a s D L : ℝ} {k : ℕ} (hk : k ≤ 6) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hu : u ≤ A * Real.exp (a * L)) (hs : Real.exp (3 / 2 * L) / D ≤ s) :
    u / s ^ k ≤ A * D ^ 6 * Real.exp ((a - 3 / 2 * k) * L) := by
  have hD0 : 0 < D := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hsk : Real.exp (3 / 2 * k * L) / D ^ k ≤ s ^ k := by
    have := pow_le_pow_left₀ (by positivity) hs k
    rwa [div_pow, ← Real.exp_nat_mul, show (k : ℝ) * (3 / 2 * L) = 3 / 2 * k * L by ring] at this
  rw [div_le_iff₀ (by positivity)]
  have hDk : D ^ k ≤ D ^ 6 := pow_le_pow_right₀ hD hk
  have he : Real.exp ((a - 3 / 2 * k) * L) * Real.exp (3 / 2 * k * L) = Real.exp (a * L) := by
    rw [← Real.exp_add]; ring_nf
  calc u ≤ A * Real.exp (a * L) := hu
    _ = A * D ^ k * Real.exp ((a - 3 / 2 * k) * L) * (Real.exp (3 / 2 * k * L) / D ^ k) := by
        rw [← he]; field_simp
    _ ≤ A * D ^ 6 * Real.exp ((a - 3 / 2 * k) * L) * s ^ k := by gcongr

set_option maxHeartbeats 16000000 in
/-- **Theorem E(2), the core** (paper §3.5, case `𝒱(a/q) = ∅`): fix `B > 0` and `0 < ε < 1/8`, put
`τ₀ = N^{−3/2+ε}`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1` with no vanishing factor at `a/q`, every
critical point `t*` of `log|G|` with `|t*| ≤ 4|ν|/S₂` (the peak of Lemma W) and every `T`:
`|∫_{|θ−θ*|≤τ₀/(2π)} F_N(e(θ))e(−Tθ)dθ − e(−Ta/q)Ĥ(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + e^{−N^{2ε}/(2048 log N)})`.
The only hypothesis is Siegel–Walfisz (through Lemma W). -/
theorem thmE2_core (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a →
      Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ‖Rcore N ((a : ℝ) / q + ts / (2 * π)) ((N : ℝ) ^ (-(3 / 2 : ℝ) + ε)) T -
            ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
          ‖FW (WN N) ((a : ℝ) / q + ts / (2 * π))‖ *
            ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sS N ((a : ℝ) / q + ts / (2 * π)) +
              Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  have hLamE : 0 ≤ LamE := sum_nonneg fun i _ => Am_nonneg _
  have hLamT : 0 ≤ LamT := by unfold LamT; have := Am_nonneg 0; have := Am_nonneg 3
                              have := Am_nonneg 4; have := Am_nonneg 6; positivity
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  have hε3 : (0 : ℝ) < 1 / 2 - 3 * ε := by linarith
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp B hc 1
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (6 * B) hε3 (16 * 8 ^ 6)
  obtain ⟨K₄, hK₄, hk4⟩ := ev_poly_exp (18 * B + 9) (by positivity : 0 < 2 * ε) (16 * K₀ ^ 3 * LamE)
  obtain ⟨K₅, hK₅, hk5⟩ := ev_poly_exp (12 * B + 6) one_pos (K₀ ^ 2 * LamT)
  obtain ⟨K₆, hK₆, hk6⟩ := ev_poly_exp (3 / 2) (by positivity : 0 < 2 * ε) 2048
  obtain ⟨K₇, hK₇, hk7⟩ := ev_poly_exp 1 one_pos 16
  set Kmax := max (max (max K₁ K₂) (max K₃ K₄)) (max (max K₅ K₆) K₇)
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha hnv ts hts hF T => ?_⟩
  obtain ⟨-, hS2pos, hwin, hrat, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL4 : K₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKL
  have hL5 : K₅ ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL6 : K₆ ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL7 : K₇ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKL
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
  -- `N|t*| ≤ 1/q`
  have hts' : Nr * |ts| ≤ 1 / q := by
    have h1 : Nr * |ts| ≤ Real.exp (-c * √L) := by
      have := hts.trans hrat; rw [le_div_iff₀ hNpos] at this; linarith
    have h2 : (q : ℝ) * Real.exp (-c * √L) ≤ 1 := by
      have := hk1 L hL1; rw [one_mul] at this
      have he : Real.exp (c * √L) * Real.exp (-c * √L) = 1 := by rw [← Real.exp_add]; simp
      calc (q : ℝ) * Real.exp (-c * √L) ≤ Real.exp (c * √L) * Real.exp (-c * √L) :=
            mul_le_mul_of_nonneg_right (hqL.trans this) (Real.exp_pos _).le
        _ = 1 := he
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-c * √L)]
  set θs := (a : ℝ) / q + ts / (2 * π) with hθs
  have hpar := fun w (hw : w ∈ WN N) => pStar_le hq hnv hts' hw
  have hne : ∀ w ∈ WN N, 1 + ee (w * θs) ≠ 0 := fun w hw => (hpar w hw).1
  have hpq : ∀ w ∈ WN N, ‖pStar θs w‖ ≤ q := fun w hw => (hpar w hw).2
  -- the cumulants
  set k1 : ℝ := ∑ w ∈ WN N, (w : ℝ) / 2
  have h1 : kap (WN N) (pStar θs) 1 = (k1 : ℂ) := kS_one hq hnv hts' hF
  set X : ℝ := ∑ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) with hX
  have h2X : kap (WN N) (pStar θs) 2 = (X : ℂ) := kS_two hq hnv hts'
  have hfilt : (WN N).filter (fun w => ¬ vanish q a w) = WN N := filter_true_of_mem hnv
  have htsw : |ts| < π / (q * Nr) := by
    have : |ts| ≤ 1 / (q * Nr) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at hts'; linarith
    exact lt_of_le_of_lt this (div_lt_div_of_pos_right (by linarith [Real.two_le_pi]) (by positivity))
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
  -- the window conditions
  set τ := Nr ^ (-(3 / 2 : ℝ) + ε) with hτdef
  have hτe : τ = Real.exp ((-(3 / 2) + ε) * L) := hrp _
  have hτ0 : 0 < τ := by rw [hτe]; exact Real.exp_pos _
  have hτ : 16 * q * Nr * τ ≤ 1 := by
    have h := hk2 L hL2
    have h' : 16 * (q : ℝ) ≤ Real.exp ((1 / 2 - ε) * L) :=
      (by nlinarith : 16 * (q : ℝ) ≤ 16 * L ^ B).trans (h.trans (Real.exp_le_exp.mpr (by nlinarith)))
    have e : Nr * τ = Real.exp ((-(1 / 2) + ε) * L) := by
      rw [hτe, ← hexpL, ← Real.exp_add]; congr 1; ring
    have he : Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc 16 * q * Nr * τ = 16 * q * (Nr * τ) := by ring
      _ ≤ Real.exp ((1 / 2 - ε) * L) * Real.exp ((-(1 / 2) + ε) * L) := by
          rw [e]; exact mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = 1 := he
  have hy : α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 ≤ 1 := by
    have hτk : ∀ k : ℕ, τ ^ k = Real.exp (k * ((-(3 / 2) + ε) * L)) := fun k => by
      rw [hτe, ← Real.exp_nat_mul]
    set E0 := Real.exp ((-(1 / 2) + 3 * ε) * L)
    have hterm : ∀ (u : ℝ) (j : ℕ), 3 ≤ j → u ≤ A * Real.exp ((j + 1) * L) → u * τ ^ j ≤ A * E0 := by
      intro u j hj hu
      rw [hτk]
      calc u * Real.exp (j * ((-(3 / 2) + ε) * L)) ≤ A * Real.exp ((j + 1) * L) * Real.exp (j * ((-(3 / 2) + ε) * L)) :=
            mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
        _ = A * Real.exp ((1 - j * (1 / 2 - ε)) * L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ A * E0 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
            have : (3 : ℝ) ≤ j := by exact_mod_cast hj
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr this) hε1.le) hL0.le]
    have t3 := hterm α3 3 le_rfl (by norm_num; exact hα3)
    have t4 := hterm α4 4 (by norm_num) (by norm_num; exact hα4)
    have t5 := hterm α5 5 (by norm_num) (by norm_num; exact hα5)
    have t6 := hterm ρ 6 (by norm_num) (by norm_num; exact hρb)
    have h4A : 4 * A * E0 ≤ 1 := by
      have h := hk3 L hL3
      have hq6 : (q : ℝ) ^ 6 ≤ L ^ (6 * B) := by
        rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
        exact pow_le_pow_left₀ (by linarith) hqL 6
      have h' : 4 * A ≤ Real.exp ((1 / 2 - 3 * ε) * L) := by
        rw [hA]
        calc 4 * (4 * 8 ^ 6 * (q : ℝ) ^ 6) = 16 * 8 ^ 6 * (q : ℝ) ^ 6 := by ring
          _ ≤ 16 * 8 ^ 6 * L ^ (6 * B) := by gcongr
          _ ≤ Real.exp ((1 / 2 - 3 * ε) * √L) := h
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
      have he : Real.exp ((1 / 2 - 3 * ε) * L) * E0 = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      nlinarith [Real.exp_pos ((-(1 / 2) + 3 * ε) * L)]
    linarith
  -- the abstract core
  have hcore := core_int (WN N) (pStar θs) hq1 hpq hWN hτ hτ0 hs0 h1 h2 (by
    have e : ‖kap (WN N) (pStar θs) 3‖ / 6 * τ ^ 3 + ‖kap (WN N) (pStar θs) 4‖ / 24 * τ ^ 4 +
        ‖kap (WN N) (pStar θs) 5‖ / 120 * τ ^ 5 + 2 * 8 ^ 6 * (q : ℝ) ^ 6 * (∑ w ∈ WN N, (w : ℝ) ^ 6) * τ ^ 6 =
        α3 * τ ^ 3 + α4 * τ ^ 4 + α5 * τ ^ 5 + ρ * τ ^ 6 := by rw [hρ]; try ring
    rw [e]; exact hy) T
  -- the identity `Rcore − e(−Ta/q)Ĥ = G(θ*) e(−Tθ*) (I − mainE)`
  have hee : ee (-(T * θs)) = ee (-(T * ((a : ℝ) / q))) * Complex.exp (-(I * T * ts)) := by
    rw [hθs, show -(T * ((a : ℝ) / q + ts / (2 * π))) = -(T * ((a : ℝ) / q)) + (-(T * ts)) / (2 * π) by ring,
      ee_add, ee_div_two_pi]; push_cast; ring_nf
  have hid : Rcore N θs τ T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts θs T =
      FW (WN N) θs * ee (-(T * θs)) * ((1 / (2 * π) : ℂ) *
        (∫ σ in (-τ)..τ, (∏ w ∈ WN N, (1 + pStar θs w * (Complex.exp (I * w * σ) - 1))) *
          Complex.exp (-(I * T * σ))) - mainE k1 s (kap (WN N) (pStar θs) 3) (kap (WN N) (pStar θs) 4) T) := by
    rw [Rcore_eq N θs τ T hne, hee]
    unfold Hhat
    have : (kS N θs 1).re = k1 := by unfold kS; rw [h1, Complex.ofReal_re]
    rw [this]; unfold kS; ring
  rw [hid, norm_mul, norm_mul, norm_ee, mul_one]
  refine mul_le_mul_of_nonneg_left (hcore.trans ?_) (norm_nonneg _)
  -- the size of the error
  set M := A * D ^ 6 with hM
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [one_le_pow₀ (n := 6) hD1]
  set x := Real.exp (-(1 / 2) * L) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hxk : ∀ k : ℕ, x ^ k = Real.exp (-(k / 2 : ℝ) * L) := fun k => by
    rw [hx, ← Real.exp_nat_mul]; congr 1; ring
  have b3 : α3 / s ^ 3 ≤ M * x := by
    have := norm_cum (k := 3) (by norm_num) (by linarith) hD1 hα3 hsD
    rw [hx]; convert this using 2; push_cast; ring_nf
  have b4 : α4 / s ^ 4 ≤ M * x ^ 2 := by
    have := norm_cum (k := 4) (by norm_num) (by linarith) hD1 hα4 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have b5 : α5 / s ^ 5 ≤ M * x ^ 3 := by
    have := norm_cum (k := 5) (by norm_num) (by linarith) hD1 hα5 hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have br : ρ / s ^ 6 ≤ M * x ^ 4 := by
    have := norm_cum (k := 6) (by norm_num) (by linarith) hD1 hρb hsD
    rw [hxk]; convert this using 2; push_cast; ring_nf
  have hEI := EI_le hs0 hα30 hα40 hα50 hρ0 hM1 hx0 hx1 b3 b4 b5 br
  have hTI := TI_le hs0 hα30 hα40 hM1 (b3.trans (by nlinarith)) (b4.trans (by nlinarith [pow_le_one₀ hx0 hx1 (n := 2)]))
  -- polylog factors
  have hMle : M ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hM, hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : (q : ℝ) ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hLB6 : 0 ≤ L ^ (6 * B) := by positivity
  have hpow : ∀ k : ℕ, (L ^ (6 * B) * L ^ 3) ^ k = L ^ ((6 * B + 3) * k) := by
    intro k
    have h63 : L ^ (6 * B) * L ^ 3 = L ^ (6 * B + 3) := by
      rw [Real.rpow_add hL0, show L ^ (3 : ℝ) = L ^ 3 by norm_cast]
    rw [h63, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hM3 : 16 * M ^ 3 * LamE ≤ Real.exp (2 * ε * L) := by
    have h := hk4 L hL4
    have e : L ^ (18 * B + 9) = (L ^ (6 * B) * L ^ 3) ^ 3 := by rw [hpow]; congr 1; push_cast; ring
    have hm3 : M ^ 3 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 := pow_le_pow_left₀ hM0 (by linarith) 3
    calc 16 * M ^ 3 * LamE ≤ 16 * (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 3 * LamE := by gcongr
      _ = 16 * K₀ ^ 3 * LamE * L ^ (18 * B + 9) := by rw [e]; ring
      _ ≤ Real.exp (2 * ε * √L) := h
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hM2 : M ^ 2 * LamT ≤ Real.exp (√L) := by
    have h := hk5 L hL5
    have e : L ^ (12 * B + 6) = (L ^ (6 * B) * L ^ 3) ^ 2 := by rw [hpow]; congr 1; push_cast; ring
    have hm2 : M ^ 2 ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 := pow_le_pow_left₀ hM0 (by linarith) 2
    calc M ^ 2 * LamT ≤ (K₀ * (L ^ (6 * B) * L ^ 3)) ^ 2 * LamT := by gcongr
      _ = K₀ ^ 2 * LamT * L ^ (12 * B + 6) := by rw [e]; ring
      _ ≤ Real.exp (1 * √L) := h
      _ = _ := by rw [one_mul]
  -- the main part
  have hpart1 : EI α3 α4 α5 ρ s ≤ Nr ^ (-(3 / 2 : ℝ) + 2 * ε) / s := by
    refine hEI.trans ?_
    rw [div_le_div_iff_of_pos_right hs0, hrp]
    have e : Real.exp ((-(3 / 2) + 2 * ε) * L) = x ^ 3 * Real.exp (2 * ε * L) := by
      rw [hxk, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e]
    have : 0 ≤ x ^ 3 := by positivity
    nlinarith
  -- the tail
  have hE2 : Real.exp (2 * ε * L) / (256 * L) ≤ s ^ 2 * τ ^ 2 := by
    have h1' : (Real.exp (3 / 2 * L) / D) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hsD 2
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 * τ ^ 2 = Real.exp (2 * ε * L) / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hτe, ← Real.exp_nat_mul,
        div_mul_eq_mul_div, ← Real.exp_add]
      congr 1
      · congr 1; push_cast; ring
      · norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right h1' (by positivity)
  have hpart2 : Real.exp (-(s ^ 2 * τ ^ 2) / 4) * TI α3 α4 s ≤
      Real.exp (-(Nr ^ (2 * ε)) / (2048 * L)) := by
    rw [hrp]
    set E := Real.exp (2 * ε * L)
    have hEpos : 0 < E := Real.exp_pos _
    have h6 := hk6 L hL6
    have hL32 : L ^ (3 / 2 : ℝ) = L * √L := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL0, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hL32] at h6
    have hsqE : √L ≤ E / (2048 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2048 * (L * √L) ≤ E := h6.trans (Real.exp_le_exp.mpr (by nlinarith))
      linarith
    have hTs : TI α3 α4 s ≤ M ^ 2 * LamT := by
      refine hTI.trans ?_
      rw [div_le_iff₀ hs0]
      have : 0 ≤ M ^ 2 * LamT := by positivity
      nlinarith
    calc Real.exp (-(s ^ 2 * τ ^ 2) / 4) * TI α3 α4 s
        ≤ Real.exp (-(E / (256 * L)) / 4) * (M ^ 2 * LamT) := by
          have hTI0 : 0 ≤ TI α3 α4 s := by
            unfold TI; have := Am_nonneg 0; have := Am_nonneg 3; have := Am_nonneg 4; have := Am_nonneg 6
            positivity
          exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hTs hTI0 (Real.exp_pos _).le
      _ ≤ Real.exp (-(E / (256 * L)) / 4) * Real.exp (E / (2048 * L)) := by
          gcongr; exact hM2.trans (Real.exp_le_exp.mpr hsqE)
      _ = Real.exp (-E / (2048 * L)) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
  have h2pi : 1 / (2 * π) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hb1 : 0 ≤ Nr ^ (-(3 / 2 : ℝ) + 2 * ε) / s := by positivity
  have hb2 : 0 ≤ Real.exp (-(Nr ^ (2 * ε)) / (2048 * L)) := (Real.exp_pos _).le
  calc 1 / (2 * π) * (EI α3 α4 α5 ρ s + Real.exp (-(s ^ 2 * τ ^ 2) / 4) * TI α3 α4 s)
      ≤ 1 / (2 * π) * (Nr ^ (-(3 / 2 : ℝ) + 2 * ε) / s + Real.exp (-(Nr ^ (2 * ε)) / (2048 * L))) := by
        gcongr
    _ ≤ 1 * (Nr ^ (-(3 / 2 : ℝ) + 2 * ε) / s + Real.exp (-(Nr ^ (2 * ε)) / (2048 * L))) := by gcongr
    _ = _ := one_mul _

end ArcsAlgo.Core
