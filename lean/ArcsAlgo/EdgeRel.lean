module

public import ArcsAlgo.EdgeE2
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false

/-!
# Theorem E(2), relative form (paper §3.5, "In particular")

* `He_le`, `mainE_ge`: for `z² ≤ L` and small normalized cumulants the Edgeworth bracket is `≥ 1/2`, so
  `|mainE(T)| ≥ φ(z)/(2s)`.
* `thmE2_rel`: if `𝒱(a/q) = ∅`, then uniformly for `|z| ≤ √(log N)`,
  `|R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ 12N^{−1+2ε}|𝒜*_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`, i.e.
  `R = 𝒜*(1 + O(N^{−1+2ε})) + O(2^n e^{(−log 2 + ℓ*_q + o(1))π(N)})`.

The only hypothesis is `SiegelWalfisz`.
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- `|He_k(z)| ≤ c_k L³` for `z² ≤ L`, `L ≥ 1` (`k = 3, 4, 6`). -/
theorem He_le {z L : ℝ} (hL : 1 ≤ L) (hz : z ^ 2 ≤ L) :
    |He 3 z| ≤ 4 * L ^ 3 ∧ |He 4 z| ≤ 10 * L ^ 3 ∧ |He 6 z| ≤ 76 * L ^ 3 := by
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have ha : |z| ≤ L := by
    have : |z| ^ 2 ≤ L ^ 2 := by rw [sq_abs]; nlinarith
    exact (pow_le_pow_iff_left₀ (abs_nonneg z) (by linarith) (by norm_num)).mp this
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL3 : L ^ 2 ≤ L ^ 3 := by nlinarith
  have h4 : z ^ 4 ≤ L ^ 2 := by nlinarith
  have h6 : z ^ 6 ≤ L ^ 3 := by nlinarith [mul_le_mul h4 hz hz0 (by positivity)]
  have hz3 : |z| ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (abs_nonneg z) ha 3
  simp only [He]
  refine ⟨?_, ?_, ?_⟩
  · calc |z ^ 3 - 3 * z| ≤ |z| ^ 3 + 3 * |z| := by
          rw [← abs_pow]; refine (abs_sub _ _).trans ?_; rw [abs_mul]; norm_num
      _ ≤ 4 * L ^ 3 := by have : |z| ≤ L ^ 3 := ha.trans (hL2.trans hL3); linarith
  · rw [abs_le]; constructor <;> nlinarith
  · have hLL : L ≤ L ^ 3 := hL2.trans hL3
    have h1 : 1 ≤ L ^ 3 := by nlinarith
    have h44 : z ^ 4 ≤ L ^ 3 := h4.trans hL3
    have h66 : 0 ≤ z ^ 6 := by positivity
    have h40 : 0 ≤ z ^ 4 := by positivity
    rw [abs_le]; constructor <;> linarith

/-- **The Edgeworth bracket is `≥ 1/2`**: if `|κ₃|/(6s³), |κ₄|/(24s⁴) ≤ u` and `52L³u ≤ 1/2`, `u ≤ 1`, then
`|mainE(T)| ≥ φ(z)/(2s)` for `z² ≤ L`. -/
theorem mainE_ge {k1 s L u : ℝ} {κ₃ κ₄ : ℂ} (hs : 0 < s) (hL : 1 ≤ L) (T : ℝ)
    (hz : ((T - k1) / s) ^ 2 ≤ L) (h3 : ‖κ₃‖ / 6 / s ^ 3 ≤ u) (h4 : ‖κ₄‖ / 24 / s ^ 4 ≤ u) (hu1 : u ≤ 1)
    (hu : 52 * L ^ 3 * u ≤ 1 / 2) :
    phiN ((T - k1) / s) / (2 * s) ≤ ‖mainE k1 s κ₃ κ₄ T‖ := by
  set z := (T - k1) / s
  obtain ⟨b3, b4, b6⟩ := He_le hL hz
  have hu0 : 0 ≤ u := le_trans (by positivity) h3
  have hφ : 0 ≤ phiN z / s := by unfold phiN; positivity
  unfold mainE
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ]
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have n3 : ‖κ₃ * (He 3 z : ℂ) / (6 * (s : ℂ) ^ 3)‖ ≤ 4 * L ^ 3 * u := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, Complex.norm_ofNat]
    calc ‖κ₃‖ * |He 3 z| / (6 * s ^ 3) = ‖κ₃‖ / 6 / s ^ 3 * |He 3 z| := by ring
      _ ≤ u * (4 * L ^ 3) := mul_le_mul h3 b3 (abs_nonneg _) hu0
      _ = _ := by ring
  have n4 : ‖κ₄ * (He 4 z : ℂ) / (24 * (s : ℂ) ^ 4)‖ ≤ 10 * L ^ 3 * u := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, Complex.norm_ofNat]
    calc ‖κ₄‖ * |He 4 z| / (24 * s ^ 4) = ‖κ₄‖ / 24 / s ^ 4 * |He 4 z| := by ring
      _ ≤ u * (10 * L ^ 3) := mul_le_mul h4 b4 (abs_nonneg _) hu0
      _ = _ := by ring
  have n6 : ‖κ₃ ^ 2 * (He 6 z : ℂ) / (72 * (s : ℂ) ^ 6)‖ ≤ 38 * L ^ 3 * u := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, Complex.norm_ofNat]
    have hq : (‖κ₃‖ / 6 / s ^ 3) ^ 2 ≤ u := by
      have := pow_le_pow_left₀ (by positivity) h3 2; nlinarith
    calc ‖κ₃‖ ^ 2 * |He 6 z| / (72 * s ^ 6) = (‖κ₃‖ / 6 / s ^ 3) ^ 2 / 2 * |He 6 z| := by field_simp; ring
      _ ≤ u / 2 * (76 * L ^ 3) := mul_le_mul (by linarith) b6 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hb : 1 / 2 ≤ ‖1 + κ₃ * (He 3 z : ℂ) / (6 * (s : ℂ) ^ 3) + κ₄ * (He 4 z : ℂ) / (24 * (s : ℂ) ^ 4) +
      κ₃ ^ 2 * (He 6 z : ℂ) / (72 * (s : ℂ) ^ 6)‖ := by
    set a := κ₃ * (He 3 z : ℂ) / (6 * (s : ℂ) ^ 3)
    set b := κ₄ * (He 4 z : ℂ) / (24 * (s : ℂ) ^ 4)
    set c := κ₃ ^ 2 * (He 6 z : ℂ) / (72 * (s : ℂ) ^ 6)
    have h := norm_sub_norm_le (1 : ℂ) (-(a + b + c))
    rw [sub_neg_eq_add, norm_one, norm_neg] at h
    have := norm_add₃_le (a := a) (b := b) (c := c)
    have e : (1 : ℂ) + (a + b + c) = 1 + a + b + c := by ring
    rw [e] at h
    linarith
  calc phiN z / (2 * s) = phiN z / s * (1 / 2) := by ring
    _ ≤ phiN z / s * _ := mul_le_mul_of_nonneg_left hb hφ


set_option maxHeartbeats 8000000 in
/-- **Theorem E(2), relative form** (paper §3.5, "In particular"): if `𝒱(a/q) = ∅`, then for `N ≥ N₀`,
uniformly for `|z| ≤ √(log N)`, `z = (T − κ₁*)/s*`:
`|R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ 12 N^{−1+2ε}|𝒜*_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}`,
`𝒜*_{a/q}(T) = e(−Ta/q)Ĥ(T)`, i.e. `R = 𝒜*(1 + O(N^{−1+2ε})) + O(2^n e^{(−log 2 + ℓ*_q + o(1))π(N)})`.
The only hypothesis is Siegel–Walfisz. -/
theorem thmE2_rel (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((T - (kS N ((a : ℝ) / q + ts / (2 * π)) 1).re) / sS N ((a : ℝ) / q + ts / (2 * π))) ^ 2 ≤ Real.log N →
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
          12 * (N : ℝ) ^ (-1 + 2 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)) := by
  obtain ⟨N₀, hE2⟩ := thmE2 hSW hB hε0 hε hδ
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  set K₀ : ℝ := 4 * 8 ^ 6 * 16 ^ 6 with hK₀
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp B hc 1
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp (6 * B + 6) (by norm_num : (0 : ℝ) < 1 / 2) (104 * K₀)
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp 2 (by positivity : 0 < 2 * ε) (2048 * (B + 6))
  set Kmax := max (max K₁ K₂) K₃
  refine ⟨N₀ + N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP he ha hnv ts hts hF T hz => ?_⟩
  have hmain := (hE2 N (by omega) q a hq hqP he ha ts hts hF T).1 hnv
  obtain ⟨-, hS2pos, hwin, hrat, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKL
  have hL3 : K₃ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hnp : ∀ k : ℕ, Nr ^ k = Real.exp (k * L) := fun k => by rw [← hexpL, ← Real.exp_nat_mul]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
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
  have hpq : ∀ w ∈ WN N, ‖pStar θs w‖ ≤ q := fun w hw => (pStar_le hq hnv hts' hw).2
  -- `s*`
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
  have hXle : X ≤ 2 * (q : ℝ) ^ 2 * Nr ^ 3 := by
    have hterm : ∀ w ∈ WN N, (w : ℝ) ^ 2 / (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) ≤ (q : ℝ) ^ 2 * (w : ℝ) ^ 2 := by
      intro w hw
      have hc := cos_star_ge hq hnv hts' hw
      rw [arg_eq q a w ts] at hc
      have hc2 : 1 / (4 * (q : ℝ) ^ 2) ≤ Real.cos (alw q a w + w * ts / 2) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hc 2
        rw [sq_abs] at this; convert this using 1; field_simp; ring
      have hpos : 0 < 4 * Real.cos (alw q a w + w * ts / 2) ^ 2 := by
        have : 0 < 1 / (4 * (q : ℝ) ^ 2) := by positivity
        linarith
      rw [div_le_iff₀ hpos]
      have : 1 ≤ (q : ℝ) ^ 2 * (4 * Real.cos (alw q a w + w * ts / 2) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ) ^ 2)
        rw [show 4 * (q : ℝ) ^ 2 * (1 / (4 * (q : ℝ) ^ 2)) = 1 by field_simp] at this
        linarith
      nlinarith [sq_nonneg (w : ℝ)]
    calc X ≤ ∑ w ∈ WN N, (q : ℝ) ^ 2 * (w : ℝ) ^ 2 := sum_le_sum hterm
      _ = (q : ℝ) ^ 2 * ∑ w ∈ WN N, (w : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ (q : ℝ) ^ 2 * (2 * Nr ^ 3) := by
          gcongr; have := sum_pow_WN (N := N) (by omega) 2; rw [← hNr] at this; exact this
      _ = _ := by ring
  set s := sS N θs with hsdef
  have hsX : s = √X := by rw [hsdef]; unfold sS kS; rw [h2X, Complex.ofReal_re]
  have hs0 : 0 < s := by rw [hsX]; exact Real.sqrt_pos.mpr hX0
  have hs2 : s ^ 2 = X := by rw [hsX, Real.sq_sqrt hX0.le]
  set D := 16 * √L with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hL0.le |>.mpr (by linarith)]
  have hsD : Real.exp (3 / 2 * L) / D ≤ s := by
    rw [hsX, Real.le_sqrt (by positivity) hX0.le]
    have e : (Real.exp (3 / 2 * L) / D) ^ 2 = Nr ^ 3 / (256 * L) := by
      rw [div_pow, ← Real.exp_nat_mul, hD, mul_pow, Real.sq_sqrt hL0.le, hnp 3]
      congr 1; push_cast; ring_nf; ring
    rw [e]
    have e2 : Nr ^ 3 / (256 * L) = Nr ^ 3 / (64 * L) / 4 := by field_simp; ring
    linarith
  have hsU : s ≤ 2 * L ^ B * Real.exp (3 / 2 * L) := by
    rw [hsX, Real.sqrt_le_left (by positivity)]
    have : (2 * L ^ B * Real.exp (3 / 2 * L)) ^ 2 = 4 * (L ^ B) ^ 2 * Nr ^ 3 := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul, hnp 3]; push_cast; ring_nf
    rw [this]
    have hq2 : (q : ℝ) ^ 2 ≤ (L ^ B) ^ 2 := pow_le_pow_left₀ hq0.le hqL 2
    nlinarith [pow_pos hNpos 3]
  -- the normalized cumulants
  set A : ℝ := 4 * 8 ^ 6 * (q : ℝ) ^ 6 with hA
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
  have hα3 : ‖kS N θs 3‖ / 6 ≤ A * Real.exp (4 * L) := by
    have := hα 3 le_rfl (by norm_num); norm_num [Nat.factorial] at this; exact this
  have hα4 : ‖kS N θs 4‖ / 24 ≤ A * Real.exp (5 * L) := by
    have := hα 4 (by norm_num) (by norm_num); norm_num [Nat.factorial] at this; exact this
  set u := A * D ^ 6 * Real.exp (-(1 / 2) * L) with hu
  have hu3 : ‖kS N θs 3‖ / 6 / s ^ 3 ≤ u := by
    have := norm_cum (k := 3) (by norm_num) (by positivity) hD1 hα3 hsD
    rw [hu]; convert this using 3; push_cast; ring
  have hu4 : ‖kS N θs 4‖ / 24 / s ^ 4 ≤ u := by
    have := norm_cum (k := 4) (by norm_num) (by positivity) hD1 hα4 hsD
    refine this.trans ?_
    rw [hu]; gcongr; push_cast; nlinarith
  have hAD : A * D ^ 6 ≤ K₀ * L ^ (6 * B) * L ^ 3 := by
    rw [hA, hD, hK₀, mul_pow, show √L ^ 6 = L ^ 3 by
      rw [show √L ^ 6 = (√L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]]
    have hq6 : (q : ℝ) ^ 6 ≤ L ^ (6 * B) := by
      rw [show L ^ (6 * B) = (L ^ B) ^ 6 by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf]
      exact pow_le_pow_left₀ (by linarith) hqL 6
    have : (0 : ℝ) ≤ L ^ 3 := by positivity
    nlinarith
  have h52 : 52 * L ^ 3 * u ≤ 1 / 2 := by
    have h := hk2 L hL2
    have e : L ^ (6 * B + 6) = L ^ (6 * B) * L ^ 3 * L ^ 3 := by
      rw [Real.rpow_add hL0, show L ^ (6 : ℝ) = L ^ 3 * L ^ 3 by norm_cast; ring]; ring
    rw [e] at h
    have h' : 104 * (A * D ^ 6) * L ^ 3 ≤ Real.exp (1 / 2 * L) := by
      have : 104 * (A * D ^ 6) * L ^ 3 ≤ 104 * K₀ * (L ^ (6 * B) * L ^ 3 * L ^ 3) := by
        have : (0 : ℝ) ≤ L ^ 3 := by positivity
        nlinarith
      exact this.trans (h.trans (Real.exp_le_exp.mpr (by nlinarith)))
    have he : Real.exp (1 / 2 * L) * Real.exp (-(1 / 2) * L) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    rw [hu]
    have hp : 0 < Real.exp (-(1 / 2) * L) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_right h' hp.le]
  have hu1 : u ≤ 1 := by
    have : 0 ≤ u := by positivity
    have : 1 ≤ 52 * L ^ 3 := by nlinarith [one_le_pow₀ (n := 3) hLone]
    nlinarith
  have hmE := mainE_ge hs0 hLone T hz hu3 hu4 hu1 h52
  -- `|𝒜*| ≥ |G(θ*)| e^{−L/2}/(2√(2π)s)`
  set G := ‖Gw (WN N) q a θs‖
  have hGF : G = ‖FW (WN N) θs‖ := by simp only [G]; rw [Gw_eq_FW hnv]
  have hsq : Real.sqrt (2 * π) ≤ 13 / 5 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d2]
  have hsq0 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hphi : Real.exp (-(L / 2)) / Real.sqrt (2 * π) ≤ phiN ((T - (kS N θs 1).re) / s) := by
    unfold phiN
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hsq0.le
  have hAs : G * (Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s)) ≤
      ‖ee (-(T * ((a : ℝ) / q))) * Hhat N ts θs T‖ := by
    unfold Hhat
    rw [norm_mul, norm_ee, one_mul, norm_mul, norm_mul, norm_cexp_IT, one_mul, ← hGF]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans ?_ hmE
    rw [show Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s) = Real.exp (-(L / 2)) / Real.sqrt (2 * π) / (2 * s) by
      field_simp]
    exact div_le_div_of_nonneg_right hphi (by positivity)
  -- the error against `12 N^{−1+2ε}|𝒜*|`
  set e_ := Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))
  have he_ : 5 * e_ ≤ Real.exp ((-(3 / 2) + 2 * ε) * L) / s := by
    rw [le_div_iff₀ hs0]
    have h3 := hk3 L hL3
    have hE : 2048 * (B + 6) * L ^ 2 ≤ Real.exp (2 * ε * L) := by
      have : L ^ (2 : ℝ) = L ^ 2 := by norm_cast
      rw [this] at h3; exact h3.trans (Real.exp_le_exp.mpr (by nlinarith))
    have hlogLB : Real.log (L ^ B) ≤ B * L := by
      rw [Real.log_rpow hL0]; exact mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos hL0]) hB.le
    have hNe : (N : ℝ) ^ (2 * ε) = Real.exp (2 * ε * L) := hrp _
    -- `log(10 L^B e^{3L}) ≤ e^{2εL}/(2048L)`
    have hk : Real.log 10 + B * L + 3 * L ≤ Real.exp (2 * ε * L) / (2048 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : Real.log 10 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h := Real.exp_one_gt_d9
        have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        have h3 : (27 / 10 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        norm_num at h3 ⊢; linarith
      have h1 : Real.log 10 * (2048 * L) ≤ 3 * (2048 * L) := mul_le_mul_of_nonneg_right this (by positivity)
      have h2 : L ≤ L ^ 2 := by nlinarith
      have e2 : (Real.log 10 + B * L + 3 * L) * (2048 * L) =
          Real.log 10 * (2048 * L) + 2048 * B * L ^ 2 + 6144 * L ^ 2 := by ring
      rw [e2]
      have e3 : 2048 * (B + 6) * L ^ 2 = 2048 * B * L ^ 2 + 12288 * L ^ 2 := by ring
      linarith
    have hprod : 10 * L ^ B * Real.exp (3 * L) * e_ ≤ 1 := by
      have : 10 * L ^ B * Real.exp (3 * L) = Real.exp (Real.log 10 + Real.log (L ^ B) + 3 * L) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by positivity)]
      rw [this, show e_ = Real.exp (-(Real.exp (2 * ε * L)) / (2048 * L)) by simp only [e_]; rw [hNe]]
      rw [← Real.exp_add, Real.exp_le_one_iff, neg_div]
      linarith
    have he0 : 0 ≤ e_ := (Real.exp_pos _).le
    have h1 : 5 * e_ * s ≤ 5 * e_ * (2 * L ^ B * Real.exp (3 / 2 * L)) := mul_le_mul_of_nonneg_left hsU (by positivity)
    have h2 : 5 * e_ * (2 * L ^ B * Real.exp (3 / 2 * L)) * Real.exp (3 / 2 * L) ≤ Real.exp ((-(3 / 2) + 2 * ε) * L) * Real.exp (3 / 2 * L) := by
      have e1 : 5 * e_ * (2 * L ^ B * Real.exp (3 / 2 * L)) * Real.exp (3 / 2 * L) = 10 * L ^ B * Real.exp (3 * L) * e_ := by
        rw [show Real.exp (3 * L) = Real.exp (3 / 2 * L) * Real.exp (3 / 2 * L) by rw [← Real.exp_add]; ring_nf]; ring
      have e2 : Real.exp ((-(3 / 2) + 2 * ε) * L) * Real.exp (3 / 2 * L) = Real.exp (2 * ε * L) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, e2]
      exact hprod.trans (Real.one_le_exp (by positivity))
    have h3 := le_of_mul_le_mul_right h2 (Real.exp_pos (3 / 2 * L))
    linarith
  refine hmain.trans ?_
  have hNm : (N : ℝ) ^ (-1 + 2 * ε) = Real.exp ((-1 + 2 * ε) * L) := hrp _
  have hN3 : (N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) = Real.exp ((-(3 / 2) + 2 * ε) * L) := hrp _
  rw [hN3]
  set Lb := 2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)
  have hG0 : 0 ≤ G := norm_nonneg _
  have hkey : G * (Real.exp ((-(3 / 2) + 2 * ε) * L) / s + 5 * e_) ≤
      12 * Real.exp ((-1 + 2 * ε) * L) * (G * (Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s))) := by
    have e : 12 * Real.exp ((-1 + 2 * ε) * L) * (Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s)) =
        6 / Real.sqrt (2 * π) * (Real.exp ((-(3 / 2) + 2 * ε) * L) / s) := by
      rw [show Real.exp ((-(3 / 2) + 2 * ε) * L) = Real.exp ((-1 + 2 * ε) * L) * Real.exp (-(L / 2)) by
        rw [← Real.exp_add]; ring_nf]
      field_simp; ring
    have h6 : 2 ≤ 6 / Real.sqrt (2 * π) := by rw [le_div_iff₀ hsq0]; linarith
    have hb : 0 ≤ Real.exp ((-(3 / 2) + 2 * ε) * L) / s := by positivity
    rw [show 12 * Real.exp ((-1 + 2 * ε) * L) * (G * (Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s))) =
      G * (12 * Real.exp ((-1 + 2 * ε) * L) * (Real.exp (-(L / 2)) / (2 * Real.sqrt (2 * π) * s))) by ring, e]
    refine mul_le_mul_of_nonneg_left ?_ hG0
    nlinarith
  have := mul_le_mul_of_nonneg_left hAs (by positivity : (0 : ℝ) ≤ 12 * Real.exp ((-1 + 2 * ε) * L))
  rw [hNm]
  linarith

end ArcsAlgo.Core
