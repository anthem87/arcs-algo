module

public import ArcsAlgo.EdgeArc2
set_option autoImplicit false

/-!
# Theorem E(2), the shoulder (paper §3.5)

* `Fw_quad` (Lemma W(1)): in the window, at a critical point `t*`, `F(t) ≤ F(t*) − S₂(t − t*)²/8`
  (`F″ ≤ −S₂/4`; mean value theorem for `F + S₂(t − t*)²/8`).
* `FW_le_Gw`: `|F_N| ≤ 2|G|` (the vanishing factor, if any, is `≤ 2`).
* `Gw_pos`, `norm_Gw_eq`: `|G(a/q + t/(2π))| = e^{F(t)}` in the window.
* `shoulder_pt`: at distance `≥ τ` from the peak, `|F_N| ≤ 2|G(θ*)|e^{−S₂τ²/8}`.
* `thmE2_shoulder`: both ranges `τ₀ < |t − t*|`, `|t| < π/(qN)` lie inside the window and each
  contributes `≤ 2|G(θ*)|e^{−N^{2ε}/(512 log N)}`, uniformly in `T`.

The only hypothesis is `SiegelWalfisz` (through Lemma W).
-/

open Finset Complex MeasureTheory
open scoped Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

section quad

variable {W : Finset ℕ} {q a N : ℕ}

/-- **Lemma W(1), quadratic decay**: in the window, `F(t) ≤ F(t*) − S₂(t − t*)²/8` at a critical point
`t*` (`F″ ≤ −S₂/4`). -/
theorem Fw_quad (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {ts : ℝ}
    (hts : |ts| < π / (q * N)) (hzero : Fw' W q a ts = 0) {t : ℝ} (ht : |t| < π / (q * N)) :
    Fw W q a t ≤ Fw W q a ts - S2W W q a / 8 * (t - ts) ^ 2 := by
  set δ := π / (q * N)
  set S := S2W W q a
  set h : ℝ → ℝ := fun r => Fw W q a r + S / 8 * (r - ts) ^ 2
  have hder : ∀ r, |r| < δ → HasDerivAt h (Fw' W q a r + S / 4 * (r - ts)) r := by
    intro r hr
    have h1 := hasDerivAt_Fw (a := a) hq hN hWN hr
    have h2 : HasDerivAt (fun r : ℝ => S / 8 * (r - ts) ^ 2) (S / 4 * (r - ts)) r := by
      refine ((((hasDerivAt_id r).sub_const ts).pow 2).const_mul (S / 8)).congr_deriv ?_
      simp; ring
    exact h1.add h2
  have hin : ∀ x y z, |x| < δ → |y| < δ → z ∈ Set.Icc x y → |z| < δ := fun x y z hx hy hz => by
    rw [abs_lt] at hx hy ⊢; constructor <;> linarith [hz.1, hz.2]
  have hstr := fun s t (hs : |s| < δ) (ht : |t| < δ) (hst : s ≤ t) => Fw'_strong (a := a) hq hN hWN hs ht hst
  have hmvt : ∀ x y, |x| < δ → |y| < δ → x < y → ∃ c ∈ Set.Ioo x y,
      h y - h x = (Fw' W q a c + S / 4 * (c - ts)) * (y - x) := by
    intro x y hx hy hxy
    have hc : ContinuousOn h (Set.Icc x y) := fun z hz => (hder z (hin x y z hx hy hz)).continuousAt.continuousWithinAt
    obtain ⟨c, hcm, hcd⟩ := exists_hasDerivAt_eq_slope h (fun r => Fw' W q a r + S / 4 * (r - ts)) hxy hc
      fun z hz => hder z (hin x y z hx hy ⟨hz.1.le, hz.2.le⟩)
    exact ⟨c, hcm, by rw [hcd]; field_simp⟩
  have key : h t ≤ h ts := by
    rcases lt_trichotomy t ts with hlt | heq | hgt
    · obtain ⟨c, hc, hcd⟩ := hmvt t ts ht hts hlt
      have hcδ := hin t ts c ht hts ⟨hc.1.le, hc.2.le⟩
      have := hstr c ts hcδ hts hc.2.le
      rw [hzero] at this
      have : 0 ≤ Fw' W q a c + S / 4 * (c - ts) := by linarith
      nlinarith [hc.2]
    · rw [heq]
    · obtain ⟨c, hc, hcd⟩ := hmvt ts t hts ht hgt
      have hcδ := hin ts t c hts ht ⟨hc.1.le, hc.2.le⟩
      have := hstr ts c hts hcδ hc.1.le
      rw [hzero] at this
      have : Fw' W q a c + S / 4 * (c - ts) ≤ 0 := by linarith
      nlinarith [hc.1]
  simp only [h, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at key
  linarith

end quad

/-- `|F_N(e(θ))| ≤ 2 |G(θ)|`: the vanishing factor, if any, is `≤ 2` (and there is at most one). -/
theorem FW_le_Gw {q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (N : ℕ) (θ : ℝ) :
    ‖FW (WN N) θ‖ ≤ 2 * ‖Gw (WN N) q a θ‖ := by
  unfold FW Gw
  have hv : ‖∏ w ∈ (WN N).filter (vanish q a), (1 + ee (w * θ))‖ ≤ 2 := by
    rw [norm_prod]
    have hc := card_vanish_WN hq ha N
    calc ∏ w ∈ (WN N).filter (vanish q a), ‖1 + ee (w * θ)‖ ≤ ∏ _w ∈ (WN N).filter (vanish q a), (2 : ℝ) :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun w _ => by
            rw [norm_one_add_ee]; nlinarith [Real.abs_cos_le_one (π * (w * θ)), abs_nonneg (Real.cos (π * (w * θ)))]
      _ = 2 ^ ((WN N).filter (vanish q a)).card := by rw [prod_const]
      _ ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hc
      _ = 2 := by norm_num
  rw [← prod_filter_mul_prod_filter_not (WN N) (vanish q a) (f := fun w => 1 + ee (w * θ)), norm_mul]
  nlinarith [norm_nonneg (∏ w ∈ (WN N).filter (fun w => ¬ vanish q a w), (1 + ee (w * θ))),
    norm_nonneg (∏ w ∈ (WN N).filter (vanish q a), (1 + ee (w * θ)))]

theorem Gw_pos {q a N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) {t : ℝ} (ht : |t| < π / (q * N)) :
    0 < ‖Gw (WN N) q a ((a : ℝ) / q + t / (2 * π))‖ := by
  unfold Gw
  rw [norm_prod]
  refine prod_pos fun w hw => ?_
  rw [norm_one_add_ee, arg_eq]
  have := cos_ne_zero_win (W := WN N) hq hN (fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)) hw ht
  positivity

theorem norm_Gw_eq {q a N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) {t : ℝ} (ht : |t| < π / (q * N)) :
    ‖Gw (WN N) q a ((a : ℝ) / q + t / (2 * π))‖ = Real.exp (Fw (WN N) q a t) := by
  have hWN : ∀ w ∈ WN N, w ≤ N := fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)
  rw [← log_Gw (W := WN N) (a := a) hq hN hWN ht, Real.exp_log (Gw_pos hq hN ht)]

/-- **The shoulder, pointwise**: in the window `|t| < π/(qN)`, at distance `≥ τ` from the peak,
`|F_N(e(a/q + t/(2π)))| ≤ 2|G(θ*)| e^{−S₂τ²/8}`. -/
theorem shoulder_pt {q a N : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hN : 1 ≤ N) {ts t τ : ℝ}
    (hts : |ts| < π / (q * N)) (hzero : Fw' (WN N) q a ts = 0) (ht : |t| < π / (q * N)) (hτ : 0 ≤ τ)
    (hd : τ ≤ |t - ts|) :
    ‖FW (WN N) ((a : ℝ) / q + t / (2 * π))‖ ≤
      2 * ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ * Real.exp (-(S2W (WN N) q a * τ ^ 2 / 8)) := by
  have hq1 : 1 ≤ q := by omega
  have hWN : ∀ w ∈ WN N, w ≤ N := fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)
  refine (FW_le_Gw hq ha N _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [norm_Gw_eq hq1 hN ht, norm_Gw_eq hq1 hN hts, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq' := Fw_quad (W := WN N) (a := a) hq1 hN hWN hts hzero ht
  have hS : 0 ≤ S2W (WN N) q a := by unfold S2W; positivity
  have : τ ^ 2 ≤ (t - ts) ^ 2 := by rw [← sq_abs (t - ts)]; exact pow_le_pow_left₀ hτ hd 2
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **Theorem E(2), the shoulder** (paper §3.5): fix `B > 0`, `0 < ε < 1/8`, `τ₀ = N^{−3/2+ε}`. For
`N ≥ N₀`, `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, the peak `t*` of Lemma W, and every `T`, the two ranges
`τ₀ < |t − t*|`, `|t| < π/(qN)` (`t = 2π(θ − a/q)`) are inside the window and each contributes
`≤ 2|G(θ*)| e^{−N^{2ε}/(512 log N)}`. The vanishing factor, if any, is bounded by `2`. The only hypothesis
is Siegel–Walfisz. -/
theorem thmE2_shoulder (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        let θs := (a : ℝ) / q + ts / (2 * π)
        let τ₀ := (N : ℝ) ^ (-(3 / 2 : ℝ) + ε)
        let δθ := 1 / (2 * q * (N : ℝ))
        θs + τ₀ / (2 * π) ≤ (a : ℝ) / q + δθ ∧ (a : ℝ) / q - δθ ≤ θs - τ₀ / (2 * π) ∧
        ‖∫ θ in (θs + τ₀ / (2 * π))..((a : ℝ) / q + δθ), FW (WN N) θ * ee (-(T * θ))‖ ≤
          2 * ‖Gw (WN N) q a θs‖ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N)) ∧
        ‖∫ θ in ((a : ℝ) / q - δθ)..(θs - τ₀ / (2 * π)), FW (WN N) θ * ee (-(T * θ))‖ ≤
          2 * ‖Gw (WN N) q a θs‖ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N)) := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  have hε1 : (0 : ℝ) < 1 / 2 - ε := by linarith
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp B hc 1
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp B hε1 16
  set Kmax := max K₁ K₂
  refine ⟨N₁ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha ts hts hF T => ?_⟩
  obtain ⟨-, hS2pos, hwin, hrat, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  intro θs τ₀ δθ
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_max_left _ _) hKL
  have hL2 : K₂ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hrp : ∀ x : ℝ, Nr ^ x = Real.exp (x * L) := fun x => by rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hpi := Real.pi_pos
  have h2pi := Real.two_le_pi
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
    rw [le_div_iff₀ hq0]
    nlinarith [Real.exp_pos (-c * √L)]
  have htsq : |ts| ≤ 1 / (q * Nr) := by
    rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hq0] at hts'; linarith
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
  have hwq : 2 / (q * Nr) ≤ π / (q * Nr) := div_le_div_of_nonneg_right h2pi (by positivity)
  have htsw : |ts| < π / (q * Nr) := lt_of_le_of_lt htsq (lt_of_lt_of_le
    (by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num) hwq)
  -- `S₂τ₀²/8 ≥ N^{2ε}/(512 L)`
  have hSτ : Nr ^ (2 * ε) / (512 * L) ≤ S2W (WN N) q a * τ₀ ^ 2 / 8 := by
    have h1 := hS2lo
    have e : Nr ^ 3 / (64 * L) * τ₀ ^ 2 / 8 = Nr ^ (2 * ε) / (512 * L) := by
      rw [hτe, hrp, ← Real.exp_nat_mul, show Nr ^ 3 = Real.exp (3 * L) by
        rw [← hexpL, ← Real.exp_nat_mul]; norm_num]
      rw [div_mul_eq_mul_div, ← Real.exp_add, div_div]
      congr 1
      · congr 1; push_cast; ring
      · ring
    rw [← e]
    gcongr
  have hdecay : 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) ≤
      2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(Nr ^ (2 * ε)) / (512 * L)) := by
    gcongr
    rw [neg_div]; linarith
  -- the pointwise bound on both ranges
  have hpt : ∀ θ : ℝ, |θ - a / q| < δθ → τ₀ ≤ |2 * π * (θ - a / q) - ts| →
      ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) := by
    intro θ hθ hd
    rw [norm_mul, norm_ee, mul_one]
    have hθe : θ = a / q + (2 * π * (θ - a / q)) / (2 * π) := by field_simp; ring
    have hw : |2 * π * (θ - a / q)| < π / (q * Nr) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have : 2 * π * δθ = π / (q * Nr) := by simp only [δθ]; field_simp
      rw [← this]; exact mul_lt_mul_of_pos_left hθ (by positivity)
    rw [hθe]
    exact shoulder_pt hq ha (by omega) htsw hF hw hτ0.le hd
  have hlen : ∀ x y : ℝ, |y - x| ≤ 2 * δθ → 2 * δθ ≤ 1 → |y - x| ≤ 1 := fun x y h1 h2 => h1.trans h2
  have hδ1 : 2 * δθ ≤ 1 := by
    simp only [δθ]; rw [show 2 * (1 / (2 * q * Nr)) = 1 / (q * Nr) by field_simp, div_le_one (by positivity)]
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hδ0 : 0 < δθ := by simp only [δθ]; positivity
  have hθs : θs - a / q = ts / (2 * π) := by simp only [θs]; ring
  have hk : (ts + τ₀) / (2 * π) ≤ δθ ∧ (-ts + τ₀) / (2 * π) ≤ δθ := by
    have e : δθ = (π / (q * Nr)) / (2 * π) := by simp only [δθ]; field_simp
    rw [e]
    have e2 : 2 / (q * Nr) = 1 / (q * Nr) + 1 / (q * Nr) := by ring
    have h1 : ts + τ₀ ≤ π / (q * Nr) := by linarith [le_abs_self ts, hτq, hwq, htsq]
    have h2 : -ts + τ₀ ≤ π / (q * Nr) := by linarith [neg_abs_le ts, hτq, hwq, htsq]
    exact ⟨div_le_div_of_nonneg_right h1 (by positivity), div_le_div_of_nonneg_right h2 (by positivity)⟩
  have hk1 : ts / (2 * π) + τ₀ / (2 * π) ≤ δθ := by have := hk.1; rwa [add_div] at this
  have hk2 : -(ts / (2 * π)) + τ₀ / (2 * π) ≤ δθ := by have := hk.2; rwa [add_div, neg_div] at this
  have hτ2 : 0 < τ₀ / (2 * π) := by positivity
  have he : ∀ θ : ℝ, 2 * π * (θ - a / q) - ts = 2 * π * (θ - θs) := by
    intro θ; rw [show θ - θs = θ - a / q - (θs - a / q) by ring, hθs]; field_simp; try ring
  have hR1 : θs + τ₀ / (2 * π) ≤ a / q + δθ := by
    have := hk.1; rw [add_div] at this; linarith
  have hL1' : a / q - δθ ≤ θs - τ₀ / (2 * π) := by
    have := hk.2; rw [add_div, neg_div] at this; linarith
  have hC0 : 0 ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) := by positivity
  refine ⟨hR1, hL1', ?_, ?_⟩
  · -- the right range
    have hb : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (θs + τ₀ / (2 * π)) (a / q + δθ) →
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) := by
      filter_upwards [Measure.ae_ne volume ((a : ℝ) / q + δθ)] with θ hne hθ
      rw [Set.uIoc_of_le hR1] at hθ
      have hlt : θ < a / q + δθ := lt_of_le_of_ne hθ.2 hne
      refine hpt θ (abs_lt.mpr ⟨by linarith [hθ.1], by linarith⟩) ?_
      have : τ₀ < 2 * π * (θ - a / q) - ts := by
        have h1 : τ₀ / (2 * π) < θ - θs := by linarith [hθ.1]
        rw [div_lt_iff₀ (by positivity)] at h1
        rw [he]; linarith
      rw [abs_of_pos (by linarith)]; linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae hb).trans ?_
    refine le_trans ?_ hdecay
    have : |a / q + δθ - (θs + τ₀ / (2 * π))| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      have : a / q + δθ - (θs + τ₀ / (2 * π)) ≤ 2 * δθ := by
        rw [show a / q + δθ - (θs + τ₀ / (2 * π)) = δθ - (θs - a / q) - τ₀ / (2 * π) by ring, hθs]
        have : -δθ ≤ ts / (2 * π) := by
          have := hk.2; rw [add_div, neg_div] at this
          have : 0 ≤ τ₀ / (2 * π) := by positivity
          linarith
        have : 0 ≤ τ₀ / (2 * π) := by positivity
        linarith
      linarith
    calc 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) *
          |a / q + δθ - (θs + τ₀ / (2 * π))| ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) * 1 :=
          mul_le_mul_of_nonneg_left this hC0
      _ = _ := mul_one _
  · -- the left range
    have hb : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (a / q - δθ) (θs - τ₀ / (2 * π)) →
        ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) := by
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      rw [Set.uIoc_of_le hL1'] at hθ
      refine hpt θ (abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) ?_
      have : 2 * π * (θ - a / q) - ts ≤ -τ₀ := by
        have : θ - θs ≤ -(τ₀ / (2 * π)) := by linarith [hθ.2]
        rw [he θ]
        have : 2 * π * (θ - θs) ≤ 2 * π * (-(τ₀ / (2 * π))) := mul_le_mul_of_nonneg_left this (by positivity)
        have e2 : 2 * π * (-(τ₀ / (2 * π))) = -τ₀ := by field_simp
        linarith
      rw [abs_of_neg (by linarith)]; linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const_ae hb).trans ?_
    refine le_trans ?_ hdecay
    have : |θs - τ₀ / (2 * π) - (a / q - δθ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      have : θs - τ₀ / (2 * π) - (a / q - δθ) ≤ 2 * δθ := by
        rw [show θs - τ₀ / (2 * π) - (a / q - δθ) = (θs - a / q) - τ₀ / (2 * π) + δθ by ring, hθs]
        have : ts / (2 * π) ≤ δθ := by
          have := hk.1; rw [add_div] at this
          have : 0 ≤ τ₀ / (2 * π) := by positivity
          linarith
        have : 0 ≤ τ₀ / (2 * π) := by positivity
        linarith
      linarith
    calc 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) *
          |θs - τ₀ / (2 * π) - (a / q - δθ)| ≤ 2 * ‖Gw (WN N) q a θs‖ * Real.exp (-(S2W (WN N) q a * τ₀ ^ 2 / 8)) * 1 :=
          mul_le_mul_of_nonneg_left this hC0
      _ = _ := mul_one _

end ArcsAlgo.Core
