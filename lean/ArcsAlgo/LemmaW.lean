module

public import ArcsAlgo.ArcCore
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option autoImplicit false

/-!
# Lemma W: the peak of an arc (paper §3.5), deterministic part

For weights `W` (all `≤ N`), `q ≥ 1` and the factors not vanishing at `a/q`:
`F(t) = Σ_{w∉𝒱} log|2cos(πwa/q + wt/2)| = log|G(a/q + t/(2π))|` (`Fw`, `log_Gw`, `log_Fstar`),
`F′(t) = −Σ (w/2) tan(πwa/q + wt/2)` (`Fw'`), `ν = ½Σ w tan(πwa/q)` (`nuW`), `S₂ = Σ w²` (`S2W`).

* `dist_zero_cos`, `cos_ne_zero_win`: in the window `|t| < π/(qN)` no factor of `G` vanishes.
* **W(1)** `hasDerivAt_Fw`, `Fw'_strong`: `F′ = −Σ(w/2)tan` and `F′(t) − F′(s) ≤ −(S₂/4)(t − s)`.
* **W(2)** `Fw'_zero` (`F′(0) = −ν`) and `peak`: if `S₂ > 0` and `4|ν|/S₂ < π/(qN)`, `F` has a unique
  maximum in the window at `t*`, `|t*| ≤ 4|ν|/S₂`, `F′(t*) = 0`, and `F(0) ≤ F(t*) ≤ F(0) + 4ν²/S₂`,
  i.e. `log|F*(a/q)| ≤ log|G(θ*)| ≤ log|F*(a/q)| + 4ν²/S₂`.
* **W(3)** `p_types`, `kappa2_ge`, `im_kappa1`: with `p = u/(1+u)`, `u = e(wθ)`: `p(1−p) =
  1/(4cos²(πwθ))`, `1 − 2p = −i tan(πwθ)`; `κ₂ ≥ S₂/4`, and `Im κ₁ = −F′(t)` vanishes at the peak.

No hypothesis. The bound `ν ≪ N²e^{−c√log N}` (Siegel–Walfisz) is in `LemmaWSW`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

/-- `α_w = πwa/q`. -/
noncomputable def alw (q a w : ℕ) : ℝ := π * w * a / q

/-- The zeros of `cos` are at distance `≥ π/(2q)` from `α_w` when the factor of `w` does not vanish. -/
theorem dist_zero_cos {q a w : ℕ} (hq : 1 ≤ q) (hv : ¬ vanish q a w) (k : ℤ) :
    π / (2 * q) ≤ |alw q a w - (2 * k + 1) * π / 2| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set n : ℤ := 2 * w * a - q * (2 * k + 1)
  have hn : n ≠ 0 := by
    intro h; apply hv; unfold vanish
    exact ⟨k, by simp only [n] at h; push_cast; linarith⟩
  have e : alw q a w - (2 * k + 1) * π / 2 = π * n / (2 * q) := by
    simp only [n, alw]; push_cast; field_simp
  rw [e, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * q)]
  have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  gcongr
  nlinarith [Real.pi_pos]

theorem cos_ne_zero_near {q a w : ℕ} (hq : 1 ≤ q) (hv : ¬ vanish q a w) {s : ℝ} (hs : |s| < π / (2 * q)) :
    cos (alw q a w + s) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have := dist_zero_cos hq hv k
  rw [show alw q a w - (2 * k + 1) * π / 2 = -s by linarith, abs_neg] at this
  linarith

/-! ### `F(t) = log|G(a/q + t/(2π))|` -/

/-- `F(t) = Σ_{w ∉ 𝒱} log|2 cos(πwa/q + wt/2)|`. -/
noncomputable def Fw (W : Finset ℕ) (q a : ℕ) (t : ℝ) : ℝ :=
  ∑ w ∈ W.filter (fun w => ¬ vanish q a w), Real.log (2 * cos (alw q a w + w * t / 2))

/-- `F′(t) = −Σ_{w ∉ 𝒱} (w/2) tan(πwa/q + wt/2)`. -/
noncomputable def Fw' (W : Finset ℕ) (q a : ℕ) (t : ℝ) : ℝ :=
  -∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w / 2 : ℝ) * tan (alw q a w + w * t / 2)

/-- `ν_{a/q} = ½ Σ_{w ∉ 𝒱} w tan(πwa/q)`. -/
noncomputable def nuW (W : Finset ℕ) (q a : ℕ) : ℝ :=
  (1 / 2) * ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) * tan (alw q a w)

/-- `S₂ = Σ_{w ∉ 𝒱} w²`. -/
noncomputable def S2W (W : Finset ℕ) (q a : ℕ) : ℝ := ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) ^ 2

theorem Fw'_zero (W : Finset ℕ) (q a : ℕ) : Fw' W q a 0 = -nuW W q a := by
  unfold Fw' nuW
  rw [mul_sum]; congr 1
  exact sum_congr rfl fun w _ => by simp; ring

/-- The window: every `w` with `w ≤ N`, `|t| < π/(qN)` gives `|wt/2| < π/(2q)`. -/
theorem half_lt {q N w : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) (hw : w ≤ N) {t : ℝ} (ht : |t| < π / (q * N)) :
    |(w : ℝ) * t / 2| < π / (2 * q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw' : (w : ℝ) ≤ N := by exact_mod_cast hw
  rw [abs_div, abs_mul, Nat.abs_cast, abs_two]
  calc (w : ℝ) * |t| / 2 ≤ N * |t| / 2 := by gcongr
    _ < N * (π / (q * N)) / 2 := by
        have := mul_lt_mul_of_pos_left ht hN'; linarith
    _ = π / (2 * q) := by field_simp

variable {W : Finset ℕ} {q a N : ℕ}

theorem cos_ne_zero_win (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {w : ℕ}
    (hw : w ∈ W.filter (fun w => ¬ vanish q a w)) {t : ℝ} (ht : |t| < π / (q * N)) :
    cos (alw q a w + w * t / 2) ≠ 0 :=
  cos_ne_zero_near hq (mem_filter.mp hw).2 (half_lt hq hN (hWN w (mem_filter.mp hw).1) ht)

theorem hasDerivAt_term (w : ℕ) (α t : ℝ) (hc : cos (α + w * t / 2) ≠ 0) :
    HasDerivAt (fun t => Real.log (2 * cos (α + w * t / 2))) (-((w / 2 : ℝ) * tan (α + w * t / 2))) t := by
  have h1 : HasDerivAt (fun t : ℝ => α + w * t / 2) (w / 2) t := by
    have := ((hasDerivAt_id t).const_mul ((w : ℝ) / 2)).const_add α
    convert this using 1
    · ext t; simp; ring
    · simp
  have h2 := (h1.cos.const_mul 2).log (mul_ne_zero two_ne_zero hc)
  convert h2 using 1
  rw [Real.tan_eq_sin_div_cos]; field_simp

/-- `F′` is the derivative of `F` in the window. -/
theorem hasDerivAt_Fw (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {t : ℝ}
    (ht : |t| < π / (q * N)) : HasDerivAt (Fw W q a) (Fw' W q a t) t := by
  unfold Fw Fw'
  rw [← sum_neg_distrib]
  have := HasDerivAt.fun_sum (u := W.filter (fun w => ¬ vanish q a w))
    (A := fun w t => Real.log (2 * cos (alw q a w + w * t / 2)))
    (A' := fun w => -((w / 2 : ℝ) * tan (alw q a w + w * t / 2))) (x := t)
    fun w hw => hasDerivAt_term w (alw q a w) t (cos_ne_zero_win hq hN hWN hw ht)
  convert this using 1

/-- `tan y − tan x ≥ y − x` when `cos` has no zero on `[x, y]`. -/
theorem tan_sub_ge {x y : ℝ} (hxy : x ≤ y) (hc : ∀ z ∈ Set.Icc x y, cos z ≠ 0) : y - x ≤ tan y - tan x := by
  rcases hxy.eq_or_lt with rfl | hlt
  · simp
  have hcont : ContinuousOn tan (Set.Icc x y) := fun z hz =>
    (Real.hasDerivAt_tan (hc z hz)).continuousAt.continuousWithinAt
  obtain ⟨c, hcm, hcd⟩ := exists_hasDerivAt_eq_slope tan (fun z => 1 / cos z ^ 2) hlt hcont
    fun z hz => Real.hasDerivAt_tan (hc z ⟨hz.1.le, hz.2.le⟩)
  have hcc : cos c ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one c]
  have hpos : 0 < cos c ^ 2 := by
    have := hc c ⟨hcm.1.le, hcm.2.le⟩; positivity
  have h1 : 1 ≤ 1 / cos c ^ 2 := by rw [le_div_iff₀ hpos]; linarith
  rw [hcd, le_div_iff₀ (by linarith)] at h1
  linarith

/-- **Lemma W(1)**: in the window `|t| < π/(qN)`, `F′(t) − F′(s) ≤ −(S₂/4)(t − s)` for `s < t`
(`F″ ≤ −S₂/4`). -/
theorem Fw'_strong (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {s t : ℝ}
    (hs : |s| < π / (q * N)) (ht : |t| < π / (q * N)) (hst : s ≤ t) :
    Fw' W q a t - Fw' W q a s ≤ -(S2W W q a / 4) * (t - s) := by
  unfold Fw' S2W
  rw [neg_sub_neg, ← sum_sub_distrib, sum_div, neg_mul, sum_mul, ← sum_neg_distrib]
  refine sum_le_sum fun w hw => ?_
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  -- `tan` over `[α + ws/2, α + wt/2]`
  have hseg : ∀ z ∈ Set.Icc (alw q a w + w * s / 2) (alw q a w + w * t / 2), cos z ≠ 0 := by
    intro z hz
    have hzt : |z - alw q a w| < π / (2 * q) := by
      have h1 := half_lt hq hN (hWN w (mem_filter.mp hw).1) hs
      have h2 := half_lt hq hN (hWN w (mem_filter.mp hw).1) ht
      rw [abs_lt] at h1 h2 ⊢; constructor <;> linarith [hz.1, hz.2]
    have := cos_ne_zero_near hq (mem_filter.mp hw).2 hzt
    rwa [add_sub_cancel] at this
  have hle : alw q a w + w * s / 2 ≤ alw q a w + w * t / 2 := by nlinarith
  have := tan_sub_ge hle hseg
  have e : alw q a w + w * t / 2 - (alw q a w + w * s / 2) = (w / 2) * (t - s) := by ring
  rw [e] at this
  have : (w / 2 : ℝ) * ((w / 2) * (t - s)) ≤
      (w / 2 : ℝ) * (tan (alw q a w + w * t / 2) - tan (alw q a w + w * s / 2)) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

theorem Fw'_cont (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) :
    ContinuousOn (Fw' W q a) (Set.Ioo (-(π / (q * N))) (π / (q * N))) := by
  unfold Fw'
  refine (continuousOn_finsetSum _ fun w hw => ?_).neg
  refine continuousOn_const.mul ?_
  intro t ht
  have ht' : |t| < π / (q * N) := abs_lt.mpr ht
  have hg : ContinuousAt (fun s : ℝ => alw q a w + (w : ℝ) * s / 2) t := by fun_prop
  exact (ContinuousAt.comp (g := tan) (f := fun s : ℝ => alw q a w + (w : ℝ) * s / 2)
    (Real.hasDerivAt_tan (cos_ne_zero_win hq hN hWN hw ht')).continuousAt hg).continuousWithinAt

/-- **Lemma W(2), the peak**: if `S₂ > 0` and `4|ν|/S₂ < π/(qN)`, then `F` has a unique maximum in the
window, at a point `t*` with `|t*| ≤ 4|ν|/S₂`, `F′(t*) = 0`, and `F(0) ≤ F(t*) ≤ F(0) + 4ν²/S₂`. -/
theorem peak (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) (hS : 0 < S2W W q a)
    (hsmall : 4 * |nuW W q a| / S2W W q a < π / (q * N)) :
    ∃ ts : ℝ, |ts| ≤ 4 * |nuW W q a| / S2W W q a ∧ Fw' W q a ts = 0 ∧
      (∀ t, |t| < π / (q * N) → t ≠ ts → Fw W q a t < Fw W q a ts) ∧
      Fw W q a 0 ≤ Fw W q a ts ∧ Fw W q a ts ≤ Fw W q a 0 + 4 * nuW W q a ^ 2 / S2W W q a := by
  set δ := π / (q * N)
  set ν := nuW W q a
  set S := S2W W q a
  set τ := 4 * |ν| / S
  have hτ0 : 0 ≤ τ := by positivity
  have hτ : τ < δ := hsmall
  have hwin : ∀ t, |t| ≤ τ → |t| < δ := fun t h => lt_of_le_of_lt h hτ
  have hstr := fun s t (hs : |s| < δ) (ht : |t| < δ) (hst : s ≤ t) => Fw'_strong (a := a) hq hN hWN hs ht hst
  have h0 := Fw'_zero W q a
  have hδ0 : 0 < δ := lt_of_le_of_lt hτ0 hτ
  -- `F′(−τ) ≥ 0 ≥ F′(τ)`
  have hτS : S / 4 * τ = |ν| := by simp only [τ]; field_simp
  have hlo : 0 ≤ Fw' W q a (-τ) := by
    have := hstr (-τ) 0 (by rw [abs_neg, abs_of_nonneg hτ0]; exact hτ) (by simpa using hδ0) (by linarith)
    rw [h0] at this; nlinarith [le_abs_self ν]
  have hhi : Fw' W q a τ ≤ 0 := by
    have := hstr 0 τ (by simpa using hδ0) (by rw [abs_of_nonneg hτ0]; exact hτ) hτ0
    rw [h0] at this; nlinarith [neg_abs_le ν]
  have hcont : ContinuousOn (Fw' W q a) (Set.Icc (-τ) τ) :=
    (Fw'_cont hq hN hWN).mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨ts, hts, hzero⟩ := intermediate_value_Icc' (by linarith) hcont ⟨hhi, hlo⟩
  have htsabs : |ts| ≤ τ := abs_le.mpr ⟨hts.1, hts.2⟩
  have htsw : |ts| < δ := hwin ts htsabs
  have hder : ∀ t, |t| < δ → HasDerivAt (Fw W q a) (Fw' W q a t) t := fun t ht => hasDerivAt_Fw hq hN hWN ht
  -- `F` on a segment inside the window
  have hseg : ∀ x y, |x| < δ → |y| < δ → x < y → ∃ c ∈ Set.Ioo x y,
      Fw W q a y - Fw W q a x = Fw' W q a c * (y - x) := by
    intro x y hx hy hxy
    have hin : ∀ z ∈ Set.Icc x y, |z| < δ := fun z hz => by
      rw [abs_lt] at hx hy ⊢; constructor <;> linarith [hz.1, hz.2]
    have hc : ContinuousOn (Fw W q a) (Set.Icc x y) := fun z hz =>
      (hder z (hin z hz)).continuousAt.continuousWithinAt
    obtain ⟨c, hcm, hcd⟩ := exists_hasDerivAt_eq_slope (Fw W q a) (Fw' W q a) hxy hc
      fun z hz => hder z (hin z ⟨hz.1.le, hz.2.le⟩)
    refine ⟨c, hcm, ?_⟩
    rw [hcd]; field_simp
  have hin2 : ∀ x y z, |x| < δ → |y| < δ → z ∈ Set.Ioo x y → |z| < δ := fun x y z hx hy hz => by
    rw [abs_lt] at hx hy ⊢; constructor <;> linarith [hz.1, hz.2]
  have hmax : ∀ t, |t| < δ → t ≠ ts → Fw W q a t < Fw W q a ts := by
    intro t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨c, hc, hcd⟩ := hseg t ts ht htsw hlt
      have := hstr c ts (hin2 t ts c ht htsw hc) htsw hc.2.le
      rw [hzero] at this
      have hpos : 0 < Fw' W q a c := by nlinarith [hc.2]
      nlinarith [hc.2]
    · obtain ⟨c, hc, hcd⟩ := hseg ts t htsw ht hgt
      have := hstr ts c htsw (hin2 ts t c htsw ht hc) hc.1.le
      rw [hzero] at this
      have hneg : Fw' W q a c < 0 := by nlinarith [hc.1]
      nlinarith [hc.1]
  have hz0 : |(0 : ℝ)| < δ := by simpa using hδ0
  have hgain : Fw W q a ts - Fw W q a 0 ≤ |ν| * |ts| := by
    rcases lt_trichotomy ts 0 with hlt | heq | hgt
    · obtain ⟨c, hc, hcd⟩ := hseg ts 0 htsw hz0 hlt
      have := hstr c 0 (hin2 ts 0 c htsw hz0 hc) hz0 hc.2.le
      rw [h0] at this
      have hc' : -ν ≤ Fw' W q a c := by nlinarith [hc.2]
      rw [abs_of_neg hlt]
      nlinarith [le_abs_self ν, neg_abs_le ν]
    · rw [heq]; simp
    · obtain ⟨c, hc, hcd⟩ := hseg 0 ts hz0 htsw hgt
      have := hstr 0 c hz0 (hin2 0 ts c hz0 htsw hc) hc.1.le
      rw [h0] at this
      have hc' : Fw' W q a c ≤ -ν := by nlinarith [hc.1]
      rw [abs_of_pos hgt]
      nlinarith [le_abs_self ν, neg_abs_le ν]
  refine ⟨ts, htsabs, hzero, hmax, ?_, ?_⟩
  · by_cases h : (0 : ℝ) = ts
    · rw [h]
    · exact (hmax 0 hz0 h).le
  · have : |ν| * |ts| ≤ 4 * ν ^ 2 / S := by
      calc |ν| * |ts| ≤ |ν| * τ := mul_le_mul_of_nonneg_left htsabs (abs_nonneg _)
        _ = 4 * ν ^ 2 / S := by simp only [τ]; rw [← sq_abs ν]; ring
    linarith

/-! ### `G` and the cumulants at the peak -/

/-- `G(θ) = Π_{w ∉ 𝒱} (1 + e(wθ))`, so that `G(a/q) = F*(a/q)`. -/
noncomputable def Gw (W : Finset ℕ) (q a : ℕ) (θ : ℝ) : ℂ :=
  ∏ w ∈ W.filter (fun w => ¬ vanish q a w), (1 + ee (w * θ))

theorem Gw_arc (W : Finset ℕ) (q a : ℕ) : Gw W q a ((a : ℝ) / q) = Fstar W q a := rfl

theorem arg_eq (q a w : ℕ) (t : ℝ) : π * (w * ((a : ℝ) / q + t / (2 * π))) = alw q a w + w * t / 2 := by
  unfold alw; field_simp [Real.pi_ne_zero]

/-- `log|G(a/q + t/(2π))| = F(t)` in the window. -/
theorem log_Gw (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {t : ℝ} (ht : |t| < π / (q * N)) :
    Real.log ‖Gw W q a ((a : ℝ) / q + t / (2 * π))‖ = Fw W q a t := by
  unfold Gw Fw
  rw [norm_prod, Real.log_prod]
  · refine sum_congr rfl fun w hw => ?_
    rw [norm_one_add_ee, arg_eq, show 2 * |cos (alw q a w + w * t / 2)| = |2 * cos (alw q a w + w * t / 2)| by
      rw [abs_mul, abs_two], Real.log_abs]
  · intro w hw
    rw [norm_one_add_ee, arg_eq]
    have := cos_ne_zero_win hq hN hWN hw ht
    positivity

theorem log_Fstar (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) :
    Real.log ‖Fstar W q a‖ = Fw W q a 0 := by
  have hπ : 0 < π / (q * N) := by
    have : (0 : ℝ) < q * N := by positivity
    positivity
  have := log_Gw (a := a) hq hN hWN (t := 0) (by simpa using hπ)
  rwa [zero_div, add_zero, Gw_arc] at this

/-- For `cos y ≠ 0`, `u = e^{2iy}` gives `p = u/(1 + u) = 1/2 + (i/2) tan y`. -/
theorem p_eq {y : ℝ} (hc : cos y ≠ 0) :
    Complex.exp (2 * y * Complex.I) / (1 + Complex.exp (2 * y * Complex.I)) = 1 / 2 + Complex.I / 2 * tan y := by
  have hc' : (Complex.cos y) ≠ 0 := by rw [← Complex.ofReal_cos]; exact_mod_cast hc
  have h1 : 1 + Complex.exp (2 * y * Complex.I) = Complex.exp (y * Complex.I) * (2 * Complex.cos y) := by
    rw [Complex.cos, show (2 : ℂ) * ((Complex.exp (↑y * Complex.I) + Complex.exp (-↑y * Complex.I)) / 2) =
      Complex.exp (↑y * Complex.I) + Complex.exp (-↑y * Complex.I) by ring, mul_add, ← Complex.exp_add,
      ← Complex.exp_add]
    ring_nf; rw [Complex.exp_zero]; try ring
  have h2 : Complex.exp (2 * y * Complex.I) = Complex.exp (y * Complex.I) * Complex.exp (y * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have hE : Complex.exp (y * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [h1, h2, Complex.exp_mul_I, Complex.ofReal_tan, Complex.tan]
  field_simp

/-- **Lemma W(3), the types**: with `p = u/(1 + u)`, `u = e(wθ)`, `cos(πwθ) ≠ 0`:
`p(1 − p) = 1/(4cos²(πwθ))` is real and positive, and `1 − 2p = −i tan(πwθ)` is purely imaginary;
so `κ₂ = Σ w²p(1−p) = Σ w²/(4cos²) ≥ S₂/4` is real, `κ₃ = Σ w³p(1−p)(1−2p)` is purely imaginary,
`κ₄ = Σ w⁴p(1−p)(1 − 6p(1−p))` is real, and `Im κ₁ = ½Σ w tan(πwθ)` vanishes at the peak. -/
theorem p_types {y : ℝ} (hc : cos y ≠ 0) :
    let p := Complex.exp (2 * y * Complex.I) / (1 + Complex.exp (2 * y * Complex.I))
    p * (1 - p) = ((1 / (4 * cos y ^ 2) : ℝ) : ℂ) ∧ 1 - 2 * p = -Complex.I * tan y ∧
      p = 1 / 2 + Complex.I / 2 * tan y := by
  intro p
  have hp : p = 1 / 2 + Complex.I / 2 * tan y := p_eq hc
  have ht : (1 : ℝ) + tan y ^ 2 = 1 / cos y ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]; field_simp; rw [Real.cos_sq_add_sin_sq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    have : ((1 / (4 * cos y ^ 2) : ℝ) : ℂ) = ((1 + tan y ^ 2) / 4 : ℝ) := by
      congr 1; rw [ht]; field_simp
    rw [this]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  · rw [hp]; ring
  · exact hp

/-- `κ₂ = Σ_{w∉𝒱} w²/(4 cos²(πwθ)) ≥ S₂/4` in the window. -/
theorem kappa2_ge (hq : 1 ≤ q) (hN : 1 ≤ N) (hWN : ∀ w ∈ W, w ≤ N) {t : ℝ} (ht : |t| < π / (q * N)) :
    S2W W q a / 4 ≤ ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) ^ 2 / (4 * cos (alw q a w + w * t / 2) ^ 2) := by
  unfold S2W
  rw [sum_div]
  refine sum_le_sum fun w hw => ?_
  have hc := cos_ne_zero_win hq hN hWN hw ht
  have h1 : cos (alw q a w + w * t / 2) ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one (alw q a w + w * t / 2)]
  have h0 : 0 < cos (alw q a w + w * t / 2) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [sq_nonneg (w : ℝ)]

/-- `Im κ₁ = −F′(t)`: at the peak `κ₁` is real. -/
theorem im_kappa1 (t : ℝ) :
    ∑ w ∈ W.filter (fun w => ¬ vanish q a w), (w : ℝ) * (tan (alw q a w + w * t / 2) / 2) = -Fw' W q a t := by
  unfold Fw'; rw [neg_neg]; exact sum_congr rfl fun w _ => by ring

end ArcsAlgo.Core
