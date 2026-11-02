module

public import ArcsAlgo.LemmaWSW
set_option autoImplicit false

/-!
# The prime counting function from Siegel–Walfisz

* `liK_diff_le`: `li(y) − li(x) ≤ (y − x)/log x` for `2 ≤ x ≤ y`.
* `pi_SW`: Siegel–Walfisz at `q = 1`, `|π(m) − li(m)| ≤ C m e^{−c√log m}`.
* `pi_lower`: `π(N) ≥ N/(2 log N)` for `N` large.
* `pi_upper`: for every `δ > 0`, `π(N) ≤ (1 + δ) N/log N` for `N` large.

The only hypothesis is `SiegelWalfisz` (cited, ineffective constants).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

theorem liK_diff_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : liK 0 y - liK 0 x ≤ (y - x) / Real.log x := by
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have e : liK 0 y - liK 0 x = ∫ t in x..y, liIntegrand 0 t := by
    unfold liK
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_liIntegrand 0 0 x)
      (intervalIntegrable_liIntegrand 0 x y)]; ring
  rw [e]
  have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume) hxy
    (intervalIntegrable_liIntegrand 0 x y) (intervalIntegrable_const (c := 1 / Real.log x)) fun t ht => by
      have ht2 : 2 < t := by linarith [ht.1]
      unfold liIntegrand; rw [if_pos ht2, pow_zero]
      exact one_div_le_one_div_of_le hlx (Real.log_le_log (by linarith) ht.1.le)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  rw [div_eq_mul_one_div]; exact this

theorem three_le_log {m : ℕ} (hm : 3 ≤ m) : (1 : ℝ) ≤ Real.log m := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- Siegel–Walfisz at `q = 1`: `|π(m) − li(m)| ≤ C m e^{−c√log m}`. -/
theorem pi_SW (hSW : SiegelWalfisz) : ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 3 ≤ m →
    |(Nat.primeCounting m : ℝ) - liK 0 m| ≤ C * m * Real.exp (-c * √(Real.log m)) := by
  obtain ⟨c, hc, C, hC, h⟩ := hSW 1 one_pos
  refine ⟨c, hc, C, hC, fun m hm => ?_⟩
  have hl := three_le_log hm
  have := h m (by omega) 1 0 le_rfl (by rw [Real.rpow_one]; push_cast; exact hl) (Nat.coprime_zero_left 1 |>.mpr rfl)
  rwa [cnt_one, card_primes_eq, Nat.totient_one, Nat.cast_one, div_one] at this

/-- `π(N) ≥ N/(2 log N)` for `N` large (from Siegel–Walfisz at `q = 1`). -/
theorem pi_lower (hSW : SiegelWalfisz) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / (2 * Real.log N) ≤ Nat.primeCounting N := by
  obtain ⟨c, hc, C, hC, h⟩ := pi_SW hSW
  obtain ⟨L₀, hL₀, hL⟩ := ev_poly_exp 1 hc (4 * C)
  refine ⟨⌈Real.exp L₀⌉₊ + 8, fun N hN => ?_⟩
  set Nr : ℝ := (N : ℝ) with hNr
  have hN8 : (8 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 8 ≤ N)
  set L := Real.log Nr
  have hLL : L₀ ≤ L := by
    have : Real.exp L₀ ≤ Nr := le_trans (Nat.le_ceil _) (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp L₀⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; exact this
  have hL0 : 0 < L := by linarith
  have hli : (Nr - 2) / L ≤ liK 0 Nr := by
    have := liK_diff_ge (le_refl (2 : ℝ)) (by linarith : (2 : ℝ) ≤ Nr)
    rwa [liK_of_le_two 0 le_rfl, sub_zero] at this
  have hE : C * Nr * Real.exp (-c * √L) ≤ Nr / (4 * L) := by
    have h1 := hL L hLL
    rw [Real.rpow_one] at h1
    have he : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
    rw [le_div_iff₀ (by positivity)]
    have hp : 0 ≤ Nr * Real.exp (-c * √L) := by positivity
    calc C * Nr * Real.exp (-c * √L) * (4 * L) = Nr * Real.exp (-c * √L) * (4 * C * L) := by ring
      _ ≤ Nr * Real.exp (-c * √L) * Real.exp (c * √L) := mul_le_mul_of_nonneg_left h1 hp
      _ = Nr := by rw [mul_assoc, he, mul_one]
  have h2 := (abs_le.mp (h N (by omega))).1
  rw [← hNr] at h2
  have hdiff : (Nr - 2) / L - Nr / (4 * L) - Nr / (2 * L) = (Nr / 4 - 2) / L := by field_simp; ring
  have : 0 ≤ (Nr / 4 - 2) / L := div_nonneg (by linarith) hL0.le
  linarith

/-- `π(N) ≤ (1 + δ) N/log N` for `N` large (from Siegel–Walfisz at `q = 1`). -/
theorem pi_upper (hSW : SiegelWalfisz) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (Nat.primeCounting N : ℝ) ≤ (1 + δ) * N / Real.log N := by
  obtain ⟨c, hc, C, hC, h⟩ := pi_SW hSW
  set η := δ / (3 + δ) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : 1 - η = 3 / (3 + δ) := by rw [hη]; field_simp; ring
  have hη1' : 0 < 1 - η := by rw [hη1]; positivity
  obtain ⟨L₁, hL₁, hL1⟩ := ev_poly_exp 1 hc (3 * C / δ)
  obtain ⟨L₂, hL₂, hL2⟩ := ev_poly_exp 1 hη0 (3 / (δ * Real.log 2))
  set L₀ := max (max L₁ L₂) (1 / (1 - η))
  refine ⟨⌈Real.exp L₀⌉₊ + 8, fun N hN => ?_⟩
  set Nr : ℝ := (N : ℝ) with hNr
  have hN8 : (8 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 8 ≤ N)
  set L := Real.log Nr
  have hLL : L₀ ≤ L := by
    have : Real.exp L₀ ≤ Nr := le_trans (Nat.le_ceil _) (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp L₀⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; exact this
  have hLa : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hLb : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hLc : 1 / (1 - η) ≤ L := le_trans (le_max_right _ _) hLL
  have hL1' : 1 ≤ L := le_trans hL₁ hLa
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log (by linarith)
  have hl2 := log_two_pos'
  -- the split point `y = e^{(1−η)L}`
  set y := Real.exp ((1 - η) * L)
  have hyL : Real.log y = (1 - η) * L := Real.log_exp _
  have hy1 : 1 ≤ (1 - η) * L := by rwa [div_le_iff₀ hη1', mul_comm] at hLc
  have hy2 : 2 ≤ y := by
    have := Real.add_one_le_exp ((1 - η) * L)
    linarith
  have hyN : y ≤ Nr := by
    rw [← hexpL]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hNy : Nr = y * Real.exp (η * L) := by
    rw [← Real.exp_add, ← hexpL]; congr 1; ring
  have hli : liK 0 Nr ≤ y / Real.log 2 + Nr / ((1 - η) * L) := by
    have h1 := liK_diff_le hy2 hyN
    have h2 := liK_le 0 (by linarith : (0 : ℝ) ≤ y)
    rw [zero_add, pow_one] at h2
    rw [hyL] at h1
    have h3 : (Nr - y) / ((1 - η) * L) ≤ Nr / ((1 - η) * L) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hA : Nr / ((1 - η) * L) = (1 + δ / 3) * Nr / L := by
    rw [hη1]; field_simp
  have hB : y / Real.log 2 ≤ δ / 3 * Nr / L := by
    have h1 := hL2 L hLb
    rw [Real.rpow_one] at h1
    have h1' : 3 / (δ * Real.log 2) * L ≤ Real.exp (η * L) := by
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      have : √L ≤ L := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      nlinarith
    rw [hNy, div_le_div_iff₀ hl2 hL0]
    have hy0 : 0 < y := by linarith
    have : y * (3 / (δ * Real.log 2) * L) ≤ y * Real.exp (η * L) := mul_le_mul_of_nonneg_left h1' hy0.le
    have e : y * (3 / (δ * Real.log 2) * L) * (δ / 3 * Real.log 2) = y * L := by field_simp
    have h5 := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ δ / 3 * Real.log 2)
    rw [e] at h5
    linarith
  have hE : C * Nr * Real.exp (-c * √L) ≤ δ / 3 * Nr / L := by
    have h1 := hL1 L hLa
    rw [Real.rpow_one] at h1
    have he : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
    rw [show δ / 3 * Nr / L = (δ / 3 * Nr) / L by ring, le_div_iff₀ hL0]
    have hp : 0 ≤ Nr * Real.exp (-c * √L) := by positivity
    have : C * Nr * Real.exp (-c * √L) * L * (3 / δ) = Nr * Real.exp (-c * √L) * (3 * C / δ * L) := by ring
    have h3 : Nr * Real.exp (-c * √L) * (3 * C / δ * L) ≤ Nr := by
      calc Nr * Real.exp (-c * √L) * (3 * C / δ * L) ≤ Nr * Real.exp (-c * √L) * Real.exp (c * √L) :=
            mul_le_mul_of_nonneg_left h1 hp
        _ = Nr := by rw [mul_assoc, he, mul_one]
    have e2 : δ / 3 * Nr = Nr * (δ / 3) := by ring
    rw [e2]
    have : C * Nr * Real.exp (-c * √L) * L ≤ Nr * (δ / 3) := by
      have h4 : C * Nr * Real.exp (-c * √L) * L * (3 / δ) ≤ Nr := by linarith
      have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ δ / 3)
      have e3 : C * Nr * Real.exp (-c * √L) * L * (3 / δ) * (δ / 3) = C * Nr * Real.exp (-c * √L) * L := by
        field_simp
      linarith
    linarith
  have h2 := (abs_le.mp (h N (by omega))).2
  rw [← hNr] at h2
  have e : (1 + δ) * Nr / L = (1 + δ / 3) * Nr / L + δ / 3 * Nr / L + δ / 3 * Nr / L := by ring
  rw [e]
  linarith

end ArcsAlgo.Core
