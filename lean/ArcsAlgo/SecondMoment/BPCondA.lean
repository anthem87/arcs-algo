module

public import ArcsAlgo.SecondMoment.BPMain2
set_option autoImplicit false

/-!
# Proposition B′: the assembly of the conditional statement, over abstract reals

`cond_core` (the ratio of the three local laws is `1 + κ_c h² + γ_M z h³ + O(h⁴)` once the low coefficients
cancel), `cond_assemble` (with the atom term `(1 + 1[u = 0])/λ`, exponentially small), and elementary bounds.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

/-- The algebraic core of the conditional statement. -/
theorem cond_core {LX LY LS φX φY φS FX FY FS dX dY dS K G h A t : ℝ}
    (ht : 0 < t) (hX : t ^ 3 * LX = 4 * φX * (FX + dX)) (hY : t ^ 2 * LY = 2 * φY * (FY + dY))
    (hS : t * LS = 1 * φS * (FS + dS)) (hcan : φX * φS = φY ^ 2) (hφY : 0 < φY)
    (hE : FX * FS - K * FY ^ 2 = h ^ 4 * G) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hA : 0 ≤ A)
    (hFX : |FX| ≤ A) (hFS : |FS| ≤ A) (hFY : |FY| ≤ A) (hK : |K| ≤ A) (hG : |G| ≤ A)
    (hdX : |dX| ≤ A * h ^ 4) (hdS : |dS| ≤ A * h ^ 4) (hdY : |dY| ≤ A * h ^ 4) (hYp : 1 / 2 ≤ FY + dY) :
    |LX * LS / LY ^ 2 - K| ≤ 4 * (A + 3 * A ^ 2 + 3 * A ^ 3) * h ^ 4 := by
  have hYp' : 0 < FY + dY := by linarith
  have ht2 : t ^ 2 ≠ 0 := by positivity
  have ht3 : t ^ 3 ≠ 0 := by positivity
  have hLY : LY = 2 * φY * (FY + dY) / t ^ 2 := by rw [← hY]; field_simp
  have hLX : LX = 4 * φX * (FX + dX) / t ^ 3 := by rw [← hX]; field_simp
  have hLS : LS = 1 * φS * (FS + dS) / t := by rw [← hS]; field_simp
  have e : LX * LS / LY ^ 2 = (FX + dX) * (FS + dS) / (FY + dY) ^ 2 := by
    rw [hLX, hLS, hLY, div_eq_div_iff (by positivity) (by positivity)]
    calc 4 * φX * (FX + dX) / t ^ 3 * (1 * φS * (FS + dS) / t) * (FY + dY) ^ 2
        = 4 * (φX * φS) * ((FX + dX) * (FS + dS)) * (FY + dY) ^ 2 / t ^ 4 := by field_simp <;> ring
      _ = 4 * φY ^ 2 * ((FX + dX) * (FS + dS)) * (FY + dY) ^ 2 / t ^ 4 := by rw [hcan]
      _ = _ := by field_simp <;> ring
  rw [e]
  exact ratio_err hE h0 h1 hA hFX hFS hFY hK hG hdX hdS hdY hYp

theorem rel_ex {L φ F E C φm A c : ℝ} (hφm : 0 < φm) (hφ : φm ≤ φ) (hc : 0 < c) (hE : 0 ≤ E)
    (h : |L - c * (φ * F)| ≤ C * E) (hA : C / (c * φm) ≤ A) (hC : 0 ≤ C) :
    ∃ d, L = c * φ * (F + d) ∧ |d| ≤ A * E :=
  ⟨_, (rel_of_abs hφm hφ hc hE h hA hC).1, (rel_of_abs hφm hφ hc hE h hA hC).2⟩

theorem poly4_bounds {h a b c d : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    |1 + h * a + h ^ 2 * b + h ^ 3 * c + h ^ 4 * d| ≤ 1 + |a| + |b| + |c| + |d| ∧
    1 - h * (|a| + |b| + |c| + |d|) ≤ 1 + h * a + h ^ 2 * b + h ^ 3 * c + h ^ 4 * d := by
  have p2 : h ^ 2 ≤ h := by nlinarith
  have p3 : h ^ 3 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 2)]
  have p4 : h ^ 4 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 3)]
  have q2 : 0 ≤ h ^ 2 := by positivity
  have q3 : 0 ≤ h ^ 3 := by positivity
  have q4 : 0 ≤ h ^ 4 := by positivity
  have ea : |h * a| ≤ h * |a| := by rw [abs_mul, abs_of_nonneg h0]
  have eb : |h ^ 2 * b| ≤ h * |b| := by rw [abs_mul, abs_of_nonneg q2]; nlinarith [abs_nonneg b]
  have ec : |h ^ 3 * c| ≤ h * |c| := by rw [abs_mul, abs_of_nonneg q3]; nlinarith [abs_nonneg c]
  have ed : |h ^ 4 * d| ≤ h * |d| := by rw [abs_mul, abs_of_nonneg q4]; nlinarith [abs_nonneg d]
  have ha := abs_nonneg a; have hb := abs_nonneg b; have hc := abs_nonneg c; have hd := abs_nonneg d
  constructor
  · calc _ ≤ |1 + h * a + h ^ 2 * b + h ^ 3 * c| + |h ^ 4 * d| := abs_add_le _ _
      _ ≤ |1 + h * a + h ^ 2 * b| + |h ^ 3 * c| + |h ^ 4 * d| := by gcongr; exact abs_add_le _ _
      _ ≤ |1 + h * a| + |h ^ 2 * b| + |h ^ 3 * c| + |h ^ 4 * d| := by gcongr; exact abs_add_le _ _
      _ ≤ 1 + |h * a| + |h ^ 2 * b| + |h ^ 3 * c| + |h ^ 4 * d| := by
          gcongr; exact (abs_add_le _ _).trans (by rw [abs_one])
      _ ≤ 1 + h * |a| + h * |b| + h * |c| + h * |d| := by gcongr
      _ ≤ 1 + |a| + |b| + |c| + |d| := by nlinarith
  · have := (abs_le.mp ea).1; have := (abs_le.mp eb).1; have := (abs_le.mp ec).1; have := (abs_le.mp ed).1
    nlinarith

set_option maxHeartbeats 4000000 in
/-- The final assembly of the conditional statement, over abstract reals. -/
theorem cond_assemble {m : ℕ} {LX LY LS φX φY φS FX FY FS dX dY dS G h A c0 φYm φSM KA KB R lam kapc gam za a : ℝ}
    (hm10 : 10 ≤ m) (hh : h = 1 / √(m : ℝ)) (hA1 : 1 ≤ A) (hc0d : c0 = φYm / (2 * A * φSM))
    (hφYm : 0 < φYm) (hφSM : 0 < φSM)
    (LXe : √(m : ℝ) ^ 3 * LX = 4 * φX * (FX + dX)) (LYe : √(m : ℝ) ^ 2 * LY = 2 * φY * (FY + dY))
    (LSe : √(m : ℝ) * LS = 1 * φS * (FS + dS)) (hcan : φX * φS = φY ^ 2) (hφY : φYm ≤ φY)
    (hφS0 : 0 < φS) (hφSle : φS ≤ φSM)
    (hE : FX * FS - (1 + KA * h ^ 2 + KB * h ^ 3) * FY ^ 2 = h ^ 4 * G)
    (hFX : |FX| ≤ A) (hFS : |FS| ≤ A) (hFY : |FY| ≤ A) (hK : |1 + KA * h ^ 2 + KB * h ^ 3| ≤ A) (hG : |G| ≤ A)
    (hdX : |dX| ≤ A * h ^ 4) (hdS : |dS| ≤ A * h ^ 4) (hdY : |dY| ≤ A * h ^ 4)
    (hYp : 1 / 2 ≤ FY + dY) (hSp : 1 / 2 ≤ FS + dS)
    (hR : R = LX * LS / LY ^ 2) (hlam : lam = 2 ^ m * LY / LS) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hKA : KA = kapc) (hKB : KB = gam * za) :
    |R - (1 + a / lam + kapc / m + gam * za / (m * √(m : ℝ)))| ≤
      (4 * (A + 3 * A ^ 2 + 3 * A ^ 3) + 2 / c0) / (m : ℝ) ^ 2 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsm := Real.sqrt_pos.mpr hmr
  have hA : 0 ≤ A := by linarith
  have hsm2 : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hmr.le
  have h0 : 0 < h := by rw [hh]; positivity
  have h1 : h ≤ 1 := by
    rw [hh, div_le_one hsm]
    have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ √(m : ℝ) := Real.sqrt_le_sqrt this
  have hφY0 : 0 < φY := lt_of_lt_of_le hφYm hφY
  have hcore := cond_core hsm LXe LYe LSe hcan hφY0 hE h0.le h1 hA hFX hFS hFY hK hG hdX hdS hdY hYp
  rw [← hR] at hcore
  have hh2 : h ^ 2 = 1 / m := by rw [hh, div_pow, hsm2, one_pow]
  have hh3 : h ^ 3 = 1 / (m * √(m : ℝ)) := by
    rw [hh, div_pow, one_pow, pow_succ, hsm2]
  have hh4 : h ^ 4 = 1 / (m : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hh2]; ring
  have hKv : 1 + KA * h ^ 2 + KB * h ^ 3 = 1 + kapc / m + gam * za / (m * √(m : ℝ)) := by
    rw [hh2, hh3, hKA, hKB]; ring
  rw [hKv, hh4] at hcore
  -- the atom term
  have hLY : 0 < LY := by
    have : 0 < √(m : ℝ) ^ 2 * LY := by rw [LYe]; have := hYp; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hLS : 0 < LS := by
    have : 0 < √(m : ℝ) * LS := by rw [LSe]; have := hSp; positivity
    exact pos_of_mul_pos_right this hsm.le
  have hSle : FS + dS ≤ 2 * A := by
    have := (abs_le.mp hFS).2; have := (abs_le.mp hdS).2
    have : A * h ^ 4 ≤ A := by
      have : h ^ 4 ≤ 1 := pow_le_one₀ h0.le h1
      nlinarith
    linarith
  have hlam_lb : c0 * 2 ^ m / √(m : ℝ) ≤ lam := by
    have hLYv : LY = 2 * φY * (FY + dY) / √(m : ℝ) ^ 2 := by rw [← LYe]; field_simp
    have hLSv : LS = 1 * φS * (FS + dS) / √(m : ℝ) := by rw [← LSe]; field_simp
    rw [hlam, hLYv, hLSv, hc0d]
    have k1 : φYm * (1 / 2) ≤ φY * (FY + dY) := mul_le_mul hφY hYp (by norm_num) hφY0.le
    have k2 : φS * (FS + dS) ≤ φSM * (2 * A) := mul_le_mul hφSle hSle (by linarith) hφSM.le
    have hS0 : 0 < φS * (FS + dS) := by have := hSp; positivity
    rw [show 2 ^ m * (2 * φY * (FY + dY) / √(m : ℝ) ^ 2) / (1 * φS * (FS + dS) / √(m : ℝ)) =
      2 ^ m * (2 * (φY * (FY + dY))) / (√(m : ℝ) * (φS * (FS + dS))) by field_simp <;> ring]
    rw [div_le_div_iff₀ hsm (by positivity)]
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : φYm * 2 ^ m * (√(m : ℝ) * (φS * (FS + dS))) ≤ φYm * 2 ^ m * (√(m : ℝ) * (φSM * (2 * A))) := by
      gcongr
    have : φYm * (2 * A * φSM) ≤ 2 * (φY * (FY + dY)) * (2 * A * φSM) := by
      have : 0 ≤ 2 * A * φSM := by positivity
      nlinarith
    calc φYm * 2 ^ m * (√(m : ℝ) * (φS * (FS + dS))) ≤ φYm * 2 ^ m * (√(m : ℝ) * (φSM * (2 * A))) := by gcongr
      _ = (φYm * (2 * A * φSM)) * (2 ^ m * √(m : ℝ)) := by ring
      _ ≤ (2 * (φY * (FY + dY)) * (2 * A * φSM)) * (2 ^ m * √(m : ℝ)) := by gcongr
      _ = 2 ^ m * (2 * (φY * (FY + dY))) * √(m : ℝ) * (2 * A * φSM) := by ring
  have hc0 : 0 < c0 := by rw [hc0d]; positivity
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam_lb
  have hat : a / lam ≤ 2 / c0 / (m : ℝ) ^ 2 := by
    have hcube := two_pow_ge_cube m hm10
    have hsmm : √(m : ℝ) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
    rw [div_le_div_iff₀ hlam0 (by positivity)]
    calc a * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ 2 := by gcongr
      _ = 2 / c0 * (c0 * ((m : ℝ) ^ 2)) := by field_simp
      _ ≤ 2 / c0 * (c0 * 2 ^ m / √(m : ℝ)) := by
          gcongr
          rw [le_div_iff₀ hsm]
          calc c0 * (m : ℝ) ^ 2 * √(m : ℝ) ≤ c0 * (m : ℝ) ^ 2 * m := by gcongr
            _ = c0 * (m : ℝ) ^ 3 := by ring
            _ ≤ c0 * 2 ^ m := by gcongr
      _ ≤ 2 / c0 * lam := by gcongr
  have hat0 : 0 ≤ a / lam := div_nonneg ha0 hlam0.le
  have : |R - (1 + a / lam + kapc / m + gam * za / (m * √(m : ℝ)))| ≤
      |R - (1 + kapc / m + gam * za / (m * √(m : ℝ)))| + a / lam := by
    rw [show R - (1 + a / lam + kapc / m + gam * za / (m * √(m : ℝ))) =
      (R - (1 + kapc / m + gam * za / (m * √(m : ℝ)))) - a / lam by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hat0]
  calc _ ≤ |R - (1 + kapc / m + gam * za / (m * √(m : ℝ)))| + a / lam := this
    _ ≤ 4 * (A + 3 * A ^ 2 + 3 * A ^ 3) * (1 / (m : ℝ) ^ 2) + 2 / c0 / (m : ℝ) ^ 2 := add_le_add hcore hat
    _ = _ := by ring

theorem bnd_poly4 {h a b c d A0 A : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (ha : |a| ≤ A0) (hb : |b| ≤ A0)
    (hc : |c| ≤ A0) (hd : |d| ≤ A0) (hA : 4 * A0 + 1 ≤ A) :
    |1 + h * a + h ^ 2 * b + h ^ 3 * c + h ^ 4 * d| ≤ A := by
  have := (poly4_bounds (a := a) (b := b) (c := c) (d := d) h0 h1).1
  linarith

theorem half_le_poly4 {h a b c d A0 A e : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (ha : |a| ≤ A0) (hb : |b| ≤ A0)
    (hc : |c| ≤ A0) (hd : |d| ≤ A0) (hA : 4 * A0 + 1 ≤ A) (he : |e| ≤ A * h ^ 4) (hhA : h * A ≤ 1 / 4) :
    1 / 2 ≤ (1 + h * a + h ^ 2 * b + h ^ 3 * c + h ^ 4 * d) + e := by
  have p := (poly4_bounds (a := a) (b := b) (c := c) (d := d) h0 h1).2
  have hh4 : h ^ 4 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 3)]
  have q : h * (|a| + |b| + |c| + |d|) ≤ h * A := mul_le_mul_of_nonneg_left (by linarith) h0
  have hA0 : 0 ≤ A := by linarith [abs_nonneg a]
  have q2 : A * h ^ 4 ≤ h * A := by nlinarith
  have := (abs_le.mp he).1
  linarith

theorem bnd_K {h k2 k3 z g A : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (hz : |z| ≤ g) (hA : 1 + |k2| + |k3| * g ≤ A) :
    |1 + k2 * h ^ 2 + k3 * z * h ^ 3| ≤ A := by
  have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have hh3 : h ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have e2 : |k2 * h ^ 2| ≤ |k2| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2)]; nlinarith [abs_nonneg k2]
  have e3 : |k3 * z * h ^ 3| ≤ |k3| * g := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 3)]
    have := abs_nonneg k3; have := abs_nonneg z
    calc |k3| * |z| * h ^ 3 ≤ |k3| * |z| * 1 := by gcongr
      _ ≤ |k3| * g := by rw [mul_one]; gcongr
  calc _ ≤ |1 + k2 * h ^ 2| + |k3 * z * h ^ 3| := abs_add_le _ _
    _ ≤ 1 + |k2 * h ^ 2| + |k3 * z * h ^ 3| := by
        gcongr; exact (abs_add_le _ _).trans (by rw [abs_one])
    _ ≤ A := by linarith

end ArcsAlgo.LLT
