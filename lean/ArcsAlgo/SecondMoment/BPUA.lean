module

public import ArcsAlgo.SecondMoment.BPU2
set_option autoImplicit false

/-!
# Proposition B′, unconditional part: the assembly over abstract reals

`uncond_assemble`: the ratio `Pr(E)·E[Z²]/E[Z]²`-type expansion `1 + κh² + c₂h⁴ + O(h⁶)` once the low
coefficients cancel, with the parity factor `|2 Pr(S_E ≡ u) − 1| ≤ 2^{−m}` and the atom term.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

theorem two_pow_ge_four (m : ℕ) (hm : 16 ≤ m) : (m : ℝ) ^ 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    push_cast
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [h2]
    have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
    have h4 : 16 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by rw [pow_succ]; nlinarith
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have : ((n : ℝ) + 1) ^ 4 ≤ 2 * (n : ℝ) ^ 4 := by nlinarith
    linarith

set_option maxHeartbeats 4000000 in
/-- The final assembly of the unconditional statement, over abstract reals. -/
theorem uncond_assemble {m : ℕ} {LX LY φX φY FX FY dX dY G h A φYm KA KC R lam pe kap c2 a : ℝ}
    (hm16 : 16 ≤ m) (hh : h = 1 / √(m : ℝ)) (hA1 : 1 ≤ A) (hφYm : 0 < φYm)
    (LXe : √(m : ℝ) ^ 2 * LX = 2 * φX * (FX + dX)) (LYe : √(m : ℝ) * LY = 1 * φY * (FY + dY))
    (hcan : φX = φY ^ 2) (hφY : φYm ≤ φY)
    (hE : FX - (1 + KA * h ^ 2 + KC * h ^ 4) * FY ^ 2 = h ^ 6 * G)
    (hFX : |FX| ≤ A) (hFY : |FY| ≤ A) (hK : |1 + KA * h ^ 2 + KC * h ^ 4| ≤ A) (hG : |G| ≤ A)
    (hdX : |dX| ≤ A * h ^ 6) (hdY : |dY| ≤ A * h ^ 6) (hYp : 1 / 2 ≤ FY + dY)
    (hpe : |pe - 1 / 2| ≤ 1 / (2 * 2 ^ m))
    (hR : R = pe * (LX / LY ^ 2)) (hlam : lam = 2 ^ m * LY / pe) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hKA : KA = kap) (hKC : KC = c2) :
    |R - (1 + a / lam + kap / m + c2 / (m : ℝ) ^ 2)| ≤
      (4 * (2 * A + 3 * A ^ 3) + (A + 4 * (2 * A + 3 * A ^ 3)) + 4 / φYm) / (m : ℝ) ^ 3 := by
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
  have hYp' : 0 < FY + dY := by linarith
  have hh6 : 0 ≤ h ^ 6 := by positivity
  have hh61 : h ^ 6 ≤ 1 := pow_le_one₀ h0.le h1
  set K := 1 + KA * h ^ 2 + KC * h ^ 4 with hKdef
  -- the ratio
  have hLY : LY = 1 * φY * (FY + dY) / √(m : ℝ) := by rw [← LYe]; field_simp
  have hLX : LX = 2 * φX * (FX + dX) / √(m : ℝ) ^ 2 := by rw [← LXe]; field_simp
  have hpe0 : 0 < pe := by
    have := (abs_le.mp hpe).1
    have : 1 / (2 * (2 : ℝ) ^ m) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  have hpe1 : pe ≤ 1 := by
    have := (abs_le.mp hpe).2
    have : 1 / (2 * (2 : ℝ) ^ m) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  set Q := (FX + dX) / (FY + dY) ^ 2 with hQ
  have hRQ : R = 2 * pe * Q := by
    rw [hR, hLX, hLY, hcan, hQ]
    field_simp
  -- `|Q − K| ≤ 4(2A + 3A³) h⁶`
  have hd4 : 1 / 4 ≤ (FY + dY) ^ 2 := by nlinarith
  have hQK : |Q - K| ≤ 4 * (2 * A + 3 * A ^ 3) * h ^ 6 := by
    have eN : FX + dX - K * (FY + dY) ^ 2 = h ^ 6 * G + dX - K * (2 * FY * dY + dY ^ 2) := by
      rw [hKdef]; linear_combination hE
    have hd : 0 < (FY + dY) ^ 2 := by positivity
    rw [hQ, div_sub' (ne_of_gt hd), abs_div, abs_of_pos hd, show FX + dX - (FY + dY) ^ 2 * K =
      FX + dX - K * (FY + dY) ^ 2 by ring, eN, div_le_iff₀ hd]
    have b1 : |h ^ 6 * G| ≤ A * h ^ 6 := by rw [abs_mul, abs_of_nonneg hh6]; nlinarith [abs_nonneg G]
    have hdY1 : |dY| ≤ A := by nlinarith
    have b3 : |K * (2 * FY * dY + dY ^ 2)| ≤ 3 * A ^ 3 * h ^ 6 := by
      rw [abs_mul]
      have : |2 * FY * dY + dY ^ 2| ≤ 3 * A ^ 2 * h ^ 6 := by
        calc |2 * FY * dY + dY ^ 2| ≤ |2 * FY * dY| + |dY ^ 2| := abs_add_le _ _
          _ = 2 * |FY| * |dY| + |dY| * |dY| := by rw [abs_mul, abs_mul, abs_two, sq, abs_mul]
          _ ≤ 2 * A * (A * h ^ 6) + A * (A * h ^ 6) := by gcongr
          _ = 3 * A ^ 2 * h ^ 6 := by ring
      calc |K| * |2 * FY * dY + dY ^ 2| ≤ A * (3 * A ^ 2 * h ^ 6) := mul_le_mul hK this (abs_nonneg _) hA
        _ = 3 * A ^ 3 * h ^ 6 := by ring
    have hN : |h ^ 6 * G + dX - K * (2 * FY * dY + dY ^ 2)| ≤ (2 * A + 3 * A ^ 3) * h ^ 6 := by
      calc _ ≤ |h ^ 6 * G + dX| + |K * (2 * FY * dY + dY ^ 2)| := abs_sub _ _
        _ ≤ |h ^ 6 * G| + |dX| + |K * (2 * FY * dY + dY ^ 2)| := by gcongr; exact abs_add_le _ _
        _ ≤ A * h ^ 6 + A * h ^ 6 + 3 * A ^ 3 * h ^ 6 := by gcongr
        _ = (2 * A + 3 * A ^ 3) * h ^ 6 := by ring
    have : 0 ≤ (2 * A + 3 * A ^ 3) * h ^ 6 := by positivity
    nlinarith
  have hQb : |Q| ≤ A + 4 * (2 * A + 3 * A ^ 3) := by
    have := abs_sub_abs_le_abs_sub Q K
    have : 4 * (2 * A + 3 * A ^ 3) * h ^ 6 ≤ 4 * (2 * A + 3 * A ^ 3) := by
      have : 0 ≤ 4 * (2 * A + 3 * A ^ 3) := by positivity
      nlinarith
    linarith
  -- `|R − K| ≤ 4(2A + 3A³) h⁶ + |Q| 2^{−m}`
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hRK : |R - K| ≤ 4 * (2 * A + 3 * A ^ 3) * h ^ 6 + (A + 4 * (2 * A + 3 * A ^ 3)) / 2 ^ m := by
    rw [hRQ, show 2 * pe * Q - K = (2 * pe - 1) * Q + (Q - K) by ring]
    have h2pe : |2 * pe - 1| ≤ 1 / 2 ^ m := by
      rw [show 2 * pe - 1 = 2 * (pe - 1 / 2) by ring, abs_mul, abs_two]
      calc 2 * |pe - 1 / 2| ≤ 2 * (1 / (2 * 2 ^ m)) := by gcongr
        _ = 1 / 2 ^ m := by field_simp
    calc |(2 * pe - 1) * Q + (Q - K)| ≤ |(2 * pe - 1) * Q| + |Q - K| := abs_add_le _ _
      _ = |2 * pe - 1| * |Q| + |Q - K| := by rw [abs_mul]
      _ ≤ 1 / 2 ^ m * (A + 4 * (2 * A + 3 * A ^ 3)) + 4 * (2 * A + 3 * A ^ 3) * h ^ 6 := by
          gcongr
      _ = _ := by ring
  have hh2 : h ^ 2 = 1 / m := by rw [hh, div_pow, hsm2, one_pow]
  have hh4 : h ^ 4 = 1 / (m : ℝ) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hh2]; ring
  have hh6v : h ^ 6 = 1 / (m : ℝ) ^ 3 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hh2]; ring
  have hKv : K = 1 + kap / m + c2 / (m : ℝ) ^ 2 := by rw [hKdef, hh2, hh4, hKA, hKC]; ring
  have h4 := two_pow_ge_four m hm16
  have hm3 : (m : ℝ) ^ 3 ≤ 2 ^ m := by
    have : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ m)) (by norm_num)
    linarith
  -- the atom term: `λ ≥ 2^m φ_min/(2√m)`
  have hlam_lb : 2 ^ m * φYm / (2 * √(m : ℝ)) ≤ lam := by
    rw [hlam, hLY, div_le_div_iff₀ (by positivity) hpe0]
    have k1 : φYm * (1 / 2) ≤ φY * (FY + dY) := mul_le_mul hφY hYp (by norm_num) hφY0.le
    rw [show 2 ^ m * (1 * φY * (FY + dY) / √(m : ℝ)) * (2 * √(m : ℝ)) = 2 ^ m * (2 * (φY * (FY + dY))) by
      field_simp]
    have : 2 ^ m * φYm * pe ≤ 2 ^ m * φYm * 1 := by gcongr
    nlinarith
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam_lb
  have hat : a / lam ≤ 4 / φYm / (m : ℝ) ^ 3 := by
    have hsmm : √(m : ℝ) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
    rw [div_le_div_iff₀ hlam0 (by positivity)]
    calc a * (m : ℝ) ^ 3 ≤ 2 * (m : ℝ) ^ 3 := by gcongr
      _ = 4 / φYm * (φYm * (m : ℝ) ^ 3 / 2) := by field_simp; ring
      _ ≤ 4 / φYm * (2 ^ m * φYm / (2 * √(m : ℝ))) := by
          have key : φYm * (m : ℝ) ^ 3 / 2 ≤ 2 ^ m * φYm / (2 * √(m : ℝ)) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            calc φYm * (m : ℝ) ^ 3 * (2 * √(m : ℝ)) ≤ φYm * (m : ℝ) ^ 3 * (2 * m) := by gcongr
              _ = 2 * (φYm * (m : ℝ) ^ 4) := by ring
              _ ≤ 2 * (φYm * 2 ^ m) := by gcongr
              _ = 2 ^ m * φYm * 2 := by ring
          exact mul_le_mul_of_nonneg_left key (by positivity)
      _ ≤ 4 / φYm * lam := by gcongr
  have hat0 : 0 ≤ a / lam := div_nonneg ha0 hlam0.le
  have hfin : |R - (1 + a / lam + kap / m + c2 / (m : ℝ) ^ 2)| ≤ |R - K| + a / lam := by
    rw [hKv, show R - (1 + a / lam + kap / m + c2 / (m : ℝ) ^ 2) = (R - (1 + kap / m + c2 / (m : ℝ) ^ 2)) - a / lam
      by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hat0]
  have hB : (A + 4 * (2 * A + 3 * A ^ 3)) / 2 ^ m ≤ (A + 4 * (2 * A + 3 * A ^ 3)) / (m : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hm3
  calc _ ≤ |R - K| + a / lam := hfin
    _ ≤ 4 * (2 * A + 3 * A ^ 3) * h ^ 6 + (A + 4 * (2 * A + 3 * A ^ 3)) / 2 ^ m + 4 / φYm / (m : ℝ) ^ 3 := by
        linarith
    _ ≤ 4 * (2 * A + 3 * A ^ 3) * (1 / (m : ℝ) ^ 3) + (A + 4 * (2 * A + 3 * A ^ 3)) / (m : ℝ) ^ 3 +
          4 / φYm / (m : ℝ) ^ 3 := by rw [hh6v]; linarith
    _ = _ := by ring

end ArcsAlgo.LLT
