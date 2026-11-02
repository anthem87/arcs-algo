module

public import ArcsAlgo.SecondMoment.BPUA
set_option autoImplicit false

/-!
# Proposition B′, unconditional part (as corrected)

`propBprime_uncond`: for fixed `M ≥ 2`, on the event `S_E ≡ u (mod 2)` and uniformly in `|u| ≤ M`,
`E[Z²]/Z̄² = 1 + (1 + 1[u = 0])/Z̄ + κ/m + c₂(M, u)/m² + O(m^{−3})` with `c₂(M, u) = c₂(M, 0) − 2κu²/Ew²`,
from [BR, Theorem 22.1] (`BR22Edge`) at order 7 for `X′ = (εw, ε′w)` and `Y′ = εw` (`P₁ = P₃ = P₅ = 0`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

theorem bnd_poly6 {h a b c A0 A : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (ha : |a| ≤ A0) (hb : |b| ≤ A0)
    (hc : |c| ≤ A0) (hA : 3 * A0 + 1 ≤ A) :
    |1 + h ^ 2 * a + h ^ 4 * b + h ^ 6 * c| ≤ A := by
  have q2 : 0 ≤ h ^ 2 := by positivity
  have q4 : 0 ≤ h ^ 4 := by positivity
  have q6 : 0 ≤ h ^ 6 := by positivity
  have r2 : h ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have r4 : h ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have r6 : h ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have ea : |h ^ 2 * a| ≤ A0 := by rw [abs_mul, abs_of_nonneg q2]; nlinarith [abs_nonneg a]
  have eb : |h ^ 4 * b| ≤ A0 := by rw [abs_mul, abs_of_nonneg q4]; nlinarith [abs_nonneg b]
  have ec : |h ^ 6 * c| ≤ A0 := by rw [abs_mul, abs_of_nonneg q6]; nlinarith [abs_nonneg c]
  calc _ ≤ |1 + h ^ 2 * a + h ^ 4 * b| + |h ^ 6 * c| := abs_add_le _ _
    _ ≤ |1 + h ^ 2 * a| + |h ^ 4 * b| + |h ^ 6 * c| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 + |h ^ 2 * a| + |h ^ 4 * b| + |h ^ 6 * c| := by
        gcongr; exact (abs_add_le _ _).trans (by rw [abs_one])
    _ ≤ A := by linarith

theorem half_le_poly6 {h a b c A0 A e : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (ha : |a| ≤ A0) (hb : |b| ≤ A0)
    (hc : |c| ≤ A0) (hA : 3 * A0 + 1 ≤ A) (he : |e| ≤ A * h ^ 6) (hhA : h * A ≤ 1 / 4) :
    1 / 2 ≤ (1 + h ^ 2 * a + h ^ 4 * b + h ^ 6 * c) + e := by
  have r2 : h ^ 2 ≤ h := by nlinarith
  have r4 : h ^ 4 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 3)]
  have r6 : h ^ 6 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 5)]
  have q2 : 0 ≤ h ^ 2 := by positivity
  have q4 : 0 ≤ h ^ 4 := by positivity
  have q6 : 0 ≤ h ^ 6 := by positivity
  have ea : |h ^ 2 * a| ≤ h * A0 := by rw [abs_mul, abs_of_nonneg q2]; nlinarith [abs_nonneg a]
  have eb : |h ^ 4 * b| ≤ h * A0 := by rw [abs_mul, abs_of_nonneg q4]; nlinarith [abs_nonneg b]
  have ec : |h ^ 6 * c| ≤ h * A0 := by rw [abs_mul, abs_of_nonneg q6]; nlinarith [abs_nonneg c]
  have hA0 : 0 ≤ A0 := le_trans (abs_nonneg a) ha
  have hAA : 0 ≤ A := by linarith
  have := (abs_le.mp ea).1; have := (abs_le.mp eb).1; have := (abs_le.mp ec).1
  have := (abs_le.mp he).1
  have : A * h ^ 6 ≤ h * A := by nlinarith
  have : h * (3 * A0) ≤ h * A := mul_le_mul_of_nonneg_left (by linarith) h0
  nlinarith

/-- The coefficient `c₂(M, 0)` of `m⁻²` without conditioning, at `u = 0`. -/
noncomputable def c2B (M : ℕ) : ℝ := CCu M 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Proposition B′, unconditional part** (paper §6.3, as corrected). Fix `M ≥ 2`. On the event
`S_E ≡ u (mod 2)`, uniformly in `|u| ≤ M`, with `Z̄ = E[Z | S_E ≡ u (mod 2)]`,
`E[Z² | S_E ≡ u]/Z̄² = 1 + (1 + 1[u = 0])/Z̄ + κ/m + c₂(M, u)/m² + O_M(m^{−3})`,
`c₂(M, u) = c₂(M, 0) − 2κu²/Ew²`. Hypothesis: [BR, Theorem 22.1] (`BR22Edge`) only. -/
theorem propBprime_uncond (hBR : BR22Edge) (hM : 2 ≤ M) :
    ∃ C : ℝ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ u : ℤ, |(u : ℝ)| ≤ M →
      |m2U M m u / lamU M m u ^ 2 - (1 + (1 + if u = 0 then 1 else 0) / lamU M m u + kapB M / m +
        (c2B M - 2 * kapB M * (u : ℝ) ^ 2 / ew2 M) / (m : ℝ) ^ 2)| ≤ C / (m : ℝ) ^ 3 := by
  have hM1 : 1 ≤ M := by omega
  obtain ⟨CX, hCX, hX⟩ := brXu7 hBR hM
  obtain ⟨CY, hCY, hY⟩ := brYu7 hBR hM
  obtain ⟨A0, hA0, hb⟩ := coef_boundsU M M
  have he := ew2_pos M
  have hm2 := mw2_pos hM1
  obtain ⟨φYm, hφYmd⟩ : ∃ x : ℝ, x = Real.exp (-(1 / 2) * ((M : ℝ) ^ 2 / ew2 M)) /
      (√(2 * Real.pi) ^ 1 * √(ew2 M)) := ⟨_, rfl⟩
  have hπ : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hse := Real.sqrt_pos.mpr he
  have hφYm : 0 < φYm := by rw [hφYmd]; positivity
  have hφXm : 0 < φYm ^ 2 := by positivity
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = 3 * A0 + 1 + |KKu M| + |CCu M 0| + 2 * |kapB M| * (M : ℝ) ^ 2 / mw M 2 +
      CX / (2 * φYm ^ 2) + CY / (1 * φYm) := ⟨_, rfl⟩
  have q1 : 0 ≤ CX / (2 * φYm ^ 2) := by positivity
  have q2 : 0 ≤ CY / (1 * φYm) := by positivity
  have q3 : 0 ≤ 2 * |kapB M| * (M : ℝ) ^ 2 / mw M 2 := by positivity
  have q4 := abs_nonneg (KKu M)
  have q5 := abs_nonneg (CCu M 0)
  have hA1 : 1 ≤ A := by rw [hAd]; linarith
  refine ⟨4 * (2 * A + 3 * A ^ 3) + (A + 4 * (2 * A + 3 * A ^ 3)) + 4 / φYm, max 16 (⌈(4 * A) ^ 2⌉₊ + 1),
    fun m hm u hu => ?_⟩
  have hm16 : 16 ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsm := Real.sqrt_pos.mpr hmr
  have hmA : (4 * A) ^ 2 ≤ (m : ℝ) := by
    have h1 := Nat.le_ceil ((4 * A) ^ 2)
    have h2 : ((⌈(4 * A) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
    push_cast at h2; linarith
  have hsA : 4 * A ≤ √(m : ℝ) := Real.le_sqrt_of_sq_le hmA
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / √(m : ℝ) := ⟨_, rfl⟩
  have h0 : 0 < h := by rw [hh]; positivity
  have h1 : h ≤ 1 := by rw [hh, div_le_one hsm]; linarith
  have hhA : h * A ≤ 1 / 4 := by
    rw [hh, div_mul_eq_mul_div, one_mul, div_le_iff₀ hsm]; linarith
  have hu' : |(u : ℝ) * h| ≤ M := by
    rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg (u : ℝ)]
  have hu2 : ((u : ℝ) * h) ^ 2 ≤ (M : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hu' 2; rwa [sq_abs] at this
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb h u h0.le h1 hu
  have eXb := hX m hm1 u
  have eYb := hY m hm1 u
  rw [← hh] at eXb eYb
  simp only [pow_one] at eYb
  obtain ⟨dX, LXe, hdX⟩ := rel_ex (A := A) hφXm (hφYmd ▸ gaussXu_lb hM hu2) (by norm_num : (0 : ℝ) < 2)
    (by positivity) eXb (by rw [hAd]; linarith) hCX
  obtain ⟨dY, LYe, hdY⟩ := rel_ex (A := A) hφYm (hφYmd ▸ gaussYu_lb hM hu2) (by norm_num : (0 : ℝ) < 1)
    (by positivity) eYb (by rw [hAd]; linarith) hCY
  have hE := gen_uncond (FXut2 M u) (FXut4 M u) (FXuB M h u) (FYut2 M u) (FYut4 M u) (FYuB M h u)
    (KKu M) (CCu M u) h (coefU_e2 hM u) (coefU_e4 hM u)
  have hA3 : 3 * A0 + 1 ≤ A := by rw [hAd]; linarith
  have hYp := half_le_poly6 h0.le h1 b4 b5 b6 hA3 hdY hhA
  have hφY := hφYmd ▸ gaussYu_lb hM hu2
  have hφY0 := lt_of_lt_of_le hφYm hφY
  have hCCu : CCu M u = c2B M - 2 * kapB M * (u : ℝ) ^ 2 / ew2 M := by
    rw [CCu_eq hM, ew2_mw hM1]; rfl
  have hK : |1 + KKu M * h ^ 2 + CCu M u * h ^ 4| ≤ A := by
    have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
    have hh4 : h ^ 4 ≤ 1 := pow_le_one₀ h0.le h1
    have hc : |CCu M u| ≤ |CCu M 0| + 2 * |kapB M| * (M : ℝ) ^ 2 / mw M 2 := by
      rw [CCu_eq hM]
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hm2, abs_two]
      apply div_le_div_of_nonneg_right _ hm2.le
      have : |(u : ℝ) ^ 2| ≤ (M : ℝ) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        have := pow_le_pow_left₀ (abs_nonneg _) hu 2; rwa [sq_abs] at this
      have := abs_nonneg (kapB M)
      nlinarith
    have e2 : |KKu M * h ^ 2| ≤ |KKu M| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2)]; nlinarith [abs_nonneg (KKu M)]
    have e4 : |CCu M u * h ^ 4| ≤ |CCu M u| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 4)]; nlinarith [abs_nonneg (CCu M u)]
    calc _ ≤ |1 + KKu M * h ^ 2| + |CCu M u * h ^ 4| := abs_add_le _ _
      _ ≤ 1 + |KKu M * h ^ 2| + |CCu M u * h ^ 4| := by
          gcongr; exact (abs_add_le _ _).trans (by rw [abs_one])
      _ ≤ A := by rw [hAd]; linarith
  have hpe : |parE M m u - 1 / 2| ≤ 1 / (2 * 2 ^ m) := by
    refine (parE_near hM1 m u).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (2 : ℝ) ^ m ≤ (M : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hM) m
    linarith
  have hpe0 : 0 < parE M m u := by
    have := (abs_le.mp hpe).1
    have : 1 / (2 * (2 : ℝ) ^ m) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  have hLY := pos_of_eq3 (k := 1) hsm (by rw [pow_one]; exact LYe) (by norm_num) hφY0 (by linarith)
  have hite0 : (0 : ℝ) ≤ 1 + if u = 0 then 1 else 0 := by split_ifs <;> norm_num
  have hite2 : (1 + if u = 0 then 1 else 0 : ℝ) ≤ 2 := by split_ifs <;> norm_num
  exact uncond_assemble (m := m) hm16 hh hA1 hφYm LXe LYe (gauss_cancelU hM ((u : ℝ) * h)) hφY hE
    (bnd_poly6 h0.le h1 b1 b2 b3 hA3) (bnd_poly6 h0.le h1 b4 b5 b6 hA3) hK
    (show |GU M h u| ≤ A by linarith) hdX hdY hYp hpe
    (ratio_lawsU hM m u hLY.ne' hpe0.ne') (lamU_laws hM m u) hite0 hite2 (KKu_eq hM) hCCu

end ArcsAlgo.LLT
