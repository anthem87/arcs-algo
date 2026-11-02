module

public import ArcsAlgo.SecondMoment.BPCondA
set_option autoImplicit false

/-!
# Proposition B′, conditional part

`propBprime_cond`: for fixed `M ≥ 2` and `g ≥ 0`, uniformly in `|z| ≤ g`, `|u| ≤ M`, `u ≡ s (mod 2)`,
`E[Z² | S_E = s]/Z̄² = 1 + (1 + 1[u = 0])/Z̄ + κ_c/m + γ_M z/m^{3/2} + O(m^{−2})`, from [BR, Theorem 22.1]
(`BR22Edge`) applied to `X = (w, εw, ε′w)`, `Y = (w, εw)` and `w` at order 5.
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

theorem pos_of_eq3 {t L c φ F : ℝ} {k : ℕ} (ht : 0 < t) (hL : t ^ k * L = c * φ * F) (hc : 0 < c) (hφ : 0 < φ)
    (hF : 0 < F) : 0 < L := by
  have : 0 < t ^ k * L := by rw [hL]; positivity
  exact pos_of_mul_pos_right this (by positivity)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Proposition B′, conditional part** (paper §6.3). Fix `M ≥ 2` and `g ≥ 0`, put
`z = (s − mμ)/(σ√m)`. Uniformly in `|z| ≤ g` and `|u| ≤ M` with `u ≡ s (mod 2)`, with `Z̄ = λ = E[Z | S_E = s]`,
`E[Z² | S_E = s]/Z̄² = 1 + (1 + 1[u = 0])/Z̄ + κ_c/m + γ_M z/m^{3/2} + O_{M,g}(m^{−2})`.
Hypothesis: [BR, Theorem 22.1] (`BR22Edge`) only. -/
theorem propBprime_cond (hBR : BR22Edge) (hM : 2 ≤ M) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ, |zB M m s| ≤ g → |(u : ℝ)| ≤ M → (2 : ℤ) ∣ u - s →
      |m2B M m s u / lamB M m s u ^ 2 - (1 + (1 + if u = 0 then 1 else 0) / lamB M m s u + kapcB M / m +
        gamB M * zB M m s / (m * √(m : ℝ)))| ≤ C / (m : ℝ) ^ 2 := by
  have hM1 : 1 ≤ M := by omega
  obtain ⟨CX, hCX, hX⟩ := brX5 hBR hM
  obtain ⟨CY, hCY, hY⟩ := brY5 hBR hM
  obtain ⟨CS, hCS, hS⟩ := brS5 hBR hM
  obtain ⟨A0, hA0, hb⟩ := coef_bounds M g M
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  obtain ⟨φXm, hφXmd⟩ : ∃ x : ℝ, x = Real.exp (-(1 / 2) * (g ^ 2 + 2 * ((M : ℝ) ^ 2 / ew2 M))) /
      (√(2 * Real.pi) ^ 3 * (√(sig2 M) * ew2 M)) := ⟨_, rfl⟩
  obtain ⟨φYm, hφYmd⟩ : ∃ x : ℝ, x = Real.exp (-(1 / 2) * (g ^ 2 + (M : ℝ) ^ 2 / ew2 M)) /
      (√(2 * Real.pi) ^ 2 * (√(sig2 M) * √(ew2 M))) := ⟨_, rfl⟩
  obtain ⟨φSm, hφSmd⟩ : ∃ x : ℝ, x = Real.exp (-(1 / 2) * g ^ 2) / (√(2 * Real.pi) ^ 1 * √(sig2 M)) := ⟨_, rfl⟩
  obtain ⟨φSM, hφSMd⟩ : ∃ x : ℝ, x = 1 / (√(2 * Real.pi) ^ 1 * √(sig2 M)) := ⟨_, rfl⟩
  have hπ : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hσ := Real.sqrt_pos.mpr hs2
  have hse := Real.sqrt_pos.mpr he
  have hφXm : 0 < φXm := by rw [hφXmd]; positivity
  have hφYm : 0 < φYm := by rw [hφYmd]; positivity
  have hφSm : 0 < φSm := by rw [hφSmd]; positivity
  have hφSM : 0 < φSM := by rw [hφSMd]; positivity
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = 4 * A0 + 1 + |KK2 M| + |KK3 M| * g + CX / (4 * φXm) + CY / (2 * φYm) + CS / (1 * φSm) :=
    ⟨_, rfl⟩
  have q1 : 0 ≤ CX / (4 * φXm) := by positivity
  have q2 : 0 ≤ CY / (2 * φYm) := by positivity
  have q3 : 0 ≤ CS / (1 * φSm) := by positivity
  have q4 : 0 ≤ |KK3 M| * g := by positivity
  have q5 := abs_nonneg (KK2 M)
  have hA1 : 1 ≤ A := by rw [hAd]; linarith
  have hA : 0 ≤ A := by linarith
  obtain ⟨c0, hc0d⟩ : ∃ c : ℝ, c = φYm / (2 * A * φSM) := ⟨_, rfl⟩
  have hc0 : 0 < c0 := by rw [hc0d]; positivity
  refine ⟨4 * (A + 3 * A ^ 2 + 3 * A ^ 3) + 2 / c0, max 10 (⌈(4 * A) ^ 2⌉₊ + 1),
    fun m hm s u hz hu hsu => ?_⟩
  have hm10 : 10 ≤ m := le_trans (le_max_left _ _) hm
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
  obtain ⟨z, hzd⟩ : ∃ z : ℝ, z = zB M m s := ⟨_, rfl⟩
  rw [← hzd] at hz ⊢
  have hu' : |(u : ℝ) * h| ≤ M := by
    rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg (u : ℝ)]
  have hz2 : z ^ 2 ≤ g ^ 2 := by have := pow_le_pow_left₀ (abs_nonneg z) hz 2; rwa [sq_abs] at this
  have hu2 : ((u : ℝ) * h) ^ 2 ≤ (M : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hu' 2; rwa [sq_abs] at this
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb h z u h0.le h1 hz hu
  -- the three local expansions
  have eXb := hX m hm1 s u hsu
  have eYb := hY m hm1 s u hsu
  have eSb := hS m hm1 s
  rw [← hh, ← hzd] at eXb eYb eSb
  simp only [pow_one] at eXb eYb eSb
  obtain ⟨dX, LXe, hdX⟩ := rel_ex (A := A) hφXm (hφXmd ▸ phiX_lb hM hz2 hu2) (by norm_num : (0 : ℝ) < 4)
    (by positivity) eXb (by rw [hAd]; linarith) hCX
  obtain ⟨dY, LYe, hdY⟩ := rel_ex (A := A) hφYm (hφYmd ▸ phiY_lb hM hz2 hu2) (by norm_num : (0 : ℝ) < 2)
    (by positivity) eYb (by rw [hAd]; linarith) hCY
  obtain ⟨dS, LSe, hdS⟩ := rel_ex (A := A) hφSm (hφSmd ▸ phiS_lb hM hz2) (by norm_num : (0 : ℝ) < 1)
    (by positivity) eSb (by rw [hAd]; linarith) hCS
  have e1 : FXt1 M z u - 2 * FYt1 M z u + FSt1 M z 0 = 0 := by
    have := coef_e1 hM z u
    rw [show FSt1 M z u = FSt1 M z 0 from rfl] at this; linarith
  have hE := gen_cond (FXt1 M z u) (FXt2 M z u) (FXt3 M z u) (FXB M h z u) (FYt1 M z u) (FYt2 M z u)
    (FYt3 M z u) (FYB M h z u) (FSt1 M z 0) (FSt2 M z 0) (FSt3 M z 0) (FSB M h z 0) (KK2 M) (KK3 M * z) h
    e1 (coef_e2 hM z u) (coef_e3 hM z u)
  have hS1 : |FSt1 M z 0| ≤ A0 := by rw [show FSt1 M z 0 = 0 from rfl, abs_zero]; exact hA0
  have hS3 : |FSt3 M z 0| ≤ A0 := by rw [show FSt3 M z 0 = 0 from rfl, abs_zero]; exact hA0
  have hSB : |FSB M h z 0| ≤ A0 := by rw [show FSB M h z 0 = 0 from rfl, abs_zero]; exact hA0
  have hA4 : 4 * A0 + 1 ≤ A := by rw [hAd]; linarith
  have hYp := half_le_poly4 h0.le h1 b5 b6 b7 b8 hA4 hdY hhA
  have hSp := half_le_poly4 h0.le h1 hS1 b9 hS3 hSB hA4 hdS hhA
  have hφY := hφYmd ▸ phiY_lb hM hz2 hu2
  have hφS := hφSmd ▸ phiS_lb hM hz2
  have hφSle := hφSMd ▸ phiS_ub hM z
  have hφS0 := lt_of_lt_of_le hφSm hφS
  have hφY0 := lt_of_lt_of_le hφYm hφY
  have hLY := pos_of_eq3 (k := 2) hsm LYe (by norm_num) hφY0 (by linarith)
  have hLS := pos_of_eq3 (k := 1) hsm (by rw [pow_one]; exact LSe) (by norm_num) hφS0 (by linarith)
  have hite0 : (0 : ℝ) ≤ 1 + if u = 0 then 1 else 0 := by split_ifs <;> norm_num
  have hite2 : (1 + if u = 0 then 1 else 0 : ℝ) ≤ 2 := by split_ifs <;> norm_num
  exact cond_assemble (m := m) hm10 hh hA1 hc0d hφYm hφSM LXe LYe LSe (gauss_cancel hM z ((u : ℝ) * h))
    hφY hφS0 hφSle hE (bnd_poly4 h0.le h1 b1 b2 b3 b4 hA4) (bnd_poly4 h0.le h1 hS1 b9 hS3 hSB hA4)
    (bnd_poly4 h0.le h1 b5 b6 b7 b8 hA4) (bnd_K h0.le h1 hz (by rw [hAd]; linarith))
    (show |GC M h z u| ≤ A by linarith) hdX hdS hdY hYp hSp
    (ratio_laws hM m s u hLY.ne' hLS.ne') (lamB_laws hM m s u hLS.ne') hite0 hite2 (KK2_eq hM)
    (by rw [KK3_eq hM])

end ArcsAlgo.LLT
