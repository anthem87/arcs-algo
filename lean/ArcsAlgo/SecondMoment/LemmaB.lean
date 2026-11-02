module

public import ArcsAlgo.SecondMoment.Vectors
set_option autoImplicit false

/-!
# Lemma B for fixed `M` (paper §6.3), from [BR, §22]

`lemmaB_fixedM`: assuming the cited hypothesis `BR22`, for fixed `M ≥ 2` and `g`, uniformly in the
window `|s − mμ| ≤ gσ√m` and in `|u| ≤ M`, `u ≡ s (mod 2)`, with `λ = E[Z(u) | S_E = s]`:
`|λ/λ_m − 1| ≤ K/√m`, `E[Z² | S_E = s] ≤ λ²(1 + K/√m)` and `Pr(Z = 0 | S_E = s) ≤ K/√m`.

The proof is the one of Proposition B′ at first order: `E[Z²|S_E = s]/λ² = P_X P_w / P_Y²`, the
lattice indices `4·1/2²` and the Gaussian factors cancel exactly (`smA_mul_smB`), and the three
relative errors are `O(m^{−1/2})`. Chebyshev gives (3) (`p0B_le`). The constant `K` depends on `M`:
[BR, §22] is a theorem for a fixed law.
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

/-! ### The three local probabilities from [BR, §22] -/

/-- `Q₀ = (s − mμ)²/(mσ²)`. -/
noncomputable def smQ0 (M m : ℕ) (s : ℤ) : ℝ := ((s : ℝ) - m * muW M) ^ 2 / m / sig2 M

/-- `Q₁ = u²/(m Ew²)`. -/
noncomputable def smQ1 (M m : ℕ) (u : ℤ) : ℝ := (u : ℝ) ^ 2 / m / ew2 M

/-- The Gaussian term for `X = (w, εw, ε′w)`, lattice index 4. -/
noncomputable def smA (M m : ℕ) (s u : ℤ) : ℝ :=
  4 * (Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) /
    (√(2 * Real.pi) ^ 3 * √(sig2 M * ew2 M * ew2 M))) / √(m : ℝ) ^ 3

/-- The Gaussian term for `S_E`, lattice index 1. -/
noncomputable def smB (M m : ℕ) (s : ℤ) : ℝ :=
  Real.exp (-(1 / 2) * smQ0 M m s) / (√(2 * Real.pi) ^ 1 * √(sig2 M)) / √(m : ℝ) ^ 1

/-- The Gaussian term for `Y = (w, εw)`, lattice index 2. -/
noncomputable def smC (M m : ℕ) (s u : ℤ) : ℝ :=
  2 * (Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u)) /
    (√(2 * Real.pi) ^ 2 * √(sig2 M * ew2 M))) / √(m : ℝ) ^ 2

theorem sq_div_sqrt (x : ℝ) {m : ℝ} (hm : 0 ≤ m) : (x / √m) ^ 2 = x ^ 2 / m := by
  rw [div_pow, Real.sq_sqrt hm]

theorem br_X (hBR : BR22) {M : ℕ} (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
    ∀ s u : ℤ, (2 : ℤ) ∣ u - s →
      |lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiX M) m ![s, u, u] - smA M m s u| ≤ C / √(m : ℝ) ^ 4 := by
  have i0 : 0 < M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast i0
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool × Bool) 3 (fun _ => (1 / (4 * M) : ℝ)) (xiX M)
    (fun _ => by positivity) (by simp [Fintype.card_prod]; field_simp) (posDef_X hM)
    (⟨0, i0⟩, true, true) (by positivity)
  refine ⟨max C 0, le_max_right _ _, fun m hm s u hsu => ?_⟩
  have hmem : ![s, u, u] - m • xiX M (⟨0, i0⟩, true, true) ∈
      minLat (fun _ => (1 / (4 * M) : ℝ)) (xiX M) := by
    rw [minLat_X hM, mem_ker_parX]
    simp [xiX, sg]
    exact hsu
  have h := hC m hm _ hmem
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [minLat_X hM, index_parX, vcov_X (by omega), vmean_X (by omega),
    gaussDens_diag _ (fun i => by fin_cases i <;> simp [hs2, he])] at h
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sq_div_sqrt _ hm0.le] at h
  have e0 : ((s : ℝ) - m * (((M : ℝ) + 1) / 2)) ^ 2 / m / sig2 M = smQ0 M m s := by
    rw [smQ0, muW]
  have e1 : ((u : ℝ) - m * 0) ^ 2 / m / ew2 M = smQ1 M m u := by
    rw [smQ1, mul_zero, sub_zero]
  rw [e0, e1] at h
  push_cast at h
  rw [← smA] at h
  refine h.trans ?_
  gcongr
  exact le_max_left _ _

theorem br_Y (hBR : BR22) {M : ℕ} (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
    ∀ s u : ℤ, (2 : ℤ) ∣ u - s →
      |lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] - smC M m s u| ≤ C / √(m : ℝ) ^ 3 := by
  have i0 : 0 < M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast i0
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  obtain ⟨C, hC⟩ := hBR (Fin M × Bool) 2 (fun _ => (1 / (2 * M) : ℝ)) (xiY M)
    (fun _ => by positivity) (by simp [Fintype.card_prod]; field_simp) (posDef_Y hM)
    (⟨0, i0⟩, true) (by positivity)
  refine ⟨max C 0, le_max_right _ _, fun m hm s u hsu => ?_⟩
  have hmem : ![s, u] - m • xiY M (⟨0, i0⟩, true) ∈
      minLat (fun _ => (1 / (2 * M) : ℝ)) (xiY M) := by
    rw [minLat_Y hM, mem_ker_parY]
    simp [xiY, sg]
    exact hsu
  have h := hC m hm _ hmem
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [minLat_Y hM, index_parY, vcov_Y (by omega), vmean_Y (by omega),
    gaussDens_diag _ (fun i => by fin_cases i <;> simp [hs2, he])] at h
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sq_div_sqrt _ hm0.le] at h
  have e0 : ((s : ℝ) - m * (((M : ℝ) + 1) / 2)) ^ 2 / m / sig2 M = smQ0 M m s := by
    rw [smQ0, muW]
  have e1 : ((u : ℝ) - m * 0) ^ 2 / m / ew2 M = smQ1 M m u := by
    rw [smQ1, mul_zero, sub_zero]
  rw [e0, e1] at h
  push_cast at h
  rw [← smC] at h
  refine h.trans ?_
  gcongr
  exact le_max_left _ _

theorem br_1 (hBR : BR22) {M : ℕ} (hM : 2 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
    ∀ s : ℤ,
      |lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] - smB M m s| ≤ C / √(m : ℝ) ^ 2 := by
  have i0 : 0 < M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast i0
  have hs2 := sig2_pos' hM
  have he := ew2_pos M
  obtain ⟨C, hC⟩ := hBR (Fin M) 1 (fun _ => (1 / M : ℝ)) (xi1 M)
    (fun _ => by positivity) (by simp [Fintype.card_prod]; field_simp) (posDef_1 hM)
    ⟨0, i0⟩ (by positivity)
  refine ⟨max C 0, le_max_right _ _, fun m hm s => ?_⟩
  have hmem : ![s] - m • xi1 M ⟨0, i0⟩ ∈
      minLat (fun _ => (1 / M : ℝ)) (xi1 M) := by
    rw [minLat_1 hM]; exact AddSubgroup.mem_top _
  have h := hC m hm _ hmem
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [minLat_1 hM, AddSubgroup.index_top, vcov_1 (by omega), vmean_1 (by omega),
    gaussDens_diag _ (fun i => by fin_cases i <;> simp [hs2, he])] at h
  simp only [Fin.sum_univ_one, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sq_div_sqrt _ hm0.le] at h
  have e0 : ((s : ℝ) - m * (((M : ℝ) + 1) / 2)) ^ 2 / m / sig2 M = smQ0 M m s := by
    rw [smQ0, muW]
  rw [e0] at h
  push_cast at h
  rw [one_mul, ← smB] at h
  refine h.trans ?_
  gcongr
  exact le_max_left _ _

/-! ### Lemma B, for fixed `M` -/

/-- `#{w : S_E = s}`. -/
def cntS (M m : ℕ) (s : ℤ) : ℕ := (univ.filter fun w : Fin m → Fin M => Sw w = s).card

/-- `λ = E[Z(u) | S_E = s]`. -/
noncomputable def lamB (M m : ℕ) (s u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ)) / cntS M m s

/-- `E[Z(u)² | S_E = s]`. -/
noncomputable def m2B (M m : ℕ) (s u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2) / cntS M m s

/-- `Pr(Z(u) = 0 | S_E = s)`. -/
noncomputable def p0B (M m : ℕ) (s u : ℤ) : ℝ :=
  ((univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card : ℝ) / cntS M m s

/-- `c_M = 1/3 + 1/(2M) + 1/(6M²)`, so that `M² c_M = Ew²`. -/
noncomputable def cMB (M : ℕ) : ℝ := 1 / 3 + 1 / (2 * M) + 1 / (6 * (M : ℝ) ^ 2)

/-- `λ_m = 2^{m+1}/(M √(2π m c_M))`. -/
noncomputable def lamM (M m : ℕ) : ℝ := 2 ^ (m + 1) / (M * √(2 * Real.pi * m * cMB M))

theorem law1_eq (M m : ℕ) (s : ℤ) :
    lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] = (1 / M : ℝ) ^ m * cntS M m s := by
  rw [lawPow_const, card_1]; rfl

theorem lawY_eq (M m : ℕ) (s u : ℤ) :
    lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] = (1 / (2 * M) : ℝ) ^ m *
      ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) := by
  rw [lawPow_const, card_Y]; push_cast; rfl

theorem lawX_eq (M m : ℕ) (s u : ℤ) :
    lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiX M) m ![s, u, u] = (1 / (4 * M) : ℝ) ^ m *
      ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2 := by
  rw [lawPow_const, card_X]; push_cast; rfl

/-- The lattice indices and the Gaussian factors cancel: `A·B = C²`. -/
theorem smA_mul_smB {M : ℕ} (hM : 2 ≤ M) (m : ℕ) (s u : ℤ) :
    smA M m s u * smB M m s = smC M m s u ^ 2 := by
  have hσ := sig2_pos' hM
  have he := ew2_pos M
  have h1 : √(sig2 M * ew2 M * ew2 M) = √(sig2 M) * ew2 M := by
    rw [mul_assoc, Real.sqrt_mul hσ.le, Real.sqrt_mul_self he.le]
  have h2 : √(sig2 M * ew2 M) = √(sig2 M) * √(ew2 M) := Real.sqrt_mul hσ.le _
  have hexp : Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) *
      Real.exp (-(1 / 2) * smQ0 M m s) = Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u)) ^ 2 := by
    rw [← Real.exp_add, sq, ← Real.exp_add]; ring_nf
  have hse : √(ew2 M) ^ 2 = ew2 M := Real.sq_sqrt he.le
  have hss : √(sig2 M) ^ 2 = sig2 M := Real.sq_sqrt hσ.le
  have hm : √(m : ℝ) ^ 4 = √(m : ℝ) ^ 3 * √(m : ℝ) ^ 1 := by ring
  unfold smA smB smC
  rw [h1, h2]
  calc 4 * (Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) /
        (√(2 * Real.pi) ^ 3 * (√(sig2 M) * ew2 M))) / √(m : ℝ) ^ 3 *
        (Real.exp (-(1 / 2) * smQ0 M m s) / (√(2 * Real.pi) ^ 1 * √(sig2 M)) / √(m : ℝ) ^ 1)
      = 4 * (Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) *
        Real.exp (-(1 / 2) * smQ0 M m s)) /
        (√(2 * Real.pi) ^ 4 * (√(sig2 M) ^ 2 * ew2 M) * (√(m : ℝ) ^ 3 * √(m : ℝ) ^ 1)) := by
          field_simp
    _ = _ := by
      rw [hexp, hss, ← hm]
      field_simp
      simp only [hse, hss]
      ring

/-- `2^m C/B = λ_m e^{−Q₁/2}`. -/
theorem smC_div_smB {M : ℕ} (hM : 2 ≤ M) {m : ℕ} (hm : 1 ≤ m) (s u : ℤ) :
    2 ^ m * smC M m s u / smB M m s = lamM M m * Real.exp (-(1 / 2) * smQ1 M m u) := by
  have hσ := sig2_pos' hM
  have he := ew2_pos M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (M : ℝ) * √(2 * Real.pi * m * cMB M) = √(2 * Real.pi) * √(ew2 M) * √(m : ℝ) := by
    have : (M : ℝ) ^ 2 * cMB M = ew2 M := by unfold cMB ew2; field_simp; ring
    have hcM : 0 < cMB M := by unfold cMB; positivity
    calc (M : ℝ) * √(2 * Real.pi * m * cMB M) = √((M : ℝ) ^ 2) * √(2 * Real.pi * m * cMB M) := by
          rw [Real.sqrt_sq hM0.le]
      _ = √((M : ℝ) ^ 2 * (2 * Real.pi * m * cMB M)) := (Real.sqrt_mul (by positivity) _).symm
      _ = √(2 * Real.pi * ew2 M * m) := by congr 1; rw [← this]; ring
      _ = √(2 * Real.pi) * √(ew2 M) * √(m : ℝ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hexp : Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u)) =
      Real.exp (-(1 / 2) * smQ0 M m s) * Real.exp (-(1 / 2) * smQ1 M m u) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : √(sig2 M * ew2 M) = √(sig2 M) * √(ew2 M) := Real.sqrt_mul hσ.le _
  have hpi : √(2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hmm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  unfold lamM smC smB
  rw [hc, hexp, h2, pow_succ]
  have := Real.exp_pos (-(1 / 2) * smQ0 M m s)
  have := Real.sqrt_pos.mpr hσ
  have := Real.sqrt_pos.mpr he
  have := Real.sqrt_pos.mpr hm0
  have : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

/-- A relative error from an absolute one. -/
theorem rel_err {a A C α t : ℝ} {k : ℕ} (ht : 0 < t) (hα : 0 < α) (hA : α / t ^ k ≤ A)
    (h : |a - A| ≤ C / t ^ (k + 1)) (hC : 0 ≤ C) : |a - A| ≤ C / α / t * A := by
  refine h.trans ?_
  calc C / t ^ (k + 1) = C / α / t * (α / t ^ k) := by field_simp; ring
    _ ≤ C / α / t * A := by gcongr

/-- Chebyshev, in counting form. -/
theorem p0B_le {M m : ℕ} {s u : ℤ} (hlam : 0 < lamB M m s u) :
    p0B M m s u ≤ m2B M m s u / lamB M m s u ^ 2 - 1 := by
  set F := univ.filter (fun w : Fin m → Fin M => Sw w = s)
  set lam := lamB M m s u
  have hF : (0 : ℝ) < cntS M m s := by
    by_contra h
    have h0 : (cntS M m s : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    have : lam = 0 := by simp only [lam, lamB, h0, div_zero]
    linarith
  have hsum : ∑ w ∈ F, (Zc w u : ℝ) = lam * cntS M m s := by
    simp only [lam, lamB]; field_simp; rfl
  have hsum2 : ∑ w ∈ F, (Zc w u : ℝ) ^ 2 = m2B M m s u * cntS M m s := by
    simp only [m2B]; field_simp; rfl
  have hvar : ∑ w ∈ F, ((Zc w u : ℝ) - lam) ^ 2 =
      (m2B M m s u - lam ^ 2) * cntS M m s := by
    have : ∀ w ∈ F, ((Zc w u : ℝ) - lam) ^ 2 = (Zc w u : ℝ) ^ 2 - 2 * lam * (Zc w u : ℝ) + lam ^ 2 :=
      fun _ _ => by ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum, hsum2]
    simp [cntS, F]; ring
  have hcheb : lam ^ 2 * ((univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0).card : ℝ) ≤
      ∑ w ∈ F, ((Zc w u : ℝ) - lam) ^ 2 := by
    have hsub : (univ.filter fun w : Fin m → Fin M => Sw w = s ∧ Zc w u = 0) =
        F.filter (fun w => Zc w u = 0) := by
      ext w; simp [F]
    rw [hsub, mul_comm, ← nsmul_eq_mul, ← sum_const]
    calc ∑ _w ∈ F.filter (fun w => Zc w u = 0), lam ^ 2
        = ∑ w ∈ F.filter (fun w => Zc w u = 0), ((Zc w u : ℝ) - lam) ^ 2 :=
          sum_congr rfl fun w hw => by rw [(mem_filter.mp hw).2]; simp
      _ ≤ ∑ w ∈ F, ((Zc w u : ℝ) - lam) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  rw [hvar] at hcheb
  unfold p0B
  rw [div_le_iff₀ hF]
  have hlam2 : 0 < lam ^ 2 := by positivity
  have : m2B M m s u / lam ^ 2 - 1 = (m2B M m s u - lam ^ 2) / lam ^ 2 := by field_simp
  rw [this, div_mul_eq_mul_div, le_div_iff₀ hlam2]
  linarith

/-- The window gives `Q₀ ≤ g²`. -/
theorem smQ0_le {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} {s : ℤ}
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) : smQ0 M m s ≤ g ^ 2 := by
  have hσ := sig2_pos' hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : ((s : ℝ) - m * muW M) ^ 2 ≤ g ^ 2 * sig2 M * m := by
    have := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs] at this
    calc _ ≤ _ := this
      _ = g ^ 2 * sig2 M * m := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hm0.le]
  unfold smQ0
  rw [div_div, div_le_iff₀ (by positivity)]
  linarith

theorem smQ1_le {M m : ℕ} (hm : 1 ≤ m) {u : ℤ} (hu : |u| ≤ M) :
    smQ1 M m u ≤ (M : ℝ) ^ 2 / ew2 M / m := by
  have he := ew2_pos M
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
  have : (u : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu' 2
  unfold smQ1
  rw [div_div, div_div, mul_comm (ew2 M)]
  exact div_le_div_of_nonneg_right this (by positivity)

/-- Lower bounds for the three Gaussian terms in the window. -/
theorem smABC_low {M : ℕ} (hM : 2 ≤ M) (g : ℝ) : ∃ αA αB αC : ℝ, 0 < αA ∧ 0 < αB ∧ 0 < αC ∧
    ∀ m : ℕ, 1 ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      αA / √(m : ℝ) ^ 3 ≤ smA M m s u ∧ αB / √(m : ℝ) ^ 1 ≤ smB M m s ∧
        αC / √(m : ℝ) ^ 2 ≤ smC M m s u := by
  have hσ := sig2_pos' hM
  have he := ew2_pos M
  have hq1p : 0 ≤ (M : ℝ) ^ 2 / ew2 M := by positivity
  refine ⟨4 * (Real.exp (-(1 / 2) * (g ^ 2 + (M : ℝ) ^ 2 / ew2 M + (M : ℝ) ^ 2 / ew2 M)) /
    (√(2 * Real.pi) ^ 3 * √(sig2 M * ew2 M * ew2 M))),
    Real.exp (-(1 / 2) * g ^ 2) / (√(2 * Real.pi) ^ 1 * √(sig2 M)),
    2 * (Real.exp (-(1 / 2) * (g ^ 2 + (M : ℝ) ^ 2 / ew2 M)) /
    (√(2 * Real.pi) ^ 2 * √(sig2 M * ew2 M))), by positivity, by positivity, by positivity,
    fun m hm1 s u hw hu => ?_⟩
  have hQ0 := smQ0_le hM hm1 hw
  have hQ1 := (smQ1_le (M := M) hm1 hu).trans (div_le_self hq1p (by exact_mod_cast hm1))
  have eA : Real.exp (-(1 / 2) * (g ^ 2 + (M : ℝ) ^ 2 / ew2 M + (M : ℝ) ^ 2 / ew2 M)) ≤
      Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u + smQ1 M m u)) :=
    Real.exp_le_exp.mpr (by linarith)
  have eB : Real.exp (-(1 / 2) * g ^ 2) ≤ Real.exp (-(1 / 2) * smQ0 M m s) :=
    Real.exp_le_exp.mpr (by linarith)
  have eC : Real.exp (-(1 / 2) * (g ^ 2 + (M : ℝ) ^ 2 / ew2 M)) ≤
      Real.exp (-(1 / 2) * (smQ0 M m s + smQ1 M m u)) :=
    Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right eA (by positivity)) (by norm_num)) (by positivity)
  · exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right eB (by positivity)) (by positivity)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right eC (by positivity)) (by norm_num)) (by positivity)

/-- The second-moment ratio: `ab ≤ c²(1 + 16ε)` from relative errors `ε ≤ 1/2` and `AB = C²`. -/
theorem ratio_two {a b c A B C ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hAB : A * B = C ^ 2) (ha : a ≤ (1 + ε) * A) (hb : b ≤ (1 + ε) * B)
    (hb0 : 0 ≤ b) (hc : (1 - ε) * C ≤ c) : a * b ≤ c ^ 2 * (1 + 16 * ε) := by
  have hpoly : (1 + ε) ^ 2 ≤ (1 - ε) ^ 2 * (1 + 16 * ε) := by
    have : 0 ≤ ε * (1 - 2 * ε) * (3 - 2 * ε) :=
      mul_nonneg (mul_nonneg hε0 (by linarith)) (by linarith)
    nlinarith
  have hc1' : 0 ≤ (1 - ε) * C := mul_nonneg (by linarith) hC.le
  calc a * b ≤ ((1 + ε) * A) * ((1 + ε) * B) :=
        mul_le_mul ha hb hb0 (mul_nonneg (by linarith) hA.le)
    _ = (1 + ε) ^ 2 * C ^ 2 := by rw [← hAB]; ring
    _ ≤ (1 - ε) ^ 2 * (1 + 16 * ε) * C ^ 2 := by gcongr
    _ = ((1 - ε) * C) ^ 2 * (1 + 16 * ε) := by ring
    _ ≤ c ^ 2 * (1 + 16 * ε) := by gcongr

/-- The first-moment ratio: `|x c B/(b C) − 1| ≤ 4ε`. -/
theorem ratio_one {x b c B C ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hB : 0 < B) (hC : 0 < C)
    (hx1 : x ≤ 1) (hx2 : 1 - ε ≤ x) (hb1 : (1 - ε) * B ≤ b) (hb2 : b ≤ (1 + ε) * B)
    (hc1 : (1 - ε) * C ≤ c) (hc2 : c ≤ (1 + ε) * C) :
    |x * (c * B) / (b * C) - 1| ≤ 4 * ε := by
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos (by linarith) hB) hb1
  have hbC : 0 < b * C := mul_pos hb0 hC
  have hP : 0 < C * B := mul_pos hC hB
  have hx0 : 0 ≤ x := by linarith
  have hc0 : 0 ≤ c := le_trans (mul_nonneg (by linarith) hC.le) hc1
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hbC]
    have h1 : (1 - ε) * ((1 - ε) * C) ≤ x * c :=
      mul_le_mul hx2 hc1 (mul_nonneg (by linarith) hC.le) hx0
    have h2 : (1 - ε) * ((1 - ε) * C) * B ≤ x * c * B := mul_le_mul_of_nonneg_right h1 hB.le
    have h3 : (1 - 4 * ε) * (b * C) ≤ (1 - ε) * ((1 - ε) * C) * B := by
      rcases le_or_gt (1 - 4 * ε) 0 with h | h
      · have := mul_nonpos_of_nonpos_of_nonneg h hbC.le
        have : 0 ≤ (1 - ε) * ((1 - ε) * C) * B :=
          mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (by linarith) hC.le)) hB.le
        linarith
      · have h4 : (1 - 4 * ε) * (b * C) ≤ (1 - 4 * ε) * ((1 + ε) * B * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb2 hC.le) h.le
        have h5 : (1 - 4 * ε) * ((1 + ε) * B * C) ≤ (1 - ε) * ((1 - ε) * C) * B := by
          nlinarith [mul_nonneg (by positivity : 0 ≤ ε + 5 * ε ^ 2) hP.le]
        linarith
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hbC]
    have h1 : x * (c * B) ≤ 1 * (c * B) := mul_le_mul_of_nonneg_right hx1 (mul_nonneg hc0 hB.le)
    have h1' : c * B ≤ (1 + ε) * C * B := mul_le_mul_of_nonneg_right hc2 hB.le
    have h2 : (1 - ε) * B * C ≤ b * C := mul_le_mul_of_nonneg_right hb1 hC.le
    have h3 : (4 * ε + 1) * ((1 - ε) * B * C) ≤ (4 * ε + 1) * (b * C) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : (1 + ε) * C * B ≤ (4 * ε + 1) * ((1 - ε) * B * C) := by
      nlinarith [mul_nonneg (mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)) hP.le]
    linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma B for fixed `M`** (paper §6.3), from the local expansion [BR, §22] (`BR22`), applied
to the lattice vectors `Y = (w, εw)` (index 2), `X = (w, εw, ε′w)` (index 4) and `w` (index 1)
whose hypotheses are verified above. With `λ = E[Z(u) | S_E = s]`, uniformly in the window
`|s − mμ| ≤ gσ√m` and in `|u| ≤ M`, `u ≡ s (mod 2)`:
(1) `|λ/λ_m − 1| ≤ K/√m`; (2) `E[Z² | S_E = s] ≤ λ²(1 + K/√m)`;
(3) `Pr(Z = 0 | S_E = s) ≤ K/√m`. The constant `K` depends on `M` and `g`. -/
theorem lemmaB_fixedM (hBR : BR22) {M : ℕ} (hM : 2 ≤ M) (g : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      0 < lamB M m s u ∧ |lamB M m s u / lamM M m - 1| ≤ K / √(m : ℝ) ∧
      m2B M m s u ≤ lamB M m s u ^ 2 * (1 + K / √(m : ℝ)) ∧ p0B M m s u ≤ K / √(m : ℝ) := by
  obtain ⟨CX, hCX, hX⟩ := br_X hBR hM
  obtain ⟨CY, hCY, hY⟩ := br_Y hBR hM
  obtain ⟨C1, hC1, h1⟩ := br_1 hBR hM
  obtain ⟨αA, αB, αC, hαA, hαB, hαC, hlow⟩ := smABC_low hM g
  have he := ew2_pos M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hq1p : 0 ≤ (M : ℝ) ^ 2 / ew2 M := by positivity
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀, K₀ = CX / αA + C1 / αB + CY / αC + (M : ℝ) ^ 2 / ew2 M := ⟨_, rfl⟩
  have dX : CX / αA ≤ K₀ := by
    rw [hK₀def]; linarith [div_nonneg hC1 hαB.le, div_nonneg hCY hαC.le]
  have dB : C1 / αB ≤ K₀ := by
    rw [hK₀def]; linarith [div_nonneg hCX hαA.le, div_nonneg hCY hαC.le]
  have dC : CY / αC ≤ K₀ := by
    rw [hK₀def]; linarith [div_nonneg hC1 hαB.le, div_nonneg hCX hαA.le]
  have dq : (M : ℝ) ^ 2 / ew2 M ≤ K₀ := by
    rw [hK₀def]; linarith [div_nonneg hC1 hαB.le, div_nonneg hCX hαA.le, div_nonneg hCY hαC.le]
  have hK₀ : 0 ≤ K₀ := hq1p.trans dq
  refine ⟨16 * K₀, by positivity, ⌈4 * K₀ ^ 2⌉₊ + 1, fun m hm s u hw hu hsu => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have ht : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hK2 : 2 * K₀ ≤ √(m : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have : (⌈4 * K₀ ^ 2⌉₊ : ℝ) ≤ m := by exact_mod_cast (by omega : ⌈4 * K₀ ^ 2⌉₊ ≤ m)
    nlinarith [Nat.le_ceil (4 * K₀ ^ 2)]
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = K₀ / √(m : ℝ) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hε : ε ≤ 1 / 2 := by rw [hεdef, div_le_iff₀ ht]; linarith
  have hK : 16 * K₀ / √(m : ℝ) = 16 * ε := by rw [hεdef]; ring
  rw [hK]
  obtain ⟨hA, hB, hC⟩ := hlow m hm1 s u hw hu
  have hA0 : 0 < smA M m s u := lt_of_lt_of_le (by positivity) hA
  have hB0 : 0 < smB M m s := lt_of_lt_of_le (by positivity) hB
  have hC0 : 0 < smC M m s u := lt_of_lt_of_le (by positivity) hC
  -- relative errors
  have hrel : ∀ {C α : ℝ}, C / α ≤ K₀ → C / α / √(m : ℝ) ≤ ε := fun h => by
    rw [hεdef]; exact div_le_div_of_nonneg_right h ht.le
  have ra := (rel_err ht hαA hA (hX m hm1 s u hsu) hCX).trans
    (mul_le_mul_of_nonneg_right (hrel dX) hA0.le)
  have rb := (rel_err ht hαB hB (h1 m hm1 s) hC1).trans
    (mul_le_mul_of_nonneg_right (hrel dB) hB0.le)
  have rc := (rel_err ht hαC hC (hY m hm1 s u hsu) hCY).trans
    (mul_le_mul_of_nonneg_right (hrel dC) hC0.le)
  obtain ⟨ra1, ra2⟩ := abs_le.mp ra
  obtain ⟨rb1, rb2⟩ := abs_le.mp rb
  obtain ⟨rc1, rc2⟩ := abs_le.mp rc
  have hpow : ∀ k : ℝ, 0 < k → k ^ m * (1 / k) ^ m = 1 := fun k hk => by
    rw [← mul_pow, mul_one_div_cancel hk.ne', one_pow]
  have hcnt : (cntS M m s : ℝ) = (M : ℝ) ^ m * lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] := by
    rw [law1_eq, ← mul_assoc, hpow _ hM0, one_mul]
  have hSZ : ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) =
      (2 * M : ℝ) ^ m * lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] := by
    rw [lawY_eq, ← mul_assoc, hpow _ (by positivity), one_mul]
  have hSZ2 : ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), (Zc w u : ℝ) ^ 2 =
      (4 * M : ℝ) ^ m * lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiX M) m ![s, u, u] := by
    rw [lawX_eq, ← mul_assoc, hpow _ (by positivity), one_mul]
  generalize lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiX M) m ![s, u, u] = a at ra1 ra2 hSZ2
  generalize lawPow (fun _ => (1 / M : ℝ)) (xi1 M) m ![s] = b at rb1 rb2 hcnt
  generalize lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiY M) m ![s, u] = c at rc1 rc2 hSZ
  have hb0 : 0 < b := by nlinarith
  have hc0 : 0 < c := by nlinarith
  have hMm : (0 : ℝ) < (M : ℝ) ^ m := by positivity
  have hlam : lamB M m s u = 2 ^ m * c / b := by
    unfold lamB; rw [hSZ, hcnt, mul_pow]; field_simp
  have hm2 : m2B M m s u = 4 ^ m * a / b := by
    unfold m2B; rw [hSZ2, hcnt, mul_pow]; field_simp
  have hlam0 : 0 < lamB M m s u := by rw [hlam]; positivity
  have hab := ratio_two (a := a) (b := b) (c := c) hε0 hε hA0 hB0 hC0 (smA_mul_smB hM m s u) (by linarith) (by linarith)
    hb0.le (by linarith)
  have h2 : m2B M m s u ≤ lamB M m s u ^ 2 * (1 + 16 * ε) := by
    have e4 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hm2, hlam, div_pow, mul_pow, e4]
    have h4 : (0 : ℝ) < 4 ^ m := by positivity
    calc 4 ^ m * a / b = 4 ^ m * (a * b) / b ^ 2 := by field_simp
      _ ≤ 4 ^ m * (c ^ 2 * (1 + 16 * ε)) / b ^ 2 := by gcongr
      _ = 4 ^ m * c ^ 2 / b ^ 2 * (1 + 16 * ε) := by ring
  refine ⟨hlam0, ?_, h2, ?_⟩
  · have hx := smC_div_smB hM hm1 s u
    have hQ1 := (smQ1_le (M := M) hm1 hu)
    have hsqm : √(m : ℝ) ≤ m := by
      have h1m : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have := Real.sqrt_le_sqrt (show (m : ℝ) ≤ m * m by nlinarith)
      rwa [Real.sqrt_mul_self hm0.le] at this
    have hQ1ε : smQ1 M m u ≤ ε := by
      calc smQ1 M m u ≤ (M : ℝ) ^ 2 / ew2 M / m := hQ1
        _ ≤ (M : ℝ) ^ 2 / ew2 M / √(m : ℝ) := div_le_div_of_nonneg_left hq1p ht hsqm
        _ ≤ ε := by rw [hεdef]; exact div_le_div_of_nonneg_right dq ht.le
    have hQ1p : 0 ≤ smQ1 M m u := by unfold smQ1; positivity
    have hx1 : Real.exp (-(1 / 2) * smQ1 M m u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hx2 : 1 - ε ≤ Real.exp (-(1 / 2) * smQ1 M m u) := by
      have := Real.add_one_le_exp (-(1 / 2) * smQ1 M m u)
      linarith
    have hlM : 0 < lamM M m := by unfold lamM cMB; positivity
    have hexp0 := Real.exp_pos (-(1 / 2) * smQ1 M m u)
    have hratio : lamB M m s u / lamM M m =
        Real.exp (-(1 / 2) * smQ1 M m u) * (c * smB M m s) / (b * smC M m s u) := by
      have : lamM M m = 2 ^ m * smC M m s u / smB M m s / Real.exp (-(1 / 2) * smQ1 M m u) := by
        rw [hx]; field_simp
      rw [hlam, this]; field_simp
    rw [hratio]
    refine (ratio_one hε0 hε hB0 hC0 hx1 hx2 (by linarith) (by linarith) (by linarith)
      (by linarith)).trans (by linarith)
  · refine (p0B_le hlam0).trans ?_
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    linarith

end ArcsAlgo.LLT
