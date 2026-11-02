module

public import ArcsAlgo.Uniform.Typ2
public import ArcsAlgo.Uniform.Sum1
set_option autoImplicit false

/-!
# Typical pairs (paper §6.3, proof of Lemma B(2))

`pair_typ`: for `|x|, |y|, |x △ y|` within `T` of `m/2`, `16T ≤ m`, `m ≥ 32`, uniformly in
`M ≥ 2` and in the window `|s − mμ| ≤ gσ√m`, `|u| ≤ M`,
`Pr(S_x = S_y = a, S_E = s) g_m(s) ≤ F(g, m, T) G(x) G(y) + E(M, m) g_m(s)`,
with `G(x) = g_{|x|}(a) g_{m−|x|}(s − a)`,
`F = (1 + 13/√m)(1 + 64T²/m²) e^{64T(2 + (4 + g)T)²/m²}` (`FacB`) and
`E = 3162/(σ³(m/16)^{5/2})` (`ErrB`, from Lemma B0′ in the four classes).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- The Gaussian of `Pr(S_x = a, S_{E∖x} = s − a)`. -/
noncomputable def Rg (M m : ℕ) {n : ℕ} (x : Finset (Fin n)) (a s : ℤ) : ℝ :=
  gaussB M x.card a * gaussB M (m - x.card) (s - a)

/-- The factor of the pointwise comparison for typical pairs. -/
noncomputable def FacB (g : ℝ) (m T : ℕ) : ℝ :=
  (1 + 13 / √(m : ℝ)) * (1 + 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2) *
    exp (64 * T * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2)

/-- The error of Lemma B0′ in the four classes, with classes of size `≥ m/16`. -/
noncomputable def ErrB (M m : ℕ) : ℝ :=
  3162 / (√(sig2 M) ^ 3 * (((m : ℝ) / 16) ^ 2 * √((m : ℝ) / 16)))

theorem sqrt_sig_ge {M : ℕ} (hM : 2 ≤ M) : (M : ℝ) ≤ 4 * √(sig2 M) ∧ muW M ≤ 4 * √(sig2 M) := by
  have hσ := sig2_pos hM
  have h1 := M_sq_le hM
  have h2 := muW_sq_le hM
  have hs := Real.sq_sqrt hσ.le
  have hs0 := Real.sqrt_nonneg (sig2 M)
  have hμ : 0 ≤ muW M := by unfold muW; positivity
  constructor <;> nlinarith [sq_nonneg ((M : ℝ) - 4 * √(sig2 M)), sq_nonneg (muW M - 4 * √(sig2 M))]

/-- `|a − ks/m| ≤ σ(2 + (4 + g)T)` for `|k − m/2| ≤ T` in the window. -/
theorem a_dev {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m) {g : ℝ} (hg : 0 ≤ g) {s u a : ℤ}
    (ha : 2 * a = s + u) (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M)
    {k T : ℝ} (hT : 0 ≤ T) (hk : |k - m / 2| ≤ T) :
    |(a : ℝ) - k * s / m| ≤ √(sig2 M) * (2 + (4 + g) * T) := by
  obtain ⟨hMσ, hμσ⟩ := sqrt_sig_ge hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hσ0 := Real.sqrt_nonneg (sig2 M)
  have ha' : (a : ℝ) = ((s : ℝ) + u) / 2 := by
    have : ((2 * a : ℤ) : ℝ) = ((s + u : ℤ) : ℝ) := by rw [ha]
    push_cast at this; linarith
  have e : (a : ℝ) - k * s / m = u / 2 - (k - m / 2) * (s / m) := by
    rw [ha']; field_simp; ring
  have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
  have hsm : √(m : ℝ) ≤ m := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hs : |(s : ℝ) / m| ≤ √(sig2 M) * (4 + g) := by
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    have h1 : |(s : ℝ)| ≤ m * muW M + g * √(sig2 M) * √(m : ℝ) := by
      have := abs_sub_abs_le_abs_sub (s : ℝ) (m * muW M)
      have hμ : 0 ≤ muW M := by unfold muW; positivity
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ m * muW M)] at this
      linarith
    have h2 : g * √(sig2 M) * √(m : ℝ) ≤ g * √(sig2 M) * m := by gcongr
    nlinarith
  rw [e]
  calc |(u : ℝ) / 2 - (k - m / 2) * (s / m)| ≤ |(u : ℝ) / 2| + |(k - m / 2) * (s / m)| := abs_sub _ _
    _ ≤ (4 * √(sig2 M)) / 2 + T * (√(sig2 M) * (4 + g)) := by
        rw [abs_div, abs_two, abs_mul]
        gcongr
        · linarith
    _ = √(sig2 M) * (2 + (4 + g) * T) := by ring

theorem w_factor {W σ2 m : ℝ} (hm : 0 < m) (hσ4 : 1 / 4 ≤ σ2) (hW : σ2 * (m / 16) / 4 ≤ W) :
    2 / √(2 * π * W) ≤ 13 / √m := by
  have h16 : (0 : ℝ) ≤ m / 16 := by linarith
  have hW' : m / 256 ≤ W := by
    have := mul_le_mul_of_nonneg_right hσ4 h16
    linarith
  have hπ : 2.5 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d2]
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  have h256 : √(256 : ℝ) = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : √(2 * π) * √m / 16 ≤ √(2 * π * W) := by
    calc √(2 * π) * √m / 16 = √(2 * π) * (√m / √256) := by rw [h256]; ring
      _ = √(2 * π) * √(m / 256) := by rw [Real.sqrt_div' _ (by norm_num)]
      _ = √(2 * π * (m / 256)) := (Real.sqrt_mul (by positivity) _).symm
      _ ≤ √(2 * π * W) := Real.sqrt_le_sqrt (by gcongr)
  calc 2 / √(2 * π * W) ≤ 2 / (√(2 * π) * √m / 16) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
    _ = 32 / (√(2 * π) * √m) := by field_simp; ring
    _ ≤ 13 / √m := by
        rw [div_le_div_iff₀ (by positivity) hsm]; nlinarith

set_option maxHeartbeats 2000000 in
/-- **Typical pairs** (paper §6.3, proof of Lemma B(2)): for `|x|, |y|, |x △ y|` within `T` of
`m/2`, `16T ≤ m`, `m ≥ 32`, uniformly in `M ≥ 2` and in the window,
`Pr(S_x = S_y = a, S_E = s) g_m(s) ≤ F(g, m, T) G(x) G(y) + E(M, m) g_m(s)`, where
`G(x) = g_{|x|}(a) g_{m−|x|}(s − a)`, `F → 1` and `E = O(σ⁻³m^{−5/2})` comes from Lemma B0′. -/
theorem pair_typ {M m T : ℕ} (hM : 2 ≤ M) (hm : 32 ≤ m) (hTm : 16 * T ≤ m) {g : ℝ} (hg : 0 ≤ g)
    {s u a : ℤ} (ha : 2 * a = s + u) (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ))
    (hu : |u| ≤ M) {x y : Finset (Fin m)} (hx : |(x.card : ℝ) - m / 2| ≤ T)
    (hy : |(y.card : ℝ) - m / 2| ≤ T) (hxy : |((x \ y).card + (y \ x).card : ℝ) - m / 2| ≤ T) :
    pairP M m x y a s * gaussB M m s ≤
      FacB g m T * (Rg M m x a s * Rg M m y a s) + ErrB M m * gaussB M m s := by
  have hσ := sig2_pos hM
  have hσ4 := sig2_ge hM
  obtain ⟨hsum, hk1, hk2⟩ := card_four x y
  set α := (x \ y).card; set β := (y \ x).card; set γ := (x ∩ y).card; set δ := (x ∪ y)ᶜ.card
  have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
  have hT' : 16 * (T : ℝ) ≤ m := by exact_mod_cast hTm
  have hsumR : (α : ℝ) + β + γ + δ = m := by exact_mod_cast hsum
  have hk1R : (α : ℝ) + γ = x.card := by exact_mod_cast hk1
  have hk2R : (β : ℝ) + γ = y.card := by exact_mod_cast hk2
  have hxa := abs_le.mp hx; have hya := abs_le.mp hy; have hxya := abs_le.mp hxy
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hnα : (m : ℝ) / 16 ≤ α := by linarith
  have hnβ : (m : ℝ) / 16 ≤ β := by linarith
  have hnγ : (m : ℝ) / 16 ≤ γ := by linarith
  have hnδ : (m : ℝ) / 16 ≤ δ := by linarith
  have h2 : ∀ {k : ℕ}, (m : ℝ) / 16 ≤ k → 2 ≤ k := fun {k} h => by
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hα2 := h2 hnα; have hβ2 := h2 hnβ; have hγ2 := h2 hnγ; have hδ2 := h2 hnδ
  have hn : (0 : ℝ) < m / 16 := by linarith
  -- Lemma B0′ in the four classes
  have hQ := quad_err hM hα2 hβ2 hγ2 hδ2 hn hnα hnβ hnγ hnδ a s (I0 m M)
  have hQg := qg_le hM (by omega) (by omega) (by omega) (by omega) hsum a s (I0 m M)
  rw [show α + γ = x.card from hk1] at hQg
  -- the variance in `c`
  have hW := w3_ge hn hnα hnβ hnγ hnδ hσ
  set W := (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α))) * (sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ))) /
          (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α)) + sig2 M * ((β : ℝ) * δ / ((β : ℝ) + δ)))
  have hWf : 2 / √(2 * π * W) ≤ 13 / √(m : ℝ) := w_factor (by linarith) hσ4 hW
  -- the comparison of the two conditional densities
  have hY1 := a_dev hM (by omega) hg ha hw hu hT0 hx
  have hY2 := a_dev hM (by omega) hg ha hw hu hT0 hy
  have hA0 : (0 : ℝ) < α := by linarith
  have hB0 : (0 : ℝ) < β := by linarith
  have hC0 : (0 : ℝ) < γ := by linarith
  have hD0 : (0 : ℝ) < δ := by linarith
  have hR := typ_ratio (Y := √(sig2 M) * (2 + (4 + g) * T)) (a := (a : ℝ)) (s := (s : ℝ))
    hA0 hB0 hC0 hD0 hσ hT0 (by rw [hsumR]; exact hT')
    (by rw [hsumR, add_comm (γ : ℝ), hk1R]; exact hx) (by rw [hsumR, hk2R]; exact hy)
    (by rw [hsumR]; exact hxy)
    (by rw [hsumR, add_comm (γ : ℝ), hk1R]; exact hY1) (by rw [hsumR, hk2R]; exact hY2)
  rw [hsumR, hk2R] at hR
  have hpair := gaussB_pair hM (k := y.card) (m := m) (by omega) (by omega) a s
  have hexp : 64 * (T : ℝ) * (√(sig2 M) * (2 + (4 + g) * T)) ^ 2 / (sig2 M * (m : ℝ) ^ 2) =
      64 * T * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hσ.le]; field_simp
  rw [hexp] at hR
  -- assembling
  have hgm := gaussB_nonneg M m s
  have hRx : 0 ≤ Rg M m x a s := mul_nonneg (gaussB_nonneg _ _ _) (gaussB_nonneg _ _ _)
  set Gν := gd ((γ : ℝ) * a / ((γ : ℝ) + α) + (β : ℝ) * ((s : ℝ) - a) / ((β : ℝ) + δ))
          (sig2 M * ((γ : ℝ) * α / ((γ : ℝ) + α) + (β : ℝ) * δ / ((β : ℝ) + δ))) (a : ℝ)
  have hGν : 0 ≤ Gν := gd_nonneg _ _ _
  have hQg' : (∑ c ∈ I0 m M, gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) *
      gaussB M δ (s - 2 * a + c)) ≤ Rg M m x a s * Gν * (1 + 13 / √(m : ℝ)) := by
    refine hQg.trans ?_
    unfold Rg
    gcongr
    exact mul_nonneg (mul_nonneg (gaussB_nonneg _ _ _) (gaussB_nonneg _ _ _)) hGν
  rw [pairP_eq (by omega)]
  have hQ' := (abs_le.mp hQ).2
  have hEr : 3162 / (√(sig2 M) ^ 3 * (((m : ℝ) / 16) ^ 2 * √((m : ℝ) / 16))) = ErrB M m := rfl
  rw [hEr] at hQ'
  generalize (∑ c ∈ I0 m M, lawS M γ c * lawS M α (a - c) * lawS M β (a - c) *
      lawS M δ (s - 2 * a + c)) = Qs at hQ' ⊢
  generalize (∑ c ∈ I0 m M, gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) *
      gaussB M δ (s - 2 * a + c)) = Qg at hQ' hQg'
  have hQle : Qs ≤ Rg M m x a s * Gν * (1 + 13 / √(m : ℝ)) + ErrB M m := by linarith
  have step1 : Qs * gaussB M m s ≤
      Rg M m x a s * Gν * (1 + 13 / √(m : ℝ)) * gaussB M m s + ErrB M m * gaussB M m s := by
    have := mul_le_mul_of_nonneg_right hQle hgm
    linarith
  have step2 : Gν * gaussB M m s ≤ (1 + 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2) *
      exp (64 * T * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2) * Rg M m y a s := by
    unfold Rg; rw [hpair]
    calc Gν * gaussB M m s ≤ (1 + 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2) *
          exp (64 * T * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2) *
          gd ((y.card : ℝ) * s / m) (sig2 M * y.card * ((m : ℝ) - y.card) / m) a * gaussB M m s :=
          mul_le_mul_of_nonneg_right hR hgm
      _ = _ := by ring
  have h13 : 0 ≤ 1 + 13 / √(m : ℝ) := by positivity
  calc Qs * gaussB M m s
      ≤ Rg M m x a s * (1 + 13 / √(m : ℝ)) * (Gν * gaussB M m s) + ErrB M m * gaussB M m s := by
        linarith [step1, show Rg M m x a s * Gν * (1 + 13 / √(m : ℝ)) * gaussB M m s =
          Rg M m x a s * (1 + 13 / √(m : ℝ)) * (Gν * gaussB M m s) by ring]
    _ ≤ Rg M m x a s * (1 + 13 / √(m : ℝ)) * ((1 + 64 * (T : ℝ) ^ 2 / (m : ℝ) ^ 2) *
          exp (64 * T * (2 + (4 + g) * T) ^ 2 / (m : ℝ) ^ 2) * Rg M m y a s) +
          ErrB M m * gaussB M m s := by
        gcongr
    _ = FacB g m T * (Rg M m x a s * Rg M m y a s) + ErrB M m * gaussB M m s := by
        unfold FacB; ring

end ArcsAlgo.LLT
