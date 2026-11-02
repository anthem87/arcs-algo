module

public import ArcsAlgo.Uniform.LVGood
public import ArcsAlgo.Uniform.B2fix
public import ArcsAlgo.Uniform.B1
public import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false

/-!
# Theorem LV: exponential tail of the endgame count (paper §6.6)

`thmLV_gen`: for any `ρ ≥ sup_{M, θ ∈ 𝔅} E cos⁴(πwθ)`, with `M = 2^b`, in the window and for `|u| ≤ M`,
`u ≡ s (mod 2)`, `Pr(Z(u) = 0 | S_E = s) ≤ C_g(m^{5/2}M⁵ρ^m + 2^{−0.53m})` for `m ≥ m₀`.
`thmLV`: the same with `ρ = 0.446`, from the numerical certificate `LVRhoCert` (`ρ ≤ 0.44495`).
`thmLV_rate`: the per-round failure is at most `2^{−m/2}` as soon as `m ≥ 7.6(b + log₂ m)`, `m ≥ m₀`.
Hypothesis: `LVRhoCert` only (for `thmLV`, `thmLV_rate`).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `Pr(Z(u) = 0 | S_E = s)`. -/
noncomputable def condZ0 (M m : ℕ) (u s : ℤ) : ℝ :=
  prW M m (fun w => Zc w u = 0 ∧ Sw w = s) / lawS M m s

/-- **The certified rate of Theorem LV** (`lv_rate_certified.py`, paper §6.6): for every `M ≥ 2`
and `θ ∈ 𝔅`, `E cos⁴(πwθ) ≤ 0.44495`. By symmetry it is stated on `1/(2M) ≤ θ ≤ 1/2 − 1/(4M)`.
A numerical certificate, taken as a hypothesis. -/
def LVRhoCert : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ θ : ℝ, 1 / (2 * (M : ℝ)) ≤ θ → θ ≤ 1 / 2 - 1 / (4 * (M : ℝ)) → rhoLV M θ ≤ 0.44495

theorem prW_or_le (E F : (Fin m → Fin M) → Prop) [DecidablePred E] [DecidablePred F] :
    prW M m (fun w => E w ∨ F w) ≤ prW M m E + prW M m F := by
  unfold prW
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  by_cases h1 : E w <;> by_cases h2 : F w <;> simp [h1, h2]

/-- `5/8 ≤ 2^{−0.53}`. -/
theorem five_eighths_le : (5 / 8 : ℝ) ≤ (2 : ℝ) ^ (-(53 / 100 : ℝ)) := by
  have h1 : (2 : ℝ) ^ (53 / 100 : ℝ) ≤ (2 : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 8 / 5 := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (5 : ℕ) ≠ 0),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Real.rpow_neg (by norm_num), le_inv_comm₀ (by norm_num) (by positivity)]
  linarith

theorem sig2_le_five {M' : ℕ} (hM' : 2 ≤ M') : sig2 (2 * M') ≤ 5 * sig2 M' := by
  have : (2 : ℝ) ≤ M' := by exact_mod_cast hM'
  unfold sig2; push_cast; nlinarith

/-- For `M = 2` the window forces enough odd weights: `S_E + #odd = 2m`. -/
theorem odd_two (hM2 : M = 2) (w : Fin m → Fin M) : Sw w + oddCnt w = 2 * m := by
  unfold Sw oddCnt
  rw [card_eq_sum_ones, sum_filter]
  push_cast
  rw [← sum_add_distrib]
  have : ∀ i, ((w i : ℕ) : ℤ) + 1 + (if (w i : ℕ) % 2 = 0 then (1 : ℤ) else 0) = 2 := by
    intro i
    have h2 : (w i : ℕ) < 2 := by have := (w i).isLt; omega
    interval_cases h : (w i : ℕ) <;> simp
  simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

set_option maxHeartbeats 2000000 in
/-- **Theorem LV (exponential tail of the endgame count)** (paper §6.6), for any `ρ` bounding
`E cos⁴(πwθ)` on `𝔅`: in the setting of Lemma B, with `M = 2^b`, `|s − mμ| ≤ gσ√m`, `|u| ≤ M`,
`u ≡ s (mod 2)`, there are `m₀` and `C_g` with, for `m ≥ m₀`,
`Pr(Z(u) = 0 | S_E = s) ≤ C_g(m^{5/2}M⁵ρ^m + 2^{−0.53m})`. -/
theorem thmLV_gen {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ M : ℕ, 2 ≤ M → ∀ θ : ℝ, 1 / (2 * (M : ℝ)) ≤ θ → θ ≤ 1 / 2 - 1 / (4 * (M : ℝ)) → rhoLV M θ ≤ ρ)
    {g : ℝ} (hg : 0 ≤ g) :
    ∃ m₀ : ℕ, ∃ C : ℝ, ∀ b : ℕ, 1 ≤ b → ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW (2 ^ b)| ≤ g * √(sig2 (2 ^ b)) * √(m : ℝ) → |(u : ℝ)| ≤ (2 ^ b : ℕ) →
      (∃ a, 2 * a = s + u) →
      condZ0 (2 ^ b) m u s ≤ C * ((m : ℝ) ^ ((5 : ℝ) / 2) * ((2 ^ b : ℕ) : ℝ) ^ 5 * ρ ^ m +
        (2 : ℝ) ^ (-(53 / 100 : ℝ) * m)) := by
  set E := Real.exp (g ^ 2 / 2)
  have hE : 0 < E := Real.exp_pos _
  set m₁ := ⌈34 * √(2 * π) * E⌉₊
  set m₂ := ⌈4 * g ^ 2⌉₊
  set C := 2 * √(2 * π) * E * (78 + 64 * π ^ 2)
  refine ⟨max (max m₁ m₂) 12000, C, fun b hb m hm s u hw hu hpar => ?_⟩
  set M := 2 ^ b with hMdef
  have hM : 2 ≤ M := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : 12000 ≤ m := le_trans (le_max_right _ _) hm
  have hmR : (12000 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmp : (0 : ℝ) < m := by linarith
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hσ := sig2_pos hM
  have hsσ := Real.sqrt_pos.mpr hσ
  have hsm := Real.sqrt_pos.mpr hmp
  -- `Pr(S_E = s) ≥ L`
  set L := E⁻¹ / (2 * (√(2 * π) * (√(sig2 M) * √(m : ℝ))))
  have hL0 : 0 < L := by positivity
  have hlaw : L ≤ lawS M m s := by
    have hdel : del2 g m ≤ 1 / 2 := by
      unfold del2
      rw [div_le_iff₀ hmp]
      have : 34 * √(2 * π) * E ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm1)
      linarith
    have hgm0 := gm_ge hM (by omega : 1 ≤ m) hw
    have hgm : 0 < gaussB M m s := lt_of_lt_of_le (by positivity) hgm0
    have hrel := law_rel hM (by omega : 2 ≤ m) hw
    have := (abs_le.mp hrel).1
    rw [div_sub_one hgm.ne', le_div_iff₀ hgm] at this
    have h2 : gaussB M m s / 2 ≤ lawS M m s := by nlinarith
    calc L = (E⁻¹ / (√(2 * π) * (√(sig2 M) * √(m : ℝ)))) / 2 := by simp only [L]; field_simp
      _ ≤ gaussB M m s / 2 := by gcongr
      _ ≤ lawS M m s := h2
  -- the bad events
  set good : (Fin m → Fin M) → Prop := fun w => m * (M : ℝ) ^ 2 / 80 ≤ Vw w ∧ m ≤ 20 * oddCnt w
  have hZ : ∀ w : Fin m → Fin M, Zc w u = 0 ∧ Sw w = s → (¬ good w ∧ Sw w = s) ∨ Lmin M m / 4 ≤ Rw w := by
    intro w ⟨hz, hs⟩
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hg' : good w := by_contra fun h => h1 h hs
    have hpar' : ∃ a, 2 * a = Sw w + u := by rw [hs]; exact hpar
    have := Z_pos_of_good hM hm3 w u hpar' hu hg'.1 hg'.2 h2
    omega
  have hstep : prW M m (fun w => Zc w u = 0 ∧ Sw w = s) ≤
      prW M m (fun w => ¬ good w ∧ Sw w = s) + 64 * π ^ 2 * (m : ℝ) ^ 2 * (M : ℝ) ^ 4 * ρ ^ m := by
    classical
    refine (prW_mono (E' := fun w => (¬ good w ∧ Sw w = s) ∨ Lmin M m / 4 ≤ Rw w) hZ).trans
      ((prW_or_le _ _).trans ?_)
    gcongr
    exact prW_rest hM (by omega) hρ0 (hρ M hM)
  -- `Pr(¬good, S_E = s) ≤ 26 (5/8)^m / (σ′√m)`, and `≤ C₁ L (5/8)^m`
  have hbad : prW M m (fun w => ¬ good w ∧ Sw w = s) ≤ 156 * √(2 * π) * E * L * (5 / 8 : ℝ) ^ m := by
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · -- `M = 2`: the event is empty in the window
      have hb1 : b = 1 := by omega
      have hM2 : M = 2 := by rw [hMdef, hb1]; norm_num
      have : prW M m (fun w => ¬ good w ∧ Sw w = s) = 0 := by
        classical
        refine prW_false fun w ⟨hng, hs⟩ => hng ⟨?_, ?_⟩
        · have hV : (m : ℝ) ≤ Vw w := by
            unfold Vw
            calc (m : ℝ) = ∑ _i : Fin m, (1 : ℝ) := by simp
              _ ≤ _ := sum_le_sum fun i _ => by
                  have := W_pos w i; have : (0 : ℝ) ≤ ((w i : ℕ) : ℝ) := Nat.cast_nonneg _
                  nlinarith
          have hMr : (M : ℝ) = 2 := by exact_mod_cast hM2
          rw [hMr]; linarith
        · have ho := odd_two hM2 w
          rw [hs] at ho
          have hoR : (oddCnt w : ℝ) = 2 * m - s := by
            have : ((oddCnt w : ℕ) : ℤ) = 2 * m - s := by linarith
            exact_mod_cast this
          rw [hM2] at hw
          have hmu : muW 2 = 3 / 2 := by unfold muW; norm_num
          have hsg : √(sig2 2) = 1 / 2 := by
            unfold sig2; rw [show ((2 : ℕ) : ℝ) ^ 2 - 1 = 3 by norm_num,
              show (3 : ℝ) / 12 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          rw [hmu, hsg] at hw
          have h4 : 4 * g ^ 2 ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm2)
          have h2g : 2 * g ≤ √(m : ℝ) := by
            rw [Real.le_sqrt (by positivity) hmp.le]; nlinarith
          have hgm : g * √(m : ℝ) ≤ m / 2 := by
            have := Real.mul_self_sqrt hmp.le
            nlinarith
          have hs' := (abs_le.mp hw).2
          have : (m : ℝ) ≤ 20 * oddCnt w := by rw [hoR]; nlinarith
          exact_mod_cast this
      rw [this]; positivity
    · obtain ⟨c, hc⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
      set M' := 2 ^ (c + 1)
      have hM'2 : 2 ≤ M' := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hMM : M = 2 * M' := by rw [hMdef, hc, pow_succ, mul_comm]
      classical
      have hsplit : ∀ w : Fin m → Fin M, ¬ good w ∧ Sw w = s →
          (20 * cntE (eH hMM) 1 w < m ∧ Sw w = s) ∨ (20 * cntE (eP hMM) 0 w < m ∧ Sw w = s) := by
        intro w ⟨hng, hs⟩
        by_contra hc'
        push_neg at hc'
        obtain ⟨h1, h2⟩ := hc'
        have h1' : m ≤ 20 * cntE (eH hMM) 1 w := by by_contra h; exact h1 (by omega) hs
        have h2' : m ≤ 20 * cntE (eP hMM) 0 w := by by_contra h; exact h2 (by omega) hs
        apply hng
        refine ⟨?_, ?_⟩
        · have hV := Vw_ge_cntH hMM w
          have : (m : ℝ) ≤ 20 * cntE (eH hMM) 1 w := by exact_mod_cast h1'
          nlinarith
        · exact le_trans h2' (by have := cntP_le_odd hMM w; omega)
      have hH := prW_few_le (m := m) hM'2 hMM (by omega) (eH hMM) (fun b => ((M' * (b : ℕ) : ℕ) : ℤ)) 1 one_pos (eH_formula hMM) 1 s
      have hP := prW_few_le (m := m) hM'2 hMM (by omega) (eP hMM) (fun b => ((b : ℕ) : ℤ) - 1) 2 two_pos (eP_formula hMM) 0 s
      have hσ' := sig2_pos hM'2
      have hs' := Real.sqrt_pos.mpr hσ'
      have hσσ : √(sig2 M) ≤ 3 * √(sig2 M') := by
        rw [show (3 : ℝ) * √(sig2 M') = √(9 * sig2 M') by
          rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        apply Real.sqrt_le_sqrt
        have := sig2_le_five hM'2; rw [← hMM] at this; linarith
      calc prW M m (fun w => ¬ good w ∧ Sw w = s)
          ≤ prW M m (fun w => 20 * cntE (eH hMM) 1 w < m ∧ Sw w = s) +
              prW M m (fun w => 20 * cntE (eP hMM) 0 w < m ∧ Sw w = s) :=
            (prW_mono (E' := fun w => (20 * cntE (eH hMM) 1 w < m ∧ Sw w = s) ∨
              (20 * cntE (eP hMM) 0 w < m ∧ Sw w = s)) hsplit).trans (prW_or_le _ _)
        _ ≤ 2 * ((5 / 8 : ℝ) ^ m * (13 / (√(sig2 M') * √(m : ℝ)))) := by linarith
        _ ≤ 156 * √(2 * π) * E * L * (5 / 8 : ℝ) ^ m := by
            have e : 156 * √(2 * π) * E * L = 78 / (√(sig2 M) * √(m : ℝ)) := by
              simp only [L]; have : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
              field_simp; ring
            rw [e]
            have : 13 / (√(sig2 M') * √(m : ℝ)) ≤ 39 / (√(sig2 M) * √(m : ℝ)) := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
            have hq := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * (5 / 8 : ℝ) ^ m)
            calc 2 * ((5 / 8 : ℝ) ^ m * (13 / (√(sig2 M') * √(m : ℝ))))
                = 2 * (5 / 8 : ℝ) ^ m * (13 / (√(sig2 M') * √(m : ℝ))) := by ring
              _ ≤ 2 * (5 / 8 : ℝ) ^ m * (39 / (√(sig2 M) * √(m : ℝ))) := hq
              _ = 78 / (√(sig2 M) * √(m : ℝ)) * (5 / 8 : ℝ) ^ m := by ring
  -- conclusion
  have hnum0 : 0 ≤ prW M m (fun w => Zc w u = 0 ∧ Sw w = s) := by unfold prW; positivity
  have hlaw0 : 0 < lawS M m s := lt_of_lt_of_le hL0 hlaw
  unfold condZ0
  have h58 : (5 / 8 : ℝ) ^ m ≤ (2 : ℝ) ^ (-(53 / 100 : ℝ) * m) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) five_eighths_le m
  have hm52 : (m : ℝ) ^ ((5 : ℝ) / 2) = (m : ℝ) ^ 2 * √(m : ℝ) := by
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hmp, Real.sqrt_eq_rpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hσM : √(sig2 M) ≤ M := by
    rw [Real.sqrt_le_left (by positivity)]
    have : sig2 M ≤ (M : ℝ) ^ 2 := by unfold sig2; nlinarith
    nlinarith
  have hρm : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
  have hX0 : 0 ≤ (m : ℝ) ^ ((5 : ℝ) / 2) * ((M : ℕ) : ℝ) ^ 5 * ρ ^ m := by positivity
  have hY0 : 0 ≤ (2 : ℝ) ^ (-(53 / 100 : ℝ) * m) := by positivity
  set X := (m : ℝ) ^ ((5 : ℝ) / 2) * ((M : ℕ) : ℝ) ^ 5 * ρ ^ m
  set Y := (2 : ℝ) ^ (-(53 / 100 : ℝ) * m)
  set A := 156 * √(2 * π) * E * (5 / 8 : ℝ) ^ m
  set B := 64 * π ^ 2 * (m : ℝ) ^ 2 * (M : ℝ) ^ 4 * ρ ^ m
  have hA : A ≤ 156 * √(2 * π) * E * Y := mul_le_mul_of_nonneg_left h58 (by positivity)
  have hBL : B / L = 128 * π ^ 2 * √(2 * π) * E * ((m : ℝ) ^ 2 * √(m : ℝ) * (M : ℝ) ^ 4 * ρ ^ m) * √(sig2 M) := by
    simp only [B, L]; field_simp; ring
  have hK0 : 0 ≤ 128 * π ^ 2 * √(2 * π) * E * ((m : ℝ) ^ 2 * √(m : ℝ) * (M : ℝ) ^ 4 * ρ ^ m) := by positivity
  have hB : B / L ≤ 128 * π ^ 2 * √(2 * π) * E * X := by
    rw [hBL]
    calc _ ≤ 128 * π ^ 2 * √(2 * π) * E * ((m : ℝ) ^ 2 * √(m : ℝ) * (M : ℝ) ^ 4 * ρ ^ m) * M :=
          mul_le_mul_of_nonneg_left hσM hK0
      _ = 128 * π ^ 2 * √(2 * π) * E * X := by simp only [X]; rw [hm52]; push_cast; ring
  have hfin : prW M m (fun w => Zc w u = 0 ∧ Sw w = s) / lawS M m s ≤ A + B / L := by
    calc prW M m (fun w => Zc w u = 0 ∧ Sw w = s) / lawS M m s
        ≤ prW M m (fun w => Zc w u = 0 ∧ Sw w = s) / L := div_le_div_of_nonneg_left hnum0 hL0 hlaw
      _ ≤ (A * L + B) / L := div_le_div_of_nonneg_right (hstep.trans (by simp only [A, B]; linarith)) hL0.le
      _ = A + B / L := by field_simp
  have hC : 156 * √(2 * π) * E * Y + 128 * π ^ 2 * √(2 * π) * E * X ≤ C * (X + Y) := by
    simp only [C]
    have h0 : 0 ≤ √(2 * π) * E := by positivity
    nlinarith [mul_nonneg h0 hX0, mul_nonneg h0 hY0, mul_nonneg (mul_nonneg h0 hY0) (sq_nonneg π)]
  linarith

/-- **Theorem LV** (paper §6.6) with the certified rate: `ρ ≤ 0.44495 < 0.446`, so
`Pr(Z(u) = 0 | S_E = s) ≤ C_g(m^{5/2}M⁵·0.446^m + 2^{−0.53m})` for `m ≥ m₀`, uniformly in `M = 2^b`. -/
theorem thmLV (hcert : LVRhoCert) {g : ℝ} (hg : 0 ≤ g) :
    ∃ m₀ : ℕ, ∃ C : ℝ, ∀ b : ℕ, 1 ≤ b → ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW (2 ^ b)| ≤ g * √(sig2 (2 ^ b)) * √(m : ℝ) → |(u : ℝ)| ≤ (2 ^ b : ℕ) →
      (∃ a, 2 * a = s + u) →
      condZ0 (2 ^ b) m u s ≤ C * ((m : ℝ) ^ ((5 : ℝ) / 2) * ((2 ^ b : ℕ) : ℝ) ^ 5 * 0.446 ^ m +
        (2 : ℝ) ^ (-(53 / 100 : ℝ) * m)) :=
  thmLV_gen (by norm_num) (fun M hM θ h1 h2 => (hcert M hM θ h1 h2).trans (by norm_num)) hg

/-- `log 0.446 ≤ −(22/19) log 2`, i.e. `0.446¹⁹ ≤ 2⁻²²`. -/
theorem log_rho_le : Real.log 0.446 ≤ -(22 / 19) * Real.log 2 := by
  have h : (0.446 : ℝ) ^ 19 ≤ (2 : ℝ)⁻¹ ^ 22 := by norm_num
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at h2
  push_cast at h2
  linarith

set_option maxHeartbeats 1000000 in
/-- **The rate of Theorem LV** (paper §6.6): the per-round failure is at most `2^{−m/2}` as soon as
`m ≥ 7.6(b + log₂ m)` and `m ≥ m₀`. -/
theorem thmLV_rate (hcert : LVRhoCert) {g : ℝ} (hg : 0 ≤ g) :
    ∃ m₀ : ℕ, ∀ b : ℕ, 1 ≤ b → ∀ m : ℕ, m₀ ≤ m → 38 / 5 * ((b : ℝ) + Real.logb 2 m) ≤ m →
      ∀ s u : ℤ, |(s : ℝ) - m * muW (2 ^ b)| ≤ g * √(sig2 (2 ^ b)) * √(m : ℝ) →
      |(u : ℝ)| ≤ (2 ^ b : ℕ) → (∃ a, 2 * a = s + u) →
      condZ0 (2 ^ b) m u s ≤ (2 : ℝ) ^ (-(m : ℝ) / 2) := by
  obtain ⟨m₀, C, hC⟩ := thmLV hcert hg
  set D := |C|
  refine ⟨max (max m₀ ⌈100 * D + 2⌉₊) 1, fun b hb m hm hrate s u hw hu hpar => ?_⟩
  have hm0 : m₀ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : 100 * D + 2 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm))
  have hD : 0 ≤ D := abs_nonneg C
  set x : ℝ := (m : ℝ) with hxdef
  have hx : 0 < x := by simp only [x]; linarith
  have h := hC b hb m hm0 s u hw hu hpar
  set T := x ^ ((5 : ℝ) / 2) * ((2 ^ b : ℕ) : ℝ) ^ 5 * (0.446 : ℝ) ^ m
  set Y := (2 : ℝ) ^ (-(53 / 100 : ℝ) * x)
  have hT0 : 0 ≤ T := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have h' : condZ0 (2 ^ b) m u s ≤ D * (T + Y) := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  -- `T ≤ x^{−5/2} 2^{−x/2}`, by logarithms
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT : T ≤ x ^ (-(5 : ℝ) / 2) * (2 : ℝ) ^ (-x / 2) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity)]
    simp only [T]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hx, Real.log_rpow hx,
      Real.log_rpow (by norm_num), Real.log_pow, Real.log_pow, Nat.cast_pow, Real.log_pow]
    have hr := log_rho_le
    have hlb : Real.logb 2 x * Real.log 2 = Real.log x := by
      rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
    have hr2 : 38 / 5 * ((b : ℝ) + Real.logb 2 x) * Real.log 2 ≤ x * Real.log 2 :=
      mul_le_mul_of_nonneg_right hrate hlog2.le
    push_cast
    nlinarith
  -- `D x^{−5/2} ≤ 1/2` and `D 2^{−0.53x} ≤ 2^{−x/2}/2`
  have hx1 : 1 ≤ x := by linarith
  have h1 : D * x ^ (-(5 : ℝ) / 2) ≤ 1 / 2 := by
    have hxr : x ≤ x ^ ((5 : ℝ) / 2) := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [neg_div, Real.rpow_neg hx.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : D * Y ≤ (2 : ℝ) ^ (-x / 2) / 2 := by
    have e : Y = (2 : ℝ) ^ (-x / 2) * (2 : ℝ) ^ (-(3 / 100 : ℝ) * x) := by
      simp only [Y]; rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hq : 2 * D ≤ (2 : ℝ) ^ ((3 / 100 : ℝ) * x) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * ((3 / 100 : ℝ) * x))
      have hl : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      nlinarith
    have hneg : (2 : ℝ) ^ (-(3 / 100 : ℝ) * x) = ((2 : ℝ) ^ ((3 / 100 : ℝ) * x))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; ring_nf
    rw [e, hneg]
    have hp : 0 < (2 : ℝ) ^ ((3 / 100 : ℝ) * x) := by positivity
    have hp2 : 0 < (2 : ℝ) ^ (-x / 2) := by positivity
    rw [show D * ((2 : ℝ) ^ (-x / 2) * ((2 : ℝ) ^ ((3 / 100 : ℝ) * x))⁻¹) =
      (2 : ℝ) ^ (-x / 2) * (D / (2 : ℝ) ^ ((3 / 100 : ℝ) * x)) by ring]
    rw [div_eq_mul_one_div ((2 : ℝ) ^ (-x / 2)) 2]
    refine mul_le_mul_of_nonneg_left ?_ hp2.le
    rw [div_le_div_iff₀ hp (by norm_num)]; linarith
  have hT' : D * T ≤ (2 : ℝ) ^ (-x / 2) / 2 := by
    calc D * T ≤ D * (x ^ (-(5 : ℝ) / 2) * (2 : ℝ) ^ (-x / 2)) := mul_le_mul_of_nonneg_left hT hD
      _ = D * x ^ (-(5 : ℝ) / 2) * (2 : ℝ) ^ (-x / 2) := by ring
      _ ≤ 1 / 2 * (2 : ℝ) ^ (-x / 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 : ℝ) ^ (-x / 2) / 2 := by ring
  calc condZ0 (2 ^ b) m u s ≤ D * (T + Y) := h'
    _ = D * T + D * Y := by ring
    _ ≤ (2 : ℝ) ^ (-x / 2) / 2 + (2 : ℝ) ^ (-x / 2) / 2 := add_le_add hT' h2
    _ = (2 : ℝ) ^ (-(m : ℝ) / 2) := by ring

end ArcsAlgo.LLT
