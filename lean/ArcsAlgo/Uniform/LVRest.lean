module

public import ArcsAlgo.Uniform.LVArcs
public import ArcsAlgo.Uniform.Indep
set_option autoImplicit false

/-!
# Theorem LV: the rest of the circle (paper §6.6)

Jensen (`pow_four_integral_le`), the fourth moment by independence (`sum_Pw_four`:
`E P_w(θ)⁴ = (E cos⁴(πwθ))^m`) and Markov: `prW_rest`.
-/

open Finset Real MeasureTheory Set

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `E cos⁴(πwθ)` for `w` uniform in `{1, …, M}`. -/
noncomputable def rhoLV (M : ℕ) (θ : ℝ) : ℝ := (∑ c : Fin M, Real.cos (π * (((c : ℕ) : ℝ) + 1) * θ) ^ 4) / M

/-- Cauchy–Schwarz on an interval: `(∫_a^b f)² ≤ (b − a) ∫_a^b f²`. -/
theorem sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ θ in a..b, f θ) ^ 2 ≤ (b - a) * ∫ θ in a..b, f θ ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have hL : 0 < b - a := by linarith
  set I := ∫ θ in a..b, f θ
  set c := I / (b - a)
  have h0 : 0 ≤ ∫ θ in a..b, (f θ - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun θ _ => sq_nonneg _
  have e : ∫ θ in a..b, (f θ - c) ^ 2 = (∫ θ in a..b, f θ ^ 2) - 2 * c * I + c ^ 2 * (b - a) := by
    have e1 : ∀ θ, (f θ - c) ^ 2 = f θ ^ 2 - 2 * c * f θ + c ^ 2 := fun θ => by ring
    simp only [e1]
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun θ => f θ ^ 2 - 2 * c * f θ).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun θ => f θ ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ => 2 * c * f θ).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have : c * (b - a) = I := by simp only [c]; field_simp
  nlinarith

/-- Jensen on an interval of length `L`: `(∫ f)⁴ ≤ L³ ∫ f⁴`. -/
theorem pow_four_integral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ θ in a..b, f θ) ^ 4 ≤ (b - a) ^ 3 * ∫ θ in a..b, f θ ^ 4 := by
  have h1 := sq_integral_le hf hab
  have h2 := sq_integral_le (by fun_prop : Continuous fun θ => f θ ^ 2) hab
  have hL : 0 ≤ b - a := by linarith
  have h3 : ((∫ θ in a..b, f θ) ^ 2) ^ 2 ≤ ((b - a) * ∫ θ in a..b, f θ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  simp only [← pow_mul] at h2
  calc (∫ θ in a..b, f θ) ^ 4 = ((∫ θ in a..b, f θ) ^ 2) ^ 2 := by ring
    _ ≤ ((b - a) * ∫ θ in a..b, f θ ^ 2) ^ 2 := h3
    _ = (b - a) ^ 2 * (∫ θ in a..b, f θ ^ 2) ^ 2 := by ring
    _ ≤ (b - a) ^ 2 * ((b - a) * ∫ θ in a..b, f θ ^ 4) :=
        mul_le_mul_of_nonneg_left (by simpa using h2) (by positivity)
    _ = (b - a) ^ 3 * ∫ θ in a..b, f θ ^ 4 := by ring

/-- **The fourth moment by independence**: `E P_w(θ)⁴ = (E cos⁴(πwθ))^m`. -/
theorem sum_Pw_four (θ : ℝ) :
    ∑ w : Fin m → Fin M, Pw w θ ^ 4 = (M : ℝ) ^ m * rhoLV M θ ^ m := by
  unfold Pw
  simp only [← Finset.prod_pow]
  rw [← Fintype.sum_pow (fun c : Fin M => Real.cos (π * (((c : ℕ) : ℝ) + 1) * θ) ^ 4) m]
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h
    rcases Nat.eq_zero_or_pos m with h' | h'
    · subst h'; simp
    · simp [zero_pow h'.ne']
  · unfold rhoLV
    rw [← mul_pow]; congr 1
    field_simp
    refine Finset.sum_congr rfl fun c _ => by ring_nf

theorem Rw_nonneg (hM : 2 ≤ M) (w : Fin m → Fin M) : 0 ≤ Rw w := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 1 / (4 * (M : ℝ)) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  exact intervalIntegral.integral_nonneg (by linarith) fun θ _ => abs_nonneg _

set_option maxHeartbeats 1000000 in
/-- **The rest of the circle** (paper §6.6, proof of Theorem LV): if `E cos⁴(πwθ) ≤ ρ` on
`1/(2M) ≤ θ ≤ 1/2 − 1/(4M)`, then by Jensen, independence and Markov
`Pr(∫_{rest}|P_w| ≥ 1/(4M√(2πm))) ≤ 64π²m²M⁴ρ^m`. -/
theorem prW_rest (hM : 2 ≤ M) (hm : 1 ≤ m) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ θ : ℝ, 1 / (2 * (M : ℝ)) ≤ θ → θ ≤ 1 / 2 - 1 / (4 * (M : ℝ)) → rhoLV M θ ≤ ρ) :
    prW M m (fun w => Lmin M m / 4 ≤ Rw w) ≤ 64 * π ^ 2 * (m : ℝ) ^ 2 * (M : ℝ) ^ 4 * ρ ^ m := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  set β : ℝ := 1 / (2 * (M : ℝ))
  set γ : ℝ := 1 / 2 - 1 / (4 * (M : ℝ))
  have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 1 / (4 * (M : ℝ)) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hβγ : β ≤ γ := by simp only [β, γ]; linarith
  have hL : γ - β ≤ 1 / 2 := by simp only [β, γ]; have : 0 < 1 / (4 * (M : ℝ)) := by positivity
                                have : 0 < 1 / (2 * (M : ℝ)) := by positivity
                                linarith
  have hL0 : 0 ≤ γ - β := by linarith
  set c := Lmin M m / 4
  have hc : 0 < c := by simp only [c]; unfold Lmin; positivity
  have hcont : ∀ w : Fin m → Fin M, Continuous fun θ => |Pw w θ| := fun w => by
    have := continuous_Pw w; fun_prop
  -- Markov
  have hmk : ∀ w : Fin m → Fin M, (if c ≤ Rw w then (1 : ℝ) else 0) ≤ Rw w ^ 4 / c ^ 4 := by
    intro w
    split_ifs with h
    · rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hc.le h 4
    · have := Rw_nonneg hM w; positivity
  -- Jensen for each `w`
  have hj : ∀ w : Fin m → Fin M, Rw w ^ 4 ≤ (γ - β) ^ 3 * ∫ θ in β..γ, Pw w θ ^ 4 := by
    intro w
    have := pow_four_integral_le (hcont w) hβγ
    have e : ∀ θ, |Pw w θ| ^ 4 = Pw w θ ^ 4 := fun θ => by
      rw [pow_abs, abs_of_nonneg (by positivity)]
    simp only [e] at this
    exact this
  -- the expectation of `∫ P⁴`
  have hE : ∑ w : Fin m → Fin M, ∫ θ in β..γ, Pw w θ ^ 4 ≤ (M : ℝ) ^ m * ((γ - β) * ρ ^ m) := by
    rw [← intervalIntegral.integral_finsetSum fun w _ =>
      ((by have := continuous_Pw w; fun_prop : Continuous fun θ => Pw w θ ^ 4).intervalIntegrable _ _)]
    simp only [sum_Pw_four]
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := intervalIntegral.integral_mono_on hβγ
      ((by unfold rhoLV; fun_prop : Continuous fun θ => rhoLV M θ ^ m).intervalIntegrable (μ := volume) β γ)
      ((continuous_const : Continuous fun _ : ℝ => ρ ^ m).intervalIntegrable (μ := volume) β γ) fun θ hθ => by
        have h0 : 0 ≤ rhoLV M θ := by unfold rhoLV; positivity
        exact pow_le_pow_left₀ h0 (hρ θ hθ.1 hθ.2) m
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  unfold prW
  calc (∑ w, if c ≤ Rw w then (1 : ℝ) else 0) / (M : ℝ) ^ m
      ≤ (∑ w : Fin m → Fin M, Rw w ^ 4 / c ^ 4) / (M : ℝ) ^ m :=
        div_le_div_of_nonneg_right (sum_le_sum fun w _ => hmk w) (by positivity)
    _ ≤ (∑ w : Fin m → Fin M, (γ - β) ^ 3 * ∫ θ in β..γ, Pw w θ ^ 4) / c ^ 4 / (M : ℝ) ^ m := by
        rw [← sum_div]
        gcongr with w
        exact hj w
    _ ≤ (γ - β) ^ 3 * ((M : ℝ) ^ m * ((γ - β) * ρ ^ m)) / c ^ 4 / (M : ℝ) ^ m := by
        rw [← mul_sum]
        gcongr
    _ = (γ - β) ^ 4 * ρ ^ m / c ^ 4 := by field_simp
    _ ≤ (1 / 2) ^ 4 * ρ ^ m / c ^ 4 := by gcongr
    _ = 64 * π ^ 2 * (m : ℝ) ^ 2 * (M : ℝ) ^ 4 * ρ ^ m := by
        have hs : √(2 * π * m) ^ 4 = (2 * π * m) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
        have hc4 : c ^ 4 = 1 / (256 * (M : ℝ) ^ 4 * (2 * π * m) ^ 2) := by
          simp only [c]; unfold Lmin; rw [← hs]; field_simp; ring
        rw [hc4]; field_simp; ring

end ArcsAlgo.LLT
