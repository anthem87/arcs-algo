module

public import ArcsAlgo.Uniform.LVFourier
public import ArcsAlgo.Uniform.LVCos
public import ArcsAlgo.Uniform.LVMajor
set_option autoImplicit false

/-!
# Theorem LV: the count is positive on good weights (paper §6.6)

The major arc (`Pw_major`), the parity window (`Pw_parity`) and `Z_pos_of_good`: if `V ≥ mM²/80`,
at least `m/20` weights are odd and the rest contributes `∫|P_w| < 1/(4M√(2πm))`, then `Z(u) > 0`.
-/

open Finset Real MeasureTheory Set

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `V = Σ_i w_i²`. -/
noncomputable def Vw (w : Fin m → Fin M) : ℝ := ∑ i, ((((w i : ℕ) : ℝ) + 1)) ^ 2

/-- `Σ_i w_i⁴`. -/
noncomputable def Qw (w : Fin m → Fin M) : ℝ := ∑ i, ((((w i : ℕ) : ℝ) + 1)) ^ 4

/-- The number of odd weights. -/
def oddCnt (w : Fin m → Fin M) : ℕ := (univ.filter fun i => (w i : ℕ) % 2 = 0).card

theorem W_le (w : Fin m → Fin M) (i : Fin m) : (((w i : ℕ) : ℝ) + 1) ≤ M := by
  have := (w i).isLt
  have : ((w i : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast this
  exact this

theorem W_pos (w : Fin m → Fin M) (i : Fin m) : 0 < (((w i : ℕ) : ℝ) + 1) := by positivity

theorem Qw_le (w : Fin m → Fin M) : Qw w ≤ (M : ℝ) ^ 2 * Vw w := by
  unfold Qw Vw; rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have h1 := W_le w i; have h0 := W_pos w i
  have : (((w i : ℕ) : ℝ) + 1) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ h0.le h1 2
  nlinarith [sq_nonneg ((((w i : ℕ) : ℝ) + 1))]

theorem Vw_le (w : Fin m → Fin M) : Vw w ≤ m * (M : ℝ) ^ 2 := by
  unfold Vw
  calc ∑ i, (((w i : ℕ) : ℝ) + 1) ^ 2 ≤ ∑ _i : Fin m, (M : ℝ) ^ 2 :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (W_pos w i).le (W_le w i) 2
    _ = m * (M : ℝ) ^ 2 := by simp

/-- `Z(u) = 2^{m+1} ∫_0^{1/2} cos(πuθ) P_w(θ) dθ`. -/
theorem Zc_half (w : Fin m → Fin M) (u : ℤ) (h : ∃ a, 2 * a = Sw w + u) :
    (Zc w u : ℝ) = 2 ^ m * (2 * ∫ θ in (0 : ℝ)..(1 / 2), Real.cos (π * u * θ) * Pw w θ) := by
  rw [Zc_integral w u h]
  congr 1
  have hc : Continuous fun θ => Real.cos (π * u * θ) * Pw w θ := by
    have := continuous_Pw w; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have : ∫ θ in (-(1 / 2 : ℝ))..0, Real.cos (π * u * θ) * Pw w θ =
      ∫ θ in (0 : ℝ)..(1 / 2), Real.cos (π * u * θ) * Pw w θ := by
    have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := 1 / 2)
      (fun θ => Real.cos (π * u * θ) * Pw w θ)
    simp only [neg_zero] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [mul_neg, Real.cos_neg, Pw_neg]
  rw [this]; ring

/-- On the major arc `P_w` is compared with `g(θ) = e^{−aθ²}`, `a = π²V/2`: with `K = π⁴Σw⁴/4`,
`|g − P_w| ≤ Kθ⁴g` for `θ ≤ 1/(πM)`, and `|P_w| ≤ g` for `θ ≤ 1/(2M)`. -/
theorem Pw_major (hM : 0 < M) (w : Fin m → Fin M) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (1 / (π * M)), |Real.exp (-(π ^ 2 * Vw w / 2) * θ ^ 2) - Pw w θ| ≤
      π ^ 4 * Qw w / 4 * θ ^ 4 * Real.exp (-(π ^ 2 * Vw w / 2) * θ ^ 2)) ∧
    (∀ θ ∈ Set.Icc (0 : ℝ) (1 / (2 * (M : ℝ))), |Pw w θ| ≤ Real.exp (-(π ^ 2 * Vw w / 2) * θ ^ 2)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set x : Fin m → ℝ → ℝ := fun i θ => π * (((w i : ℕ) : ℝ) + 1) * θ
  have hx : ∀ θ, 0 ≤ θ → ∀ i, |x i θ| ≤ π * M * θ := fun θ hθ i => by
    simp only [x]
    rw [abs_of_nonneg (by have := W_pos w i; positivity)]
    have := W_le w i
    gcongr
  have hsq : ∀ θ, ∑ i, x i θ ^ 2 = π ^ 2 * Vw w * θ ^ 2 := fun θ => by
    simp only [x, Vw, mul_sum, sum_mul]; refine sum_congr rfl fun i _ => by ring
  have hq : ∀ θ, ∑ i, x i θ ^ 4 / 4 = π ^ 4 * Qw w / 4 * θ ^ 4 := fun θ => by
    simp only [x, Qw, mul_sum, sum_mul, sum_div]; refine sum_congr rfl fun i _ => by ring
  have hg : ∀ θ, Real.exp (-(∑ i, x i θ ^ 2) / 2) = Real.exp (-(π ^ 2 * Vw w / 2) * θ ^ 2) :=
    fun θ => by rw [hsq]; ring_nf
  have hP : ∀ θ, Pw w θ = ∏ i, Real.cos (x i θ) := fun θ => rfl
  have up : ∀ θ ∈ Set.Icc (0 : ℝ) (1 / (2 * (M : ℝ))), 0 ≤ Pw w θ ∧ Pw w θ ≤ Real.exp (-(π ^ 2 * Vw w / 2) * θ ^ 2) := by
    intro θ hθ
    have h := prod_cos_le univ (fun i => x i θ) fun i _ => by
      refine (hx θ hθ.1 i).trans ?_
      have : M * θ ≤ 1 / 2 := by
        have := hθ.2; rw [le_div_iff₀ (by positivity)] at this; linarith
      nlinarith [Real.pi_pos]
    rw [hP, ← hg]; exact h
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have hθ2 : θ ∈ Set.Icc (0 : ℝ) (1 / (2 * (M : ℝ))) := ⟨hθ.1, hθ.2.trans (by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [Real.pi_gt_three])⟩
    obtain ⟨h0, h1⟩ := up θ hθ2
    have h2 := prod_cos_ge univ (fun i => x i θ) fun i _ => by
      refine (hx θ hθ.1 i).trans ?_
      have := hθ.2; rw [le_div_iff₀ (by positivity)] at this; linarith
    rw [← hP, hg, hq] at h2
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · obtain ⟨h0, h1⟩ := up θ hθ
    rw [abs_of_nonneg h0]; exact h1

/-- **The parity window**: for `1/2 − 1/(4M) ≤ θ ≤ 1/2`, each odd weight gives
`|cos(πwθ)| ≤ sin(π/4)`, so `|P_w(θ)| ≤ (√2/2)^j`, `j` the number of odd weights. -/
theorem cos_odd_le (hM : 0 < M) (a : Fin M) (ha : (a : ℕ) % 2 = 0) {θ : ℝ}
    (h1 : 1 / 2 - 1 / (4 * M) ≤ θ) (h2 : θ ≤ 1 / 2) :
    |Real.cos (π * (((a : ℕ) : ℝ) + 1) * θ)| ≤ √2 / 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨k, hk⟩ : ∃ k, (a : ℕ) = 2 * k := ⟨(a : ℕ) / 2, by omega⟩
  set W : ℝ := ((a : ℕ) : ℝ) + 1
  have hW : W = 2 * k + 1 := by simp only [W, hk]; push_cast; ring
  have hWM : W ≤ M := by
    have := a.isLt
    have : ((a : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast this
    exact this
  set δ := 1 / 2 - θ
  have hδ0 : 0 ≤ δ := by simp only [δ]; linarith
  have hδ1 : δ ≤ 1 / (4 * M) := by simp only [δ]; linarith
  have hW0 : 0 < W := by rw [hW]; positivity
  have hy0 : 0 ≤ π * W * δ := by positivity
  have hy1 : π * W * δ ≤ π / 4 := by
    have : W * δ ≤ 1 / 4 := by
      calc W * δ ≤ M * (1 / (4 * M)) := mul_le_mul hWM hδ1 hδ0 hM'.le
        _ = 1 / 4 := by field_simp
    nlinarith [Real.pi_pos]
  have e : π * W * θ = (π / 2 - π * W * δ) + (k : ℕ) * π := by
    simp only [δ]; rw [hW]; ring
  rw [show π * (((a : ℕ) : ℝ) + 1) * θ = π * W * θ from rfl, e, Real.cos_add_nat_mul_pi,
    Real.cos_pi_div_two_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [Real.pi_pos])),
    ← Real.sin_pi_div_four]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hy1

/-- **The parity window**: for `1/2 − 1/(4M) ≤ θ ≤ 1/2`, each odd weight gives
`|cos(πwθ)| ≤ sin(π/4)`, so `|P_w(θ)| ≤ (√2/2)^j`, `j` the number of odd weights. -/
theorem Pw_parity (hM : 0 < M) (w : Fin m → Fin M) {θ : ℝ} (h1 : 1 / 2 - 1 / (4 * M) ≤ θ)
    (h2 : θ ≤ 1 / 2) : |Pw w θ| ≤ (√2 / 2) ^ oddCnt w := by
  unfold Pw oddCnt
  rw [abs_prod, ← prod_filter_mul_prod_filter_not univ (fun i => (w i : ℕ) % 2 = 0)]
  have hA : ∏ i ∈ univ.filter (fun i => (w i : ℕ) % 2 = 0), |Real.cos (π * (((w i : ℕ) : ℝ) + 1) * θ)| ≤
      (√2 / 2) ^ (univ.filter fun i => (w i : ℕ) % 2 = 0).card := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i hi => cos_odd_le hM (w i) (mem_filter.mp hi).2 h1 h2
  have hB : ∏ i ∈ univ.filter (fun i => ¬ (w i : ℕ) % 2 = 0), |Real.cos (π * (((w i : ℕ) : ℝ) + 1) * θ)| ≤ 1 :=
    prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_cos_le_one _
  have hA0 := prod_nonneg fun i (_ : i ∈ univ.filter (fun i => (w i : ℕ) % 2 = 0)) =>
    abs_nonneg (Real.cos (π * (((w i : ℕ) : ℝ) + 1) * θ))
  calc _ ≤ (√2 / 2) ^ (univ.filter fun i => (w i : ℕ) % 2 = 0).card * 1 :=
        mul_le_mul hA hB (prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- `1/(M√(2πm))`, a lower bound for `λ(w)/2^{m+1}` when `V ≤ mM²`. -/
noncomputable def Lmin (M m : ℕ) : ℝ := 1 / (M * √(2 * π * m))

/-- The integral of `|P_w|` over the rest `1/(2M) ≤ θ ≤ 1/2 − 1/(4M)`. -/
noncomputable def Rw (w : Fin m → Fin M) : ℝ :=
  ∫ θ in (1 / (2 * (M : ℝ)))..(1 / 2 - 1 / (4 * (M : ℝ))), |Pw w θ|

theorem forty_pi_le (j : ℕ) (hj : 12 ≤ j) : 40 * π * j ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num; nlinarith [Real.pi_le_four]
  | succ n hn ih =>
    push_cast; rw [pow_succ]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith [Real.pi_pos]

set_option maxHeartbeats 1000000 in
/-- **The count is positive on good weights** (paper §6.6, proof of Theorem LV): if
`V ≥ mM²/80`, at least `m/20` weights are odd, `|u| ≤ M`, and the rest of the circle contributes
`∫|P_w| < 1/(4M√(2πm))`, then `Z(u) > 0`, for `m ≥ 12000`. -/
theorem Z_pos_of_good (hM : 2 ≤ M) (hm : 12000 ≤ m) (w : Fin m → Fin M) (u : ℤ)
    (hpar : ∃ a, 2 * a = Sw w + u) (hu : |(u : ℝ)| ≤ M) (hV : m * (M : ℝ) ^ 2 / 80 ≤ Vw w)
    (hj : m ≤ 20 * oddCnt w) (hR : Rw w < Lmin M m / 4) : 0 < Zc w u := by
  have hM0 : 0 < M := by omega
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hmR : (12000 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hπ := Real.pi_pos
  have hV0 : 0 < Vw w := lt_of_lt_of_le (by positivity) hV
  set V := Vw w
  set Q := Qw w
  set a := π ^ 2 * V / 2 with ha_def
  have ha : 0 < a := by positivity
  set β₁ : ℝ := 1 / (π * M)
  set β : ℝ := 1 / (2 * (M : ℝ))
  set γ : ℝ := 1 / 2 - 1 / (4 * (M : ℝ))
  have hβ₁ : 0 < β₁ := by positivity
  have hβ₁β : β₁ ≤ β := one_div_le_one_div_of_le (by positivity) (by nlinarith [Real.pi_gt_three])
  have hβ0 : 0 ≤ β := by positivity
  have hβγ : β ≤ γ := by
    have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 1 / (4 * (M : ℝ)) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    simp only [β, γ]; linarith
  have hγ : γ ≤ 1 / 2 := by simp only [γ]; have : 0 < 1 / (4 * (M : ℝ)) := by positivity
                            linarith
  set f : ℝ → ℝ := fun θ => Real.cos (π * u * θ) * Pw w θ
  have hfc : Continuous f := by have := continuous_Pw w; fun_prop
  -- the three pieces
  have hsplit : ∫ θ in (0 : ℝ)..(1 / 2), f θ =
      (∫ θ in (0 : ℝ)..β, f θ) + (∫ θ in β..γ, f θ) + ∫ θ in γ..(1 / 2), f θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  -- the major arc
  obtain ⟨hP1, hP2⟩ := Pw_major hM0 w
  have hmaj := major_lb (c := π * u) ha hβ₁ hβ₁β (by unfold Q Qw; positivity : 0 ≤ π ^ 4 * Q / 4)
    (continuous_Pw w) (fun θ hθ => hP1 θ hθ) (fun θ hθ => hP2 θ ⟨hβ₁.le.trans hθ.1, hθ.2⟩)
  set S := √(π / a)
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hS2 : S ^ 2 = π / a := Real.sq_sqrt (by positivity)
  have hu2 : (u : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hu 2; rwa [sq_abs] at this
  have hMV : (M : ℝ) ^ 2 / V ≤ 80 / m := by
    rw [div_le_div_iff₀ hV0 hmp]; linarith
  have e1 : (π * u) ^ 2 * S / (8 * a) ≤ S / 600 := by
    have : (π * u) ^ 2 / (8 * a) ≤ 1 / 600 := by
      rw [ha_def, show (π * u) ^ 2 / (8 * (π ^ 2 * V / 2)) = (u : ℝ) ^ 2 / (4 * V) by field_simp <;> ring]
      have : (u : ℝ) ^ 2 / (4 * V) ≤ (M : ℝ) ^ 2 / V / 4 := by
        rw [div_div, mul_comm V 4]; exact div_le_div_of_nonneg_right hu2 (by positivity)
      have h2 : 80 / (m : ℝ) ≤ 80 / 12000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      linarith
    calc (π * u) ^ 2 * S / (8 * a) = (π * u) ^ 2 / (8 * a) * S := by ring
      _ ≤ 1 / 600 * S := mul_le_mul_of_nonneg_right this hS.le
      _ = S / 600 := by ring
  have e2 : π ^ 4 * Q / 4 * (3 * S / (8 * a ^ 2)) ≤ S / 400 := by
    have hQ := Qw_le w
    have : π ^ 4 * Q / 4 * 3 / (8 * a ^ 2) ≤ 1 / 400 := by
      rw [ha_def, show π ^ 4 * Q / 4 * 3 / (8 * (π ^ 2 * V / 2) ^ 2) = 3 * Q / (8 * V ^ 2) by field_simp <;> ring]
      have h1 : 3 * Q / (8 * V ^ 2) ≤ 3 * ((M : ℝ) ^ 2 / V) / 8 := by
        rw [div_le_iff₀ (by positivity)]
        have : 3 * ((M : ℝ) ^ 2 / V) / 8 * (8 * V ^ 2) = 3 * (M : ℝ) ^ 2 * V := by field_simp
        rw [this]; nlinarith
      have h2 : 80 / (m : ℝ) ≤ 80 / 12000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      linarith
    calc π ^ 4 * Q / 4 * (3 * S / (8 * a ^ 2)) = π ^ 4 * Q / 4 * 3 / (8 * a ^ 2) * S := by ring
      _ ≤ 1 / 400 * S := mul_le_mul_of_nonneg_right this hS.le
      _ = S / 400 := by ring
  have e3 : 3 * (Real.exp (-a * β₁ ^ 2) / (2 * a * β₁)) ≤ S / 24 := by
    set t := V / (M : ℝ) ^ 2
    have ht : 150 ≤ t := by
      simp only [t]; rw [le_div_iff₀ (by positivity)]; nlinarith
    have hab : a * β₁ ^ 2 = t / 2 := by simp only [ha_def, β₁, t]; field_simp
    have hex : Real.exp (-(t / 2)) ≤ 2 / t := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      have := Real.add_one_le_exp (t / 2); linarith
    have h2a : 2 * a * β₁ = π * V / M := by simp only [ha_def, β₁]; field_simp
    rw [neg_mul, hab, h2a]
    have hX : 3 * (2 / t / (π * V / M)) ≤ S / 24 := by
      have eX : 3 * (2 / t / (π * V / M)) = 6 * (M : ℝ) ^ 3 / (π * V ^ 2) := by
        simp only [t]; field_simp <;> ring
      rw [eX]
      have hX0 : 0 ≤ 24 * (6 * (M : ℝ) ^ 3 / (π * V ^ 2)) := by positivity
      have : 24 * (6 * (M : ℝ) ^ 3 / (π * V ^ 2)) ≤ S := by
        rw [show S = √(π / a) from rfl, Real.le_sqrt hX0 (by positivity), ha_def]
        have hV3 : 150 ^ 3 * (M : ℝ) ^ 6 ≤ V ^ 3 := by
          have : 150 * (M : ℝ) ^ 2 ≤ V := by
            have := ht; simp only [t] at this; rwa [le_div_iff₀ (by positivity)] at this
          have h := pow_le_pow_left₀ (by positivity) this 3
          rw [mul_pow, ← pow_mul] at h; exact h
        rw [show (24 * (6 * (M : ℝ) ^ 3 / (π * V ^ 2))) ^ 2 = 20736 * (M : ℝ) ^ 6 / (π ^ 2 * V ^ 4) by ring,
          show π / (π ^ 2 * V / 2) = 2 / (π * V) by field_simp <;> ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have h := mul_le_mul_of_nonneg_left hV3 (by positivity : 0 ≤ 2 * π * V)
        have hM6 : 0 ≤ (M : ℝ) ^ 6 := by positivity
        nlinarith [Real.pi_gt_three, mul_nonneg (mul_nonneg hπ.le hV0.le) hM6]
      linarith
    calc 3 * (Real.exp (-(t / 2)) / (π * V / M)) ≤ 3 * (2 / t / (π * V / M)) := by
          gcongr
      _ ≤ S / 24 := hX
  have hI1 : 3 / 8 * S ≤ ∫ θ in (0 : ℝ)..β, f θ := by
    have := hmaj
    simp only [f]
    linarith
  -- `S/2 ≥ Lmin`
  have hL0 : 0 < Lmin M m := by unfold Lmin; positivity
  have hLS : Lmin M m ≤ S / 2 := by
    have h1 : 0 ≤ Lmin M m := hL0.le
    rw [← pow_le_pow_iff_left₀ h1 (by positivity) (two_ne_zero), div_pow, hS2]
    unfold Lmin
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ha_def, one_pow,
      show π / (π ^ 2 * V / 2) / 2 ^ 2 = 1 / (2 * π * V) by field_simp <;> ring]
    apply one_div_le_one_div_of_le (by positivity)
    have := Vw_le w
    nlinarith
  -- the rest
  have hI2 : |∫ θ in β..γ, f θ| ≤ Rw w := by
    refine (intervalIntegral.abs_integral_le_integral_abs hβγ).trans ?_
    refine intervalIntegral.integral_mono_on hβγ ((by fun_prop : Continuous fun θ => |f θ|).intervalIntegrable _ _)
      ((by have := continuous_Pw w; fun_prop : Continuous fun θ => |Pw w θ|).intervalIntegrable _ _) fun θ _ => ?_
    simp only [f, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)
  -- the parity window
  have hI3 : |∫ θ in γ..(1 / 2), f θ| ≤ Lmin M m / 4 := by
    have hb : ∀ θ ∈ Set.uIoc γ (1 / 2), ‖f θ‖ ≤ (√2 / 2) ^ oddCnt w := by
      intro θ hθ
      rw [Set.uIoc_of_le hγ] at hθ
      rw [Real.norm_eq_abs]
      simp only [f, abs_mul]
      calc |Real.cos (π * u * θ)| * |Pw w θ| ≤ 1 * |Pw w θ| :=
            mul_le_mul_of_nonneg_right (abs_cos_le_one _) (abs_nonneg _)
        _ ≤ (√2 / 2) ^ oddCnt w := by rw [one_mul]; exact Pw_parity hM0 w hθ.1.le hθ.2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [abs_of_nonneg (by linarith), show 1 / 2 - γ = 1 / (4 * (M : ℝ)) by simp only [γ]; ring]
    set j := oddCnt w
    have hj12 : 12 ≤ j := by omega
    have h40 := forty_pi_le j hj12
    have hjm : (m : ℝ) ≤ 20 * j := by exact_mod_cast hj
    have hq : ((√2 / 2) ^ j) ^ 2 = (1 / 2) ^ j := by
      rw [← pow_mul, mul_comm, pow_mul, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hq0 : 0 ≤ (√2 / 2) ^ j := by positivity
    have hkey : (√2 / 2) ^ j * √(2 * π * m) ≤ 1 := by
      rw [← pow_le_pow_iff_left₀ (by positivity) zero_le_one two_ne_zero, mul_pow, hq,
        Real.sq_sqrt (by positivity), one_pow, one_div_pow, div_mul_eq_mul_div, one_mul,
        div_le_one (by positivity)]
      nlinarith
    have hk2 : (√2 / 2) ^ j ≤ 1 / √(2 * π * m) := by rw [le_div_iff₀ (by positivity)]; exact hkey
    calc (√2 / 2) ^ j * (1 / (4 * M)) ≤ 1 / √(2 * π * m) * (1 / (4 * M)) :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ = Lmin M m / 4 := by unfold Lmin; field_simp <;> ring
  have hI : 0 < ∫ θ in (0 : ℝ)..(1 / 2), f θ := by
    rw [hsplit]
    have := (abs_le.mp hI2).1
    have := (abs_le.mp hI3).1
    linarith
  have hZ := Zc_half w u hpar
  have : (0 : ℝ) < Zc w u := by rw [hZ]; positivity
  exact_mod_cast this

end ArcsAlgo.LLT
