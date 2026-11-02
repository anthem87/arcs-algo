module

public import ArcsAlgo.Uniform.Point
public import ArcsAlgo.Uniform.GSum
public import ArcsAlgo.Uniform.Chernoff
public import ArcsAlgo.Uniform.Inv
public import ArcsAlgo.Uniform.FirstId
set_option autoImplicit false

/-!
# The first moment: the typical part and the tail (paper §6.3, Lemma B(1))

With `k₀ = ⌊m/2⌋ − T` and the typical range `k = k₀ + i`, `i ≤ 2T`:

* `typ_sum`: the typical part of `Σ_k C(m,k) p_k(a) p_{m−k}(s−a)` is `2^m B₀ √(π/α)` up to
  `2^m·3808/(σ²m²) + (2T+1)2^m·136/(σ²m²√m) + ρ_T 2^m B₀(√(π/α) + R_T) + 2^m B₀ R_T`;
* `tail_sum`: the rest is at most `2·2^m e^{−2(T−1)²/m}/M²` (Chernoff and (T1)).

All bounds are uniform in `M ≥ 2`; `Asq_le` and `cB_near` are the window estimates behind them.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

theorem muW_sq_le {M : ℕ} (hM : 2 ≤ M) : muW M ^ 2 ≤ 16 * sig2 M := by
  have h := M_sq_le hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have : muW M ≤ M := by unfold muW; linarith
  have h0 : 0 ≤ muW M := by unfold muW; positivity
  nlinarith

/-- In the window, `A₁² + A₂² ≤ σ²(g²m + 32 + 128j²)/2`, uniformly in `M`. -/
theorem Asq_le {M m : ℕ} (hM : 2 ≤ M) {g : ℝ} {s u a : ℤ} (ha : 2 * a = s + u)
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) (x : ℝ) :
    ((a : ℝ) - x * muW M) ^ 2 + (((s - a : ℤ) : ℝ) - ((m : ℝ) - x) * muW M) ^ 2 ≤
      sig2 M * (g ^ 2 * m + 32 + 128 * (x - m / 2) ^ 2) / 2 := by
  have hσ := sig2_pos hM
  have haR : (a : ℝ) = ((s : ℝ) + u) / 2 := by
    have : (2 : ℝ) * a = s + u := by exact_mod_cast ha
    linarith
  have hsaR : ((s - a : ℤ) : ℝ) = ((s : ℝ) - u) / 2 := by push_cast; linarith
  rw [haR, hsaR]
  set t := (s : ℝ) - m * muW M
  set μ := muW M
  have ht : t ^ 2 ≤ g ^ 2 * sig2 M * m := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt (Nat.cast_nonneg _)] at h
    exact h
  have hu2 : (u : ℝ) ^ 2 ≤ 16 * sig2 M := by
    have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
    have := pow_le_pow_left₀ (abs_nonneg _) hu' 2
    rw [sq_abs] at this
    linarith [M_sq_le hM]
  have hμ := muW_sq_le hM
  have e : (((s : ℝ) + u) / 2 - x * μ) ^ 2 + (((s : ℝ) - u) / 2 - ((m : ℝ) - x) * μ) ^ 2 =
      (t ^ 2 + (u - 2 * (x - m / 2) * μ) ^ 2) / 2 := by simp only [t]; ring
  rw [e]
  have h2 : (u - 2 * (x - m / 2) * μ) ^ 2 ≤ 2 * (u : ℝ) ^ 2 + 8 * (x - m / 2) ^ 2 * μ ^ 2 := by
    nlinarith [sq_nonneg ((u : ℝ) + 2 * (x - m / 2) * μ)]
  have h3 : 8 * (x - m / 2) ^ 2 * μ ^ 2 ≤ 8 * (x - m / 2) ^ 2 * (16 * sig2 M) :=
    mul_le_mul_of_nonneg_left hμ (by positivity)
  nlinarith

/-- The freezing error on the typical range, uniform in `M`. -/
noncomputable def rhoT (g : ℝ) (m T : ℕ) : ℝ :=
  (8 * ((T : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 + 2 * ((T : ℝ) + 1) * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / (m : ℝ) ^ 2) *
    exp (2 * ((T : ℝ) + 1) * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / (m : ℝ) ^ 2)

/-- The Riemann and tail error of the Gaussian sum. -/
noncomputable def RT (m T : ℕ) : ℝ := 2 + (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (2 * ((T : ℝ) - 2))

theorem ew2_ge {M : ℕ} : (M : ℝ) ^ 2 / 3 ≤ ew2 M := by
  unfold ew2; nlinarith [(M.cast_nonneg : (0 : ℝ) ≤ M)]

theorem ew2_ge_sig2 {M : ℕ} : sig2 M ≤ ew2 M := by
  rw [ew2_eq]; nlinarith [sq_nonneg (muW M)]

/-- `|μu/(2Ew²)| ≤ 3/2`: the centre is within `3/2` of `m/2`. -/
theorem cB_near {M m : ℕ} (hM : 2 ≤ M) {u : ℤ} (hu : |u| ≤ M) : |cB M m u - m / 2| ≤ 3 / 2 := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hu' : |(u : ℝ)| ≤ M := by exact_mod_cast hu
  have hμ0 : 0 ≤ muW M := by unfold muW; positivity
  have hμ : muW M ≤ M := by unfold muW; linarith
  unfold cB
  rw [add_sub_cancel_left, abs_div, abs_mul, abs_of_nonneg hμ0, abs_of_pos (by positivity : (0 : ℝ) < 2 * ew2 M),
    div_le_iff₀ (by positivity)]
  have := mul_le_mul hμ hu' (abs_nonneg _) (by positivity)
  have := ew2_ge (M := M)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The typical part of the first moment.** With `k₀ = ⌊m/2⌋ − T` and `k = k₀ + i`, `i ≤ 2T`:
`|Σ_i C(m,k) p_k(a) p_{m−k}(s−a) − 2^m B₀ √(π/α)| ≤ 2^m·3808/(σ²m²) + (2T+1) 2^m·136/(σ²m²√m)
  + ρ_T 2^m B₀ (√(π/α) + R_T) + 2^m B₀ R_T`, uniformly in `M`. -/
theorem typ_sum {M m : ℕ} (hM : 2 ≤ M) {g : ℝ} {s u a : ℤ} (ha : 2 * a = s + u)
    (hw : |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ)) (hu : |u| ≤ M) {T : ℕ} (hT : 3 ≤ T)
    (hTm : 4 * T + 8 ≤ m) :
    |∑ i ∈ range (2 * T + 1), (m.choose (m / 2 - T + i) : ℝ) *
        (lawS M (m / 2 - T + i) a * lawS M (m - (m / 2 - T + i)) (s - a)) -
        2 ^ m * B0c M m s u * √(π / alB M m)| ≤
      2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) +
        (2 * T + 1) * (2 ^ m * (136 / (sig2 M * (m : ℝ) ^ 2 * √(m : ℝ)))) +
        rhoT g m T * (2 ^ m * B0c M m s u * (√(π / alB M m) + RT m T)) +
        2 ^ m * B0c M m s u * RT m T := by
  have hσ := sig2_pos hM
  have he : 0 < ew2 M := by unfold ew2; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hT' : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hTm' : 4 * (T : ℝ) + 8 ≤ m := by exact_mod_cast hTm
  set k₀ := m / 2 - T with hk₀
  have hk0a : (m : ℝ) / 2 - T - 1 / 2 ≤ k₀ := by
    have h1 : m ≤ 2 * (m / 2) + 1 := by omega
    have h2 : T ≤ m / 2 := by omega
    have : (k₀ : ℝ) = ((m / 2 : ℕ) : ℝ) - T := by rw [hk₀, Nat.cast_sub h2]
    have h1' : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hk0b : (k₀ : ℝ) ≤ m / 2 - T := by
    have h1 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have h2 : T ≤ m / 2 := by omega
    have : (k₀ : ℝ) = ((m / 2 : ℕ) : ℝ) - T := by rw [hk₀, Nat.cast_sub h2]
    have h1' : 2 * ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    linarith
  set B := B0c M m s u
  have hB0 : 0 ≤ B := by unfold B B0c; positivity
  set α := alB M m
  have hα : 0 < α := by unfold α alB; positivity
  have hα2 : 2 / (m : ℝ) ≤ α := by
    unfold α alB; rw [div_le_div_iff₀ hm0 (by positivity)]
    nlinarith [ew2_ge_sig2 (M := M)]
  set c := cB M m u
  have hc := cB_near (m := m) hM hu
  rw [abs_le] at hc
  -- pointwise bounds
  have hpt : ∀ i ∈ range (2 * T + 1), |(m.choose (k₀ + i) : ℝ) *
      (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) -
        2 ^ m * (B * exp (-(α * (((k₀ + i : ℕ) : ℝ) - c) ^ 2)))| ≤
      (m.choose (k₀ + i) : ℝ) * (3808 / (sig2 M * (m : ℝ) ^ 2)) +
        2 ^ m * (136 / (sig2 M * (m : ℝ) ^ 2 * √(m : ℝ))) +
        rhoT g m T * (2 ^ m * (B * exp (-(α * (((k₀ + i : ℕ) : ℝ) - c) ^ 2)))) := by
    intro i hi
    have hi' : i ≤ 2 * T := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hiR : (i : ℝ) ≤ 2 * T := by exact_mod_cast hi'
    have hkR : (((k₀ + i : ℕ) : ℝ)) = k₀ + i := by push_cast; ring
    have hj1 : -((T : ℝ) + 1) ≤ ((k₀ + i : ℕ) : ℝ) - m / 2 := by
      rw [hkR]; have := (i.cast_nonneg : (0 : ℝ) ≤ i); linarith
    have hj2 : ((k₀ + i : ℕ) : ℝ) - m / 2 ≤ (T : ℝ) + 1 := by rw [hkR]; linarith
    have hk2 : 2 ≤ k₀ + i := by
      have : (2 : ℝ) ≤ ((k₀ + i : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hk3 : k₀ + i + 2 ≤ m := by
      have : ((k₀ + i : ℕ) : ℝ) + 2 ≤ m := by linarith
      exact_mod_cast this
    have hk4 : m ≤ 4 * (k₀ + i) := by
      have : (m : ℝ) ≤ 4 * ((k₀ + i : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hk5 : 4 * (k₀ + i) ≤ 3 * m := by
      have : 4 * ((k₀ + i : ℕ) : ℝ) ≤ 3 * m := by linarith
      exact_mod_cast this
    have h := term_approx hM hk2 hk3 hk4 hk5 s u a ha
    refine h.trans ?_
    gcongr
    -- the freezing factor is at most ρ_T
    have hA := Asq_le hM ha hw hu ((k₀ + i : ℕ) : ℝ)
    have hj : |((k₀ + i : ℕ) : ℝ) - m / 2| ≤ (T : ℝ) + 1 := abs_le.mpr ⟨hj1, hj2⟩
    have hjsq : (((k₀ + i : ℕ) : ℝ) - m / 2) ^ 2 ≤ ((T : ℝ) + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hj 2
    set Asq := ((a : ℝ) - ((k₀ + i : ℕ) : ℝ) * muW M) ^ 2 +
      (((s - a : ℤ) : ℝ) - ((m : ℝ) - ((k₀ + i : ℕ) : ℝ)) * muW M) ^ 2
    have hE : 4 * |((k₀ + i : ℕ) : ℝ) - m / 2| * Asq / (sig2 M * m ^ 2) ≤
        2 * ((T : ℝ) + 1) * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / (m : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hA' : Asq ≤ sig2 M * (g ^ 2 * m + 32 + 128 * ((T : ℝ) + 1) ^ 2) / 2 := by
        refine hA.trans ?_
        gcongr
      have hA0 : 0 ≤ Asq := by positivity
      have := mul_le_mul hj hA' hA0 (by positivity)
      have hσm : 0 < sig2 M * (m : ℝ) ^ 2 := by positivity
      nlinarith
    unfold rhoT
    gcongr
  -- the Gaussian sum
  set S := ∑ i ∈ range (2 * T + 1), exp (-(α * (((k₀ + i : ℕ) : ℝ) - c) ^ 2))
  have hS : |S - √(π / α)| ≤ RT m T := by
    have hd1 : (T : ℝ) - 2 ≤ -((k₀ : ℝ) - c) := by linarith
    have hd2 : (T : ℝ) - 2 ≤ (k₀ : ℝ) - c + ((2 * T : ℕ) : ℝ) := by push_cast; linarith
    have hT2 : (0 : ℝ) < (T : ℝ) - 2 := by linarith
    have h := gauss_sum hα ((k₀ : ℝ) - c) (2 * T) (by linarith) (by linarith)
    have e : ∑ i ∈ range (2 * T + 1), exp (-α * ((k₀ : ℝ) - c + i) ^ 2) = S := by
      refine sum_congr rfl fun i _ => ?_; push_cast; ring_nf
    rw [e] at h
    refine h.trans ?_
    have tail : ∀ d : ℝ, (T : ℝ) - 2 ≤ d →
        exp (-α * d ^ 2) / (2 * α * d) ≤ (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (4 * ((T : ℝ) - 2)) := by
      intro d hd
      have hd0 : 0 < d := by linarith
      have h1 : exp (-α * d ^ 2) ≤ exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) := by
        apply exp_le_exp.mpr
        have : 2 / (m : ℝ) * ((T : ℝ) - 2) ^ 2 ≤ α * d ^ 2 :=
          mul_le_mul hα2 (pow_le_pow_left₀ hT2.le hd 2) (by positivity) hα.le
        have e2 : 2 * ((T : ℝ) - 2) ^ 2 / m = 2 / (m : ℝ) * ((T : ℝ) - 2) ^ 2 := by ring
        linarith
      have h2 : 4 * ((T : ℝ) - 2) / m ≤ 2 * α * d := by
        have := mul_le_mul hα2 hd hT2.le hα.le
        have e2 : 4 * ((T : ℝ) - 2) / m = 2 * (2 / (m : ℝ) * ((T : ℝ) - 2)) := by ring
        linarith
      calc exp (-α * d ^ 2) / (2 * α * d) ≤ exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (4 * ((T : ℝ) - 2) / m) :=
            div_le_div₀ (exp_pos _).le h1 (by positivity) h2
        _ = _ := by field_simp
    have t1 := tail _ hd1
    have t2 := tail _ hd2
    unfold RT
    have : (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (4 * ((T : ℝ) - 2)) +
        (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (4 * ((T : ℝ) - 2)) =
        (m : ℝ) * exp (-(2 * ((T : ℝ) - 2) ^ 2 / m)) / (2 * ((T : ℝ) - 2)) := by field_simp; ring
    linarith
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => (exp_pos _).le
  -- the sum of the binomial coefficients
  have hC : ∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) ≤ 2 ^ m := by
    have h1 : ∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) =
        ∑ k ∈ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) := by
      rw [sum_Ico_eq_sum_range]; simp
    have h2 : Ico k₀ (k₀ + (2 * T + 1)) ⊆ range (m + 1) := by
      intro k hk; rw [mem_Ico] at hk; rw [mem_range]
      have : (k₀ : ℝ) + 2 * T ≤ m := by linarith
      have : k₀ + 2 * T ≤ m := by exact_mod_cast this
      omega
    rw [h1]
    calc ∑ k ∈ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) ≤ ∑ k ∈ range (m + 1), (m.choose k : ℝ) :=
          sum_le_sum_of_subset_of_nonneg h2 fun _ _ _ => by positivity
      _ = 2 ^ m := by exact_mod_cast Nat.sum_range_choose m
  have hρ0 : 0 ≤ rhoT g m T := by unfold rhoT; positivity
  have hsum := abs_sum_le_sum_abs (fun i => (m.choose (k₀ + i) : ℝ) *
      (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) -
        2 ^ m * (B * exp (-(α * (((k₀ + i : ℕ) : ℝ) - c) ^ 2)))) (range (2 * T + 1))
  have hsum2 := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
    ← mul_sum, ← mul_sum] at hsum2
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  have hfin : ∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) *
      (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) - 2 ^ m * B * √(π / α) =
      (∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) *
        (lawS M (k₀ + i) a * lawS M (m - (k₀ + i)) (s - a)) - 2 ^ m * (B * S)) +
        2 ^ m * B * (S - √(π / α)) := by ring
  rw [hfin]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ m * B)]
  have h3 : (3808 / (sig2 M * (m : ℝ) ^ 2)) * ∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ) ≤
      2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hC (by positivity)
  have h4 : rhoT g m T * (2 ^ m * (B * S)) ≤ rhoT g m T * (2 ^ m * B * (√(π / α) + RT m T)) := by
    apply mul_le_mul_of_nonneg_left _ hρ0
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [(abs_le.mp hS).2]
  have h5 : 2 ^ m * B * |S - √(π / α)| ≤ 2 ^ m * B * RT m T :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have e6 : ((2 * T + 1 : ℕ) : ℝ) = 2 * (T : ℝ) + 1 := by push_cast; ring
  rw [e6] at hsum2
  have hSd : ∑ i ∈ range (2 * T + 1), exp (-(α * (((k₀ + i : ℕ) : ℝ) - c) ^ 2)) = S := rfl
  rw [hSd] at hsum hsum2
  have h3' : (∑ i ∈ range (2 * T + 1), (m.choose (k₀ + i) : ℝ)) * (3808 / (sig2 M * (m : ℝ) ^ 2)) ≤
      2 ^ m * (3808 / (sig2 M * (m : ℝ) ^ 2)) := by rw [mul_comm]; exact h3
  have h4' : rhoT g m T * (2 ^ m * (B * S)) ≤ rhoT g m T * (2 ^ m * B * (√(π / α) + RT m T)) := h4
  linarith [hsum, hsum2, h3', h4', h5]

theorem pp_le_inv {M m k : ℕ} (hM : 2 ≤ M) (hk : k ≤ m) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    lawS M k a * lawS M (m - k) b ≤ 1 / (M : ℝ) ^ 2 := by
  have hM0 : 0 < M := by omega
  have hp1 : 0 ≤ lawS M k a := by unfold lawS; positivity
  have hp2 : 0 ≤ lawS M (m - k) b := by unfold lawS; positivity
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; rw [lawS_zero_ne ha]; simp
  rcases Nat.eq_zero_or_pos (m - k) with h1 | h1
  · rw [h1, lawS_zero_ne hb]; simp
  have e1 := lawS_le_inv (n := k - 1) hM0 a
  have e2 := lawS_le_inv (n := m - k - 1) hM0 b
  rw [Nat.sub_add_cancel h0] at e1
  rw [Nat.sub_add_cancel h1] at e2
  calc lawS M k a * lawS M (m - k) b ≤ 1 / M * (1 / M) := mul_le_mul e1 e2 hp2 (by positivity)
    _ = 1 / (M : ℝ) ^ 2 := by ring

/-- **The atypical part of the first moment**, through Chernoff and (T1). -/
theorem tail_sum {M m : ℕ} (hM : 2 ≤ M) {s a : ℤ} (ha : a ≠ 0) (hsa : s - a ≠ 0) {T : ℕ}
    (hT : 3 ≤ T) (hTm : 4 * T + 8 ≤ m) :
    ∑ k ∈ range (m + 1) \ Ico (m / 2 - T) (m / 2 - T + (2 * T + 1)), (m.choose k : ℝ) *
        (lawS M k a * lawS M (m - k) (s - a)) ≤
      2 * 2 ^ m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) / (M : ℝ) ^ 2 := by
  have hm0 : 0 < m := by omega
  set k₀ := m / 2 - T
  have hsub : range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)) ⊆
      (range (m + 1)).filter (fun k : ℕ => ((T : ℝ) - 1) ≤ |(k : ℝ) - m / 2|) := by
    intro k hk
    rw [mem_sdiff, mem_Ico] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine mem_filter.mpr ⟨hk1, ?_⟩
    have h1 : m ≤ 2 * (m / 2) + 1 := by omega
    have h2 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have h1' : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h2' : 2 * ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast h2
    have hT2 : T ≤ m / 2 := by omega
    rcases Nat.lt_or_ge k k₀ with h | h
    · have : k + 1 ≤ m / 2 - T := h
      have : (k : ℝ) + 1 + T ≤ ((m / 2 : ℕ) : ℝ) := by
        have : k + 1 + T ≤ m / 2 := by omega
        exact_mod_cast this
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have h' : k₀ + (2 * T + 1) ≤ k := by
        by_contra hc; exact hk2 ⟨h, by omega⟩
      have : ((m / 2 : ℕ) : ℝ) + T + 1 ≤ k := by
        have : m / 2 + T + 1 ≤ k := by omega
        exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; linarith
  have hpt : ∀ k ∈ range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) *
      (lawS M k a * lawS M (m - k) (s - a)) ≤ (m.choose k : ℝ) * (1 / (M : ℝ) ^ 2) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp (mem_sdiff.mp hk).1)
    exact mul_le_mul_of_nonneg_left (pp_le_inv hM hkm ha hsa) (by positivity)
  have hT1 : (0 : ℝ) ≤ (T : ℝ) - 1 := by
    have : (3 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  calc _ ≤ ∑ k ∈ range (m + 1) \ Ico k₀ (k₀ + (2 * T + 1)), (m.choose k : ℝ) * (1 / (M : ℝ) ^ 2) :=
        sum_le_sum hpt
    _ ≤ ∑ k ∈ (range (m + 1)).filter (fun k : ℕ => ((T : ℝ) - 1) ≤ |(k : ℝ) - m / 2|),
          (m.choose k : ℝ) * (1 / (M : ℝ) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ k ∈ (range (m + 1)).filter (fun k : ℕ => ((T : ℝ) - 1) ≤ |(k : ℝ) - m / 2|),
          (m.choose k : ℝ)) * (1 / (M : ℝ) ^ 2) := by rw [sum_mul]
    _ ≤ 2 * 2 ^ m * exp (-(2 * ((T : ℝ) - 1) ^ 2 / m)) * (1 / (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (binom_tail hm0 hT1) (by positivity)
    _ = _ := by ring

end ArcsAlgo.LLT
