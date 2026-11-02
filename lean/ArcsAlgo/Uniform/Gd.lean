module

public import ArcsAlgo.Uniform.GSum
public import ArcsAlgo.Uniform.G1
set_option autoImplicit false

/-!
# Normal densities (paper §6.3, proof of Lemma B(2))

* `gd ν v x` is the normal density `φ(x; ν, v)`; `gaussB_eq_gd`: `g_k(v) = φ(v; kμ, kσ²)`.
* `gd_mul`: `φ(c; ν₁, v₁) φ(a − c; ν₂, v₂) = φ(a; ν₁ + ν₂, v₁ + v₂) φ(c; c*, v₁v₂/(v₁ + v₂))`.
* `gsum_le`, `gd_sum_le`: over any finite set of integers, `Σ_c φ(c; ν, w) ≤ 1 + 2/√(2πw)`.
* `gd_ratio`: for `0 < v ≤ V`, `φ(a; ν, v) ≤ √(V/v) e^{|ν − ν′||a − ν′|/V} φ(a; ν′, V)`.
-/

open Finset MeasureTheory intervalIntegral Set Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- The normal density `φ(x; ν, v) = e^{−(x−ν)²/(2v)}/√(2πv)`. -/
noncomputable def gd (ν v x : ℝ) : ℝ := exp (-((x - ν) ^ 2 / (2 * v))) / √(2 * π * v)

theorem gd_nonneg (ν v x : ℝ) : 0 ≤ gd ν v x := by unfold gd; positivity

theorem gaussB_eq_gd {M : ℕ} (hM : 2 ≤ M) {k : ℕ} (hk : 1 ≤ k) (v : ℤ) :
    gaussB M k v = gd (k * muW M) (k * sig2 M) v := by
  have hσ := sig2_pos hM
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold gaussB gd zB tB
  have hz : (((v : ℝ) - k * muW M) / (√(sig2 M) * √(k : ℝ))) ^ 2 =
      ((v : ℝ) - k * muW M) ^ 2 / (k * sig2 M) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hk0.le]; ring
  rw [hz, show 2 * π * (k * sig2 M) = 2 * π * k * sig2 M by ring,
    show ((v : ℝ) - k * muW M) ^ 2 / (k * sig2 M) / 2 = ((v : ℝ) - k * muW M) ^ 2 / (2 * (k * sig2 M)) by
      ring, one_div, div_eq_inv_mul (rexp _)]

/-- **Product of two normal densities**:
`φ(c; ν₁, v₁) φ(a − c; ν₂, v₂) = φ(a; ν₁ + ν₂, v₁ + v₂) φ(c; c*, v₁v₂/(v₁ + v₂))`. -/
theorem gd_mul {ν₁ ν₂ v₁ v₂ : ℝ} (h₁ : 0 < v₁) (h₂ : 0 < v₂) (a c : ℝ) :
    gd ν₁ v₁ c * gd ν₂ v₂ (a - c) = gd (ν₁ + ν₂) (v₁ + v₂) a *
      gd ((ν₁ * v₂ + (a - ν₂) * v₁) / (v₁ + v₂)) (v₁ * v₂ / (v₁ + v₂)) c := by
  have h12 : 0 < v₁ + v₂ := by linarith
  unfold gd
  rw [div_mul_div_comm, div_mul_div_comm, ← Real.exp_add, ← Real.exp_add,
    ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  · congr 1; field_simp; ring
  · congr 1; field_simp

/-- `Σ_{c ∈ I} e^{−A(c − ν)²} ≤ √(π/A) + 2` for every finite set of integers `I`. -/
theorem gsum_le {A : ℝ} (hA : 0 < A) (ν : ℝ) (I : Finset ℤ) :
    ∑ c ∈ I, exp (-A * ((c : ℝ) - ν) ^ 2) ≤ √(π / A) + 2 := by
  set f : ℝ → ℝ := fun y => exp (-A * (y - ν) ^ 2)
  have hf : Continuous f := by fun_prop
  have hf0 : ∀ y, 0 ≤ f y := fun y => (exp_pos _).le
  have hf1 : ∀ y, f y ≤ 1 := fun y => exp_le_one_iff.mpr (by nlinarith [sq_nonneg (y - ν)])
  have hmono : MonotoneOn f (Iic ν) := by
    intro x hx y hy hxy
    apply exp_le_exp.mpr
    have : (y - ν) ^ 2 ≤ (x - ν) ^ 2 := by nlinarith [mem_Iic.mp hx, mem_Iic.mp hy]
    nlinarith
  have hanti : AntitoneOn f (Ici ν) := by
    intro x hx y hy hxy
    apply exp_le_exp.mpr
    have : (x - ν) ^ 2 ≤ (y - ν) ^ 2 := by nlinarith [mem_Ici.mp hx, mem_Ici.mp hy]
    nlinarith
  -- a lattice segment containing `I` and `ν`
  set R : ℕ := (∑ c ∈ I, c.natAbs) + (⌊ν⌋).natAbs + 1
  set L : ℤ := ⌊ν⌋ - R
  set N : ℕ := 2 * R
  have hRc : ∀ c ∈ I, (c.natAbs : ℤ) ≤ (∑ c ∈ I, c.natAbs : ℕ) := fun c hc => by
    exact_mod_cast single_le_sum (f := fun c : ℤ => c.natAbs) (fun _ _ => Nat.zero_le _) hc
  have hsub : I ⊆ (range (N + 1)).image (fun i : ℕ => L + i) := by
    intro c hc
    have h1 := hRc c hc
    have h2 : |c| ≤ (∑ c ∈ I, c.natAbs : ℕ) := by rw [Int.abs_eq_natAbs]; exact h1
    have h3 : |⌊ν⌋| = ((⌊ν⌋).natAbs : ℤ) := Int.abs_eq_natAbs _
    have hR' : (R : ℤ) = (∑ c ∈ I, c.natAbs : ℕ) + ((⌊ν⌋).natAbs : ℤ) + 1 := by
      simp only [R]; push_cast; ring
    rw [Finset.mem_image]
    refine ⟨(c - L).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have : c - L ≤ 2 * R := by
        simp only [L]; rw [abs_le] at h2; have := abs_le.mp (le_of_eq h3); omega
      omega
    · have : 0 ≤ c - L := by
        simp only [L]; rw [abs_le] at h2; have := abs_le.mp (le_of_eq h3); omega
      omega
  have hinj : Set.InjOn (fun i : ℕ => L + i) ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    intro i _ j _ h; simp at h; exact_mod_cast h
  calc ∑ c ∈ I, exp (-A * ((c : ℝ) - ν) ^ 2)
      ≤ ∑ c ∈ (range (N + 1)).image (fun i : ℕ => L + i), exp (-A * ((c : ℝ) - ν) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (exp_pos _).le
    _ = ∑ i ∈ range (N + 1), f ((L : ℝ) + i) := by
        rw [sum_image hinj]; simp [f]
    _ ≤ (∫ t in (L : ℝ)..(L : ℝ) + N, f t) + 2 := by
        have hL : (L : ℝ) ≤ ν := by
          simp only [L]; push_cast
          have := Int.floor_le ν; have : (0 : ℝ) ≤ R := Nat.cast_nonneg _; linarith
        have hLN : ν ≤ (L : ℝ) + N := by
          simp only [L, N]; push_cast
          have := Int.lt_floor_add_one ν
          have : (1 : ℝ) ≤ R := by simp only [R]; norm_cast; omega
          linarith
        have := sum_unimodal hf hf0 hf1 hmono hanti (L : ℝ) N hL hLN
        rw [abs_le] at this; linarith [this.2]
    _ ≤ √(π / A) + 2 := by
        have hint : Integrable f := by
          have := (integrable_exp_neg_mul_sq hA).comp_sub_right ν
          simpa [f] using this
        have htot : ∫ y, f y = √(π / A) := by
          have := integral_sub_right_eq_self (μ := volume) (fun y => exp (-A * y ^ 2)) ν
          simp only [f]; rw [this, integral_gaussian]
        have hle : ∫ t in (L : ℝ)..(L : ℝ) + N, f t ≤ ∫ y, f y := by
          rw [intervalIntegral.integral_of_le (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith)]
          exact setIntegral_le_integral hint (Filter.Eventually.of_forall hf0)
        linarith

/-- `Σ_{c ∈ I} φ(c; ν, w) ≤ 1 + 2/√(2πw)`. -/
theorem gd_sum_le {w : ℝ} (hw : 0 < w) (ν : ℝ) (I : Finset ℤ) :
    ∑ c ∈ I, gd ν w c ≤ 1 + 2 / √(2 * π * w) := by
  have hπ := pi_pos
  have h := gsum_le (A := 1 / (2 * w)) (by positivity) ν I
  have e : ∀ c : ℤ, gd ν w c = exp (-(1 / (2 * w)) * ((c : ℝ) - ν) ^ 2) / √(2 * π * w) := by
    intro c; unfold gd; congr 2; ring
  simp only [e]
  rw [← sum_div]
  have hs : 0 < √(2 * π * w) := Real.sqrt_pos.mpr (by positivity)
  have e2 : √(π / (1 / (2 * w))) = √(2 * π * w) := by congr 1; field_simp
  rw [e2] at h
  calc (∑ c ∈ I, exp (-(1 / (2 * w)) * ((c : ℝ) - ν) ^ 2)) / √(2 * π * w)
      ≤ (√(2 * π * w) + 2) / √(2 * π * w) := div_le_div_of_nonneg_right h hs.le
    _ = 1 + 2 / √(2 * π * w) := by field_simp

/-- **Comparing two normal densities at a point**: for `0 < v ≤ V`,
`φ(a; ν, v) ≤ √(V/v) e^{|ν − ν′||a − ν′|/V} φ(a; ν′, V)`. -/
theorem gd_ratio {ν ν' v V : ℝ} (hv : 0 < v) (hvV : v ≤ V) (a : ℝ) :
    gd ν v a ≤ √(V / v) * exp (|ν - ν'| * |a - ν'| / V) * gd ν' V a := by
  have hπ := pi_pos
  have hV : 0 < V := lt_of_lt_of_le hv hvV
  unfold gd
  have hsv : √(2 * π * V) = √(V / v) * √(2 * π * v) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have hs : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  have hr : 0 < √(V / v) := Real.sqrt_pos.mpr (by positivity)
  rw [hsv]
  rw [show √(V / v) * exp (|ν - ν'| * |a - ν'| / V) *
      (exp (-((a - ν') ^ 2 / (2 * V))) / (√(V / v) * √(2 * π * v))) =
      exp (|ν - ν'| * |a - ν'| / V) * exp (-((a - ν') ^ 2 / (2 * V))) / √(2 * π * v) by
    field_simp]
  apply div_le_div_of_nonneg_right _ hs.le
  rw [← exp_add]
  apply exp_le_exp.mpr
  have h1 : (a - ν) ^ 2 / (2 * V) ≤ (a - ν) ^ 2 / (2 * v) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have h2 : (a - ν') ^ 2 - (a - ν) ^ 2 ≤ 2 * (|ν - ν'| * |a - ν'|) := by
    have e : (a - ν') ^ 2 - (a - ν) ^ 2 = 2 * ((ν - ν') * (a - ν')) - (ν - ν') ^ 2 := by ring
    rw [e, ← abs_mul]
    nlinarith [le_abs_self ((ν - ν') * (a - ν')), sq_nonneg (ν - ν')]
  have h3 : ((a - ν') ^ 2 - (a - ν) ^ 2) / (2 * V) ≤ |ν - ν'| * |a - ν'| / V := by
    rw [div_le_div_iff₀ (by positivity) hV]; nlinarith
  have : ((a - ν') ^ 2 - (a - ν) ^ 2) / (2 * V) = (a - ν') ^ 2 / (2 * V) - (a - ν) ^ 2 / (2 * V) := by
    ring
  linarith

end ArcsAlgo.LLT
