module

public import ArcsAlgo.Uniform.Gd
public import ArcsAlgo.Uniform.Pair
public import ArcsAlgo.Uniform.Unif
set_option autoImplicit false

/-!
# The four classes with Lemma B0′ (paper §6.3, proof of Lemma B(2))

* `four_gauss`: the product of the four normal factors in `c` is
  `φ(a; k₁μ, k₁σ²) φ(s − a; (B + D)μ, (B + D)σ²) φ(a; ν, v)` times a normal density in `c`.
* `w3_ge`: that density in `c` has variance `≥ σ²n/4` when every class has size `≥ n`.
* `quad_err`: Lemma B0′ applied to each of the four independent class sums changes
  `Σ_c Pr(S_C = c) Pr(S_A = a − c) Pr(S_B = a − c) Pr(S_D = s − 2a + c)` by at most
  `3162/(σ³n^{5/2})`, uniformly in `M ≥ 2`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

/-- **Four normal factors in `c`**: `φ_C(c) φ_A(a − c) φ_B(a − c) φ_D(s − 2a + c)` is
`φ(a; k₁μ, k₁σ²) φ(s − a; (B + D)μ, (B + D)σ²) φ(a; ν, v)` times a normal density in `c`, with
`ν = Ca/(C + A) + B(s − a)/(B + D)`, `v = σ²(CA/(C + A) + BD/(B + D))`. -/
theorem four_gauss {A B C D σ2 : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hσ : 0 < σ2) (μ a s : ℝ) : ∃ c3 : ℝ, ∀ c : ℝ,
    gd (C * μ) (C * σ2) c * gd (A * μ) (A * σ2) (a - c) * gd (B * μ) (B * σ2) (a - c) *
      gd (D * μ) (D * σ2) (s - 2 * a + c) =
    gd ((C + A) * μ) ((C + A) * σ2) a * gd ((B + D) * μ) ((B + D) * σ2) (s - a) *
      gd (C * a / (C + A) + B * (s - a) / (B + D)) (σ2 * (C * A / (C + A) + B * D / (B + D))) a *
      gd c3 ((σ2 * (C * A / (C + A))) * (σ2 * (B * D / (B + D))) /
        (σ2 * (C * A / (C + A)) + σ2 * (B * D / (B + D)))) c := by
  have e1 := fun c => gd_mul (ν₁ := C * μ) (ν₂ := A * μ) (mul_pos hC hσ) (mul_pos hA hσ) a c
  have e2 := fun c => gd_mul (ν₁ := B * μ) (ν₂ := D * μ) (mul_pos hB hσ) (mul_pos hD hσ) (s - a) (a - c)
  have hw1 : C * σ2 * (A * σ2) / (C * σ2 + A * σ2) = σ2 * (C * A / (C + A)) := by
    field_simp
  have hw2 : B * σ2 * (D * σ2) / (B * σ2 + D * σ2) = σ2 * (B * D / (B + D)) := by
    field_simp
  have hw1p : 0 < σ2 * (C * A / (C + A)) := by positivity
  have hw2p : 0 < σ2 * (B * D / (B + D)) := by positivity
  set ν₁ := (C * μ * (A * σ2) + (a - A * μ) * (C * σ2)) / (C * σ2 + A * σ2)
  set ν₂ := (B * μ * (D * σ2) + (s - a - D * μ) * (B * σ2)) / (B * σ2 + D * σ2)
  have hν : ν₁ + ν₂ = C * a / (C + A) + B * (s - a) / (B + D) := by
    simp only [ν₁, ν₂]; field_simp; ring
  have hv : σ2 * (C * A / (C + A)) + σ2 * (B * D / (B + D)) =
      σ2 * (C * A / (C + A) + B * D / (B + D)) := by ring
  refine ⟨(ν₁ * (σ2 * (B * D / (B + D))) + (a - ν₂) * (σ2 * (C * A / (C + A)))) /
    (σ2 * (C * A / (C + A)) + σ2 * (B * D / (B + D))), fun c => ?_⟩
  have e3 := gd_mul (ν₁ := ν₁) (ν₂ := ν₂) hw1p hw2p a c
  have h4 : s - 2 * a + c = s - a - (a - c) := by ring
  rw [h4]
  rw [hw1] at e1; rw [hw2] at e2
  calc gd (C * μ) (C * σ2) c * gd (A * μ) (A * σ2) (a - c) * gd (B * μ) (B * σ2) (a - c) *
        gd (D * μ) (D * σ2) (s - a - (a - c))
      = (gd (C * μ) (C * σ2) c * gd (A * μ) (A * σ2) (a - c)) *
        (gd (B * μ) (B * σ2) (a - c) * gd (D * μ) (D * σ2) (s - a - (a - c))) := by ring
    _ = (gd (C * μ + A * μ) (C * σ2 + A * σ2) a * gd ν₁ (σ2 * (C * A / (C + A))) c) *
        (gd (B * μ + D * μ) (B * σ2 + D * σ2) (s - a) * gd ν₂ (σ2 * (B * D / (B + D))) (a - c)) := by
        rw [e1 c, e2 c]
    _ = gd (C * μ + A * μ) (C * σ2 + A * σ2) a * gd (B * μ + D * μ) (B * σ2 + D * σ2) (s - a) *
        (gd ν₁ (σ2 * (C * A / (C + A))) c * gd ν₂ (σ2 * (B * D / (B + D))) (a - c)) := by ring
    _ = _ := by
        rw [e3, hν, hv, show C * μ + A * μ = (C + A) * μ by ring, show C * σ2 + A * σ2 = (C + A) * σ2 by ring,
          show B * μ + D * μ = (B + D) * μ by ring, show B * σ2 + D * σ2 = (B + D) * σ2 by ring]
        ring

/-- The variance of the normal density in `c` is at least `σ²n/4` when all classes are `≥ n`. -/
theorem w3_ge {A B C D σ2 n : ℝ} (hn : 0 < n) (hA : n ≤ A) (hB : n ≤ B) (hC : n ≤ C) (hD : n ≤ D)
    (hσ : 0 < σ2) :
    σ2 * n / 4 ≤ (σ2 * (C * A / (C + A))) * (σ2 * (B * D / (B + D))) /
        (σ2 * (C * A / (C + A)) + σ2 * (B * D / (B + D))) := by
  have hh : ∀ {x y : ℝ}, n ≤ x → n ≤ y → n / 2 ≤ x * y / (x + y) := by
    intro x y hx hy
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have h1 := hh hC hA
  have h2 := hh hB hD
  set p := σ2 * (C * A / (C + A))
  set q := σ2 * (B * D / (B + D))
  have hp : σ2 * n / 2 ≤ p := by simp only [p]; nlinarith
  have hq : σ2 * n / 2 ≤ q := by simp only [q]; nlinarith
  have hp0 : 0 < p := by have : 0 < σ2 * n := by positivity
                         linarith
  have hq0 : 0 < q := by have : 0 < σ2 * n := by positivity
                         linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Telescoping four factors. -/
theorem tele4 {p1 p2 p3 p4 g1 g2 g3 g4 X Y : ℝ} (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3)
    (he1 : |p1 - g1| ≤ 17 * Y) (he2 : |p2 - g2| ≤ 17 * Y) (he3 : |p3 - g3| ≤ 17 * Y)
    (he4 : |p4 - g4| ≤ 17 * Y) (hq2 : p2 ≤ 13 * X) (hq3 : p3 ≤ 13 * X)
    (hG1 : g1 ≤ X) (hG2 : g2 ≤ X) (hG3 : g3 ≤ X) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    |p1 * p2 * p3 * p4 - g1 * g2 * g3 * g4| ≤ 3111 * (X ^ 2 * Y) * p4 + 17 * (X ^ 2 * Y) * g1 := by
  have e : p1 * p2 * p3 * p4 - g1 * g2 * g3 * g4 = (p1 - g1) * p2 * p3 * p4 + g1 * (p2 - g2) * p3 * p4 +
      g1 * g2 * (p3 - g3) * p4 + g1 * g2 * g3 * (p4 - g4) := by ring
  rw [e]
  have t1 : |(p1 - g1) * p2 * p3 * p4| ≤ 17 * Y * (13 * X) * (13 * X) * p4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp2, abs_of_nonneg hp3, abs_of_nonneg hp4]
    gcongr
  have t2 : |g1 * (p2 - g2) * p3 * p4| ≤ X * (17 * Y) * (13 * X) * p4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hp3, abs_of_nonneg hp4]
    gcongr
  have t3 : |g1 * g2 * (p3 - g3) * p4| ≤ X * X * (17 * Y) * p4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_nonneg hp4]
    gcongr
  have t4 : |g1 * g2 * g3 * (p4 - g4)| ≤ g1 * X * X * (17 * Y) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_nonneg hg3]
    gcongr
  have h4 : ∀ w1 w2 w3 w4 : ℝ, |w1 + w2 + w3 + w4| ≤ |w1| + |w2| + |w3| + |w4| := by
    intro w1 w2 w3 w4
    calc |w1 + w2 + w3 + w4| ≤ |w1 + w2 + w3| + |w4| := abs_add_le _ _
      _ ≤ |w1 + w2| + |w3| + |w4| := by gcongr; exact abs_add_le _ _
      _ ≤ |w1| + |w2| + |w3| + |w4| := by gcongr; exact abs_add_le _ _
  have := h4 ((p1 - g1) * p2 * p3 * p4) (g1 * (p2 - g2) * p3 * p4) (g1 * g2 * (p3 - g3) * p4)
    (g1 * g2 * g3 * (p4 - g4))
  linarith

end ArcsAlgo.LLT

namespace ArcsAlgo.LLT

theorem sig2_ge {M : ℕ} (hM : 2 ≤ M) : 1 / 4 ≤ sig2 M := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sig2; nlinarith

theorem eB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) {n : ℝ} (hn : 0 < n) (hnk : n ≤ k) (v : ℤ) :
    |lawS M k v - gaussB M k v| ≤ 17 * (1 / (√(sig2 M) * (n * √n))) := by
  have hσ := sig2_pos hM
  have h := lemmaB0'_gauss hM hk v
  have hC := CB_le hM hk
  have hs : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
  have h1 : n * √n ≤ k * √(k : ℝ) := mul_le_mul hnk (Real.sqrt_le_sqrt hnk) (Real.sqrt_nonneg _)
    (by positivity)
  refine h.trans ?_
  rw [mul_one_div]
  calc CB M k / (√(sig2 M) * (k * √(k : ℝ))) ≤ 17 / (√(sig2 M) * (k * √(k : ℝ))) := by gcongr
    _ ≤ 17 / (√(sig2 M) * (n * √n)) := by gcongr

theorem pB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) {n : ℝ} (hn : 0 < n) (hnk : n ≤ k) (v : ℤ) :
    lawS M k v ≤ 13 * (1 / (√(sig2 M) * √n)) := by
  have hσ := sig2_pos hM
  refine (lawS_le_max hM hk v).trans ?_
  rw [mul_one_div]; gcongr

theorem gB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 1 ≤ k) {n : ℝ} (hn : 0 < n) (hnk : n ≤ k) (v : ℤ) :
    gaussB M k v ≤ 1 / (√(sig2 M) * √n) := by
  have hσ := sig2_pos hM
  refine (gaussB_le hM hk v).trans ?_
  gcongr

theorem gaussB_nonneg (M k : ℕ) (v : ℤ) : 0 ≤ gaussB M k v := by unfold gaussB; positivity

/-- `Σ_c g_k(c) ≤ 3` for `k ≥ 2`. -/
theorem sum_gaussB_le {M k : ℕ} (hM : 2 ≤ M) (hk : 2 ≤ k) (I : Finset ℤ) :
    ∑ c ∈ I, gaussB M k c ≤ 3 := by
  have hσ := sig2_ge hM
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hw : 0 < (k : ℝ) * sig2 M := by positivity
  rw [sum_congr rfl fun c _ => gaussB_eq_gd hM (by omega) c]
  refine (gd_sum_le hw _ I).trans ?_
  have h1 : 1 ≤ √(2 * π * (k * sig2 M)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  have : 2 / √(2 * π * (k * sig2 M)) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- **Lemma B0′ in the four classes**: with all classes `≥ n` (and `≥ 2`), replacing the four laws by
their Gaussians changes the sum over `c` by at most `3162/(σ³ n^{5/2})`. -/
theorem quad_err {M : ℕ} (hM : 2 ≤ M) {α β γ δ : ℕ} (hα : 2 ≤ α) (hβ : 2 ≤ β) (hγ : 2 ≤ γ)
    (hδ : 2 ≤ δ) {n : ℝ} (hn : 0 < n) (hnα : n ≤ α) (hnβ : n ≤ β) (hnγ : n ≤ γ) (hnδ : n ≤ δ)
    (a s : ℤ) (I : Finset ℤ) :
    |∑ c ∈ I, lawS M γ c * lawS M α (a - c) * lawS M β (a - c) * lawS M δ (s - 2 * a + c) -
      ∑ c ∈ I, gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) * gaussB M δ (s - 2 * a + c)| ≤
      3162 / (√(sig2 M) ^ 3 * (n ^ 2 * √n)) := by
  have hσ := sig2_pos hM
  have hs : 0 < √(sig2 M) := Real.sqrt_pos.mpr hσ
  have hsn : 0 < √n := Real.sqrt_pos.mpr hn
  set X := 1 / (√(sig2 M) * √n)
  set Y := 1 / (√(sig2 M) * (n * √n))
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : X ^ 2 * Y = 1 / (√(sig2 M) ^ 3 * (n ^ 2 * √n)) := by
    simp only [X, Y]
    have : √n ^ 2 = n := Real.sq_sqrt hn.le
    field_simp; exact this.symm
  have hinj : Function.Injective fun c : ℤ => s - 2 * a + c := fun c d h => by simp only at h; omega
  have hpt : ∀ c ∈ I, |lawS M γ c * lawS M α (a - c) * lawS M β (a - c) * lawS M δ (s - 2 * a + c) -
      gaussB M γ c * gaussB M α (a - c) * gaussB M β (a - c) * gaussB M δ (s - 2 * a + c)| ≤
      3111 * (X ^ 2 * Y) * lawS M δ (s - 2 * a + c) + 17 * (X ^ 2 * Y) * gaussB M γ c := fun c _ =>
    tele4 (lawS_nonneg _ _ _) (lawS_nonneg _ _ _) (lawS_nonneg _ _ _) (gaussB_nonneg _ _ _)
      (gaussB_nonneg _ _ _) (gaussB_nonneg _ _ _) (eB_le hM hγ hn hnγ _) (eB_le hM hα hn hnα _)
      (eB_le hM hβ hn hnβ _) (eB_le hM hδ hn hnδ _) (pB_le hM hα hn hnα _) (pB_le hM hβ hn hnβ _)
      (gB_le hM (by omega) hn hnγ _) (gB_le hM (by omega) hn hnα _) (gB_le hM (by omega) hn hnβ _) hX hY
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 := sum_lawS_le (f := fun c => s - 2 * a + c) (by omega : 0 < M) δ I hinj
  have h2 := sum_gaussB_le hM hγ I
  have hk : 0 ≤ X ^ 2 * Y := by positivity
  have : 3111 * (X ^ 2 * Y) * ∑ c ∈ I, lawS M δ (s - 2 * a + c) +
      17 * (X ^ 2 * Y) * ∑ c ∈ I, gaussB M γ c ≤ 3111 * (X ^ 2 * Y) * 1 + 17 * (X ^ 2 * Y) * 3 := by
    gcongr
  rw [show (3162 : ℝ) / (√(sig2 M) ^ 3 * (n ^ 2 * √n)) = 3162 * (X ^ 2 * Y) by rw [hXY]; ring]
  linarith

end ArcsAlgo.LLT
