module

public import ArcsAlgo.LocalLimit.CharFun
public import ArcsAlgo.LocalLimit.Gauss
set_option autoImplicit false

/-!
# Real Gaussian moments (paper §6.2, proof of Lemma B0′)

`mom n β = ∫ θⁿ e^{−βθ²}`: `mom 0 β = √(π/β)`, `2β·mom (n+2) β = (n+1)·mom n β`, hence
`mom 6 β = 15/(8β³)·√(π/β)` and `mom 8 β = 105/(16β⁴)·√(π/β)`.
-/

open Real Complex MeasureTheory

@[expose] public section

namespace ArcsAlgo.LLT

lemma gk_zero_t (β θ : ℝ) : gk β 0 θ = ((Real.exp (-β * θ ^ 2) : ℝ) : ℂ) := by
  simp [gk, Complex.ofReal_exp]

/-- Real Gaussian moments `∫ θⁿ e^{−βθ²}`. -/
noncomputable def mom (n : ℕ) (β : ℝ) : ℝ := ∫ θ : ℝ, θ ^ n * Real.exp (-β * θ ^ 2)

lemma G_zero_t_eq (β : ℝ) (n : ℕ) : G β 0 n = ((mom n β : ℝ) : ℂ) := by
  rw [G, mom, ← integral_complex_ofReal]
  congr 1; funext θ; rw [gk_zero_t]; push_cast; ring

lemma mom_zero {β : ℝ} (hβ : 0 < β) : mom 0 β = √(π / β) := by
  apply Complex.ofReal_injective
  rw [← G_zero_t_eq, G_zero hβ, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  push_cast; simp

lemma mom_rec {β : ℝ} (hβ : 0 < β) (n : ℕ) : 2 * β * mom (n + 2) β = (n + 1) * mom n β := by
  apply Complex.ofReal_injective
  have := G_rec hβ 0 n
  rw [G_zero_t_eq, G_zero_t_eq] at this
  push_cast; simpa using this

lemma mom_two_step {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    mom (n + 2) β = (n + 1) * mom n β / (2 * β) := by
  have := mom_rec hβ n
  field_simp; linarith

lemma mom_six {β : ℝ} (hβ : 0 < β) : mom 6 β = 15 / (8 * β ^ 3) * √(π / β) := by
  have e2 : mom 2 β = _ := mom_two_step hβ 0
  have e4 : mom 4 β = _ := mom_two_step hβ 2
  have e6 : mom 6 β = _ := mom_two_step hβ 4
  rw [e6, e4, e2, mom_zero hβ]
  field_simp; push_cast; ring

lemma mom_eight {β : ℝ} (hβ : 0 < β) : mom 8 β = 105 / (16 * β ^ 4) * √(π / β) := by
  have e8 : mom 8 β = _ := mom_two_step hβ 6
  rw [e8, mom_six hβ]
  field_simp; push_cast; ring

end ArcsAlgo.LLT
