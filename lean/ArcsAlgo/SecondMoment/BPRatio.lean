module

public import ArcsAlgo.SecondMoment.BPMom
set_option autoImplicit false

/-!
# Proposition B′: the expansions in `h = m^{−1/2}` and the cancellation

`FX_decomp`, `FY_decomp`, `FS_decomp`: `Σ_{r ≤ 3} P_r h^r = φ·(1 + h t₁ + h² t₂ + h³ t₃ + h⁴ B)` at the points
`(σz, uh, uh)`, `(σz, uh)`, `σz`; `FXu_decomp`, `FYu_decomp`: `Σ_{r ≤ 5} P_r h^r = φ·(1 + h² t₂ + h⁴ t₄ + h⁶ B)`
at `(uh, uh)`, `uh` (`P₁ = P₃ = P₅ = 0` by symmetry, `edgeP_Xu_odd`, `edgeP_Yu_odd`). The low coefficients of
`F_X F_S − (1 + K₂h² + K₃zh³)F_Y²` vanish (`coef_e1`, `coef_e2`, `coef_e3`), and those of
`F_{X′} − (1 + K h² + C(u) h⁴) F_{Y′}²` (`coefU_e2`, `coefU_e4`).
-/

open Finset

@[expose] public section

namespace ArcsAlgo.LLT

variable {M : ℕ}

noncomputable def FXt1 (M : ℕ) (z u : ℝ) : ℝ := -cX M 1 0 2*z/(2*√(sig2 M)*√(ew2 M) ^ (2 : ℕ)) - cX M 1 2 0*z/(2*√(sig2 M)*√(ew2 M) ^ (2 : ℕ))

noncomputable def FXt2 (M : ℕ) (z u : ℝ) : ℝ := cX M 0 0 4/(8*√(ew2 M) ^ (4 : ℕ)) + cX M 0 2 2/(4*√(ew2 M) ^ (4 : ℕ)) + cX M 0 4 0/(8*√(ew2 M) ^ (4 : ℕ)) + 3*cX M 1 0 2 ^ (2 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 3*cX M 1 0 2 ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cX M 1 0 2*cX M 1 2 0*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 1 0 2*cX M 1 2 0/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + 3*cX M 1 2 0 ^ (2 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 3*cX M 1 2 0 ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 2 0 2*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 2 0 2/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) - cX M 2 2 0*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 2 2 0/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 4 0 0*z ^ (4 : ℕ)/(24*√(sig2 M) ^ (4 : ℕ)) - cX M 4 0 0*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (4 : ℕ)) + cX M 4 0 0/(8*√(sig2 M) ^ (4 : ℕ))

noncomputable def FXt3 (M : ℕ) (z u : ℝ) : ℝ := -5*cX M 0 0 4*cX M 1 0 2*z/(16*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - cX M 0 0 4*cX M 1 2 0*z/(16*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - 3*cX M 0 2 2*cX M 1 0 2*z/(8*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - 3*cX M 0 2 2*cX M 1 2 0*z/(8*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - cX M 0 4 0*cX M 1 0 2*z/(16*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - 5*cX M 0 4 0*cX M 1 2 0*z/(16*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - 5*cX M 1 0 2 ^ (3 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 15*cX M 1 0 2 ^ (3 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) - 3*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 9*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) - 3*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 9*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cX M 1 0 2*cX M 2 0 2*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 9*cX M 1 0 2*cX M 2 0 2*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cX M 1 0 2*cX M 2 2 0*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 3*cX M 1 0 2*cX M 2 2 0*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 1 0 2*cX M 4 0 0*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + 5*cX M 1 0 2*cX M 4 0 0*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) - 5*cX M 1 0 2*cX M 4 0 0*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 1 0 2*u ^ (2 : ℕ)*z/(2*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) + cX M 1 0 4*z/(8*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) - 5*cX M 1 2 0 ^ (3 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 15*cX M 1 2 0 ^ (3 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 2 0*cX M 2 0 2*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 3*cX M 1 2 0*cX M 2 0 2*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + 3*cX M 1 2 0*cX M 2 2 0*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 9*cX M 1 2 0*cX M 2 2 0*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 1 2 0*cX M 4 0 0*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + 5*cX M 1 2 0*cX M 4 0 0*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) - 5*cX M 1 2 0*cX M 4 0 0*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 1 2 0*u ^ (2 : ℕ)*z/(2*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) + cX M 1 2 2*z/(4*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) + cX M 1 4 0*z/(8*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) - cX M 3 0 2*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 3 0 2*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ)) - cX M 3 2 0*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cX M 3 2 0*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ))

noncomputable def FXB (M : ℕ) (h z u : ℝ) : ℝ := 15*cX M 0 0 4*cX M 1 0 2*h*u ^ (2 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 5*cX M 0 0 4*cX M 1 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 0 4*cX M 1 0 2*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) + 3*cX M 0 0 4*cX M 1 2 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 0 0 4*cX M 1 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 0 4*cX M 1 2 0*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) - cX M 0 0 4*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) + cX M 0 0 4*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + 9*cX M 0 2 2*cX M 1 0 2*h*u ^ (2 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 0 2 2*cX M 1 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 2 2*cX M 1 0 2*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) + 9*cX M 0 2 2*cX M 1 2 0*h*u ^ (2 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 0 2 2*cX M 1 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 2 2*cX M 1 2 0*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(8*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) - cX M 0 2 2*u ^ (2 : ℕ)/(2*√(ew2 M) ^ (6 : ℕ)) + cX M 0 2 2*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(4*√(ew2 M) ^ (8 : ℕ)) + 3*cX M 0 4 0*cX M 1 0 2*h*u ^ (2 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 0 4 0*cX M 1 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 4 0*cX M 1 0 2*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) + 15*cX M 0 4 0*cX M 1 2 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 5*cX M 0 4 0*cX M 1 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cX M 0 4 0*cX M 1 2 0*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) - cX M 0 4 0*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) + cX M 0 4 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + 15*cX M 1 0 2 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 45*cX M 1 0 2 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 5*cX M 1 0 2 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + 15*cX M 1 0 2 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + cX M 1 0 2 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z ^ (3 : ℕ)/(48*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - cX M 1 0 2 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) + 9*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 27*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + 21*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - 3*cX M 1 0 2 ^ (2 : ℕ)*cX M 1 2 0*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - 3*cX M 1 0 2 ^ (2 : ℕ)*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cX M 1 0 2 ^ (2 : ℕ)*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 2 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 0 2 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) + 9*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 27*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 7*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + 21*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - 3*cX M 1 0 2*cX M 1 2 0 ^ (2 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - cX M 1 0 2*cX M 1 2 0*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(2*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 2*cX M 1 2 0*u ^ (2 : ℕ)/(2*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 2*cX M 1 2 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 0 2*cX M 1 2 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 0 2*cX M 2 0 2*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 9*cX M 1 0 2*cX M 2 0 2*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 2*cX M 2 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 0 2*cX M 2 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 0 2*cX M 2 2 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cX M 1 0 2*cX M 2 2 0*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 2*cX M 2 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 0 2*cX M 2 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) + cX M 1 0 2*cX M 4 0 0*h*u ^ (2 : ℕ)*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 5*cX M 1 0 2*cX M 4 0 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + 5*cX M 1 0 2*cX M 4 0 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 1 0 4*h*u ^ (2 : ℕ)*z/(4*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 0 4*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(24*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) + 15*cX M 1 2 0 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 45*cX M 1 2 0 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 5*cX M 1 2 0 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + 15*cX M 1 2 0 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + cX M 1 2 0 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z ^ (3 : ℕ)/(48*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - cX M 1 2 0 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - 3*cX M 1 2 0 ^ (2 : ℕ)*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cX M 1 2 0 ^ (2 : ℕ)*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 2 0 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 2 0 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 2 0*cX M 2 0 2*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cX M 1 2 0*cX M 2 0 2*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 2 0*cX M 2 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 2 0*cX M 2 0 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 2 0*cX M 2 2 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 9*cX M 1 2 0*cX M 2 2 0*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 2 0*cX M 2 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cX M 1 2 0*cX M 2 2 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) + cX M 1 2 0*cX M 4 0 0*h*u ^ (2 : ℕ)*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 5*cX M 1 2 0*cX M 4 0 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + 5*cX M 1 2 0*cX M 4 0 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 1 2 2*h*u ^ (2 : ℕ)*z/(2*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 2 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(4*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - cX M 1 4 0*h*u ^ (2 : ℕ)*z/(4*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) + cX M 1 4 0*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(24*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) + cX M 2 0 2*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 2 0 2*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cX M 2 2 0*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 2 2 0*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cX M 3 0 2*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 3 0 2*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cX M 3 2 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cX M 3 2 0*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem FX_decomp (hM : 2 ≤ M) (h z u : ℝ) :
    ∑ r ∈ range 4, edgeP (pX M) (xiX M) r ![√(sig2 M) * z, u * h, u * h] * h ^ r =
      gaussDens (vcov (pX M) (xiX M)) ![√(sig2 M) * z, u * h, u * h] * (1 + h ^ (1 : ℕ) * FXt1 M z u + h ^ (2 : ℕ) * FXt2 M z u + h ^ (3 : ℕ) * FXt3 M z u + h ^ (4 : ℕ) * FXB M h z u) := by
  have hM1 : 1 ≤ M := by omega
  have hσ : √(sig2 M) ≠ 0 := (Real.sqrt_pos.mpr (sig2_pos' hM)).ne'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, edgeP_zero, edgeP_X1 hM, edgeP_X2 hM, edgeP_X3 hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one]
  simp only [show √(sig2 M) * z / √(sig2 M) = z by field_simp, heP, cX300 hM1, cX500 hM1]
  unfold FXt1 FXt2 FXt3 FXB
  ring
noncomputable def FYt1 (M : ℕ) (z u : ℝ) : ℝ := -cY M 1 2*z/(2*√(sig2 M)*√(ew2 M) ^ (2 : ℕ))

noncomputable def FYt2 (M : ℕ) (z u : ℝ) : ℝ := cY M 0 4/(8*√(ew2 M) ^ (4 : ℕ)) + 3*cY M 1 2 ^ (2 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 3*cY M 1 2 ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cY M 2 2*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cY M 2 2/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cY M 4 0*z ^ (4 : ℕ)/(24*√(sig2 M) ^ (4 : ℕ)) - cY M 4 0*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (4 : ℕ)) + cY M 4 0/(8*√(sig2 M) ^ (4 : ℕ))

noncomputable def FYt3 (M : ℕ) (z u : ℝ) : ℝ := -5*cY M 0 4*cY M 1 2*z/(16*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) - 5*cY M 1 2 ^ (3 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 15*cY M 1 2 ^ (3 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cY M 1 2*cY M 2 2*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 9*cY M 1 2*cY M 2 2*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cY M 1 2*cY M 4 0*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + 5*cY M 1 2*cY M 4 0*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) - 5*cY M 1 2*cY M 4 0*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cY M 1 2*u ^ (2 : ℕ)*z/(2*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) + cY M 1 4*z/(8*√(sig2 M)*√(ew2 M) ^ (4 : ℕ)) - cY M 3 2*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ)) + cY M 3 2*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (2 : ℕ))

noncomputable def FYB (M : ℕ) (h z u : ℝ) : ℝ := 15*cY M 0 4*cY M 1 2*h*u ^ (2 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) - 5*cY M 0 4*cY M 1 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M)*√(ew2 M) ^ (10 : ℕ)) + cY M 0 4*cY M 1 2*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(48*√(sig2 M)*√(ew2 M) ^ (12 : ℕ)) - cY M 0 4*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) + cY M 0 4*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + 15*cY M 1 2 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 45*cY M 1 2 ^ (3 : ℕ)*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 5*cY M 1 2 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + 15*cY M 1 2 ^ (3 : ℕ)*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (10 : ℕ)) + cY M 1 2 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z ^ (3 : ℕ)/(48*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - cY M 1 2 ^ (3 : ℕ)*h ^ (5 : ℕ)*u ^ (6 : ℕ)*z/(16*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (12 : ℕ)) - 3*cY M 1 2 ^ (2 : ℕ)*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 3*cY M 1 2 ^ (2 : ℕ)*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cY M 1 2 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)*z ^ (2 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - cY M 1 2 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(8*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cY M 1 2*cY M 2 2*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + 9*cY M 1 2*cY M 2 2*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (6 : ℕ)) + cY M 1 2*cY M 2 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z ^ (3 : ℕ)/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) - 3*cY M 1 2*cY M 2 2*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(8*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (8 : ℕ)) + cY M 1 2*cY M 4 0*h*u ^ (2 : ℕ)*z ^ (5 : ℕ)/(48*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - 5*cY M 1 2*cY M 4 0*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(24*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + 5*cY M 1 2*cY M 4 0*h*u ^ (2 : ℕ)*z/(16*√(sig2 M) ^ (5 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cY M 1 4*h*u ^ (2 : ℕ)*z/(4*√(sig2 M)*√(ew2 M) ^ (6 : ℕ)) + cY M 1 4*h ^ (3 : ℕ)*u ^ (4 : ℕ)*z/(24*√(sig2 M)*√(ew2 M) ^ (8 : ℕ)) + cY M 2 2*u ^ (2 : ℕ)*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cY M 2 2*u ^ (2 : ℕ)/(4*√(sig2 M) ^ (2 : ℕ)*√(ew2 M) ^ (4 : ℕ)) + cY M 3 2*h*u ^ (2 : ℕ)*z ^ (3 : ℕ)/(12*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ)) - cY M 3 2*h*u ^ (2 : ℕ)*z/(4*√(sig2 M) ^ (3 : ℕ)*√(ew2 M) ^ (4 : ℕ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem FY_decomp (hM : 2 ≤ M) (h z u : ℝ) :
    ∑ r ∈ range 4, edgeP (pY M) (xiY M) r ![√(sig2 M) * z, u * h] * h ^ r =
      gaussDens (vcov (pY M) (xiY M)) ![√(sig2 M) * z, u * h] * (1 + h ^ (1 : ℕ) * FYt1 M z u + h ^ (2 : ℕ) * FYt2 M z u + h ^ (3 : ℕ) * FYt3 M z u + h ^ (4 : ℕ) * FYB M h z u) := by
  have hM1 : 1 ≤ M := by omega
  have hσ : √(sig2 M) ≠ 0 := (Real.sqrt_pos.mpr (sig2_pos' hM)).ne'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, edgeP_zero, edgeP_Y1 hM, edgeP_Y2 hM, edgeP_Y3 hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one]
  simp only [show √(sig2 M) * z / √(sig2 M) = z by field_simp, heP, cY30 hM1, cY50 hM1]
  unfold FYt1 FYt2 FYt3 FYB
  ring
noncomputable def FSt1 (M : ℕ) (z u : ℝ) : ℝ := 0

noncomputable def FSt2 (M : ℕ) (z u : ℝ) : ℝ := cS M 4*z ^ (4 : ℕ)/(24*√(sig2 M) ^ (4 : ℕ)) - cS M 4*z ^ (2 : ℕ)/(4*√(sig2 M) ^ (4 : ℕ)) + cS M 4/(8*√(sig2 M) ^ (4 : ℕ))

noncomputable def FSt3 (M : ℕ) (z u : ℝ) : ℝ := 0

noncomputable def FSB (M : ℕ) (h z u : ℝ) : ℝ := 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem FS_decomp (hM : 2 ≤ M) (h z u : ℝ) :
    ∑ r ∈ range 4, edgeP (pS M) (xi1 M) r ![√(sig2 M) * z] * h ^ r =
      gaussDens (vcov (pS M) (xi1 M)) ![√(sig2 M) * z] * (1 + h ^ (1 : ℕ) * FSt1 M z u + h ^ (2 : ℕ) * FSt2 M z u + h ^ (3 : ℕ) * FSt3 M z u + h ^ (4 : ℕ) * FSB M h z u) := by
  have hM1 : 1 ≤ M := by omega
  have hσ : √(sig2 M) ≠ 0 := (Real.sqrt_pos.mpr (sig2_pos' hM)).ne'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, edgeP_zero, edgeP_S1 hM, edgeP_S2 hM, edgeP_S3 hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one]
  simp only [show √(sig2 M) * z / √(sig2 M) = z by field_simp, heP, cS3 hM1, cS5 hM1]
  unfold FSt1 FSt2 FSt3 FSB
  ring


theorem edgeP_Xu_odd (hM : 2 ≤ M) {r : ℕ} (hr : Odd r) (x : Fin 2 → ℝ) : edgeP (pX M) (xiXu M) r x = 0 := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp [ew2_pos]
  rw [edgeP_odd _ _ _ (vcov_Xu hM1) hD (fun α hα => ?_) hr]; · rfl
  rw [cumul_Xu hM1]
  rw [Fin.sum_univ_two, Nat.odd_add] at hα
  by_cases h0 : Odd (α 0)
  · exact cXu_odd0 hM1 h0
  · have : ¬ Even (α 1) := fun h => h0 (hα.mpr h)
    exact cXu_odd1 hM1 (Nat.not_even_iff_odd.mp this)

theorem edgeP_Yu_odd (hM : 2 ≤ M) {r : ℕ} (hr : Odd r) (x : Fin 1 → ℝ) : edgeP (pY M) (xiYu M) r x = 0 := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact ew2_pos M
  rw [edgeP_odd _ _ _ (vcov_Yu hM1) hD (fun α hα => ?_) hr]; · rfl
  rw [cumul_Yu hM1]
  rw [Fin.sum_univ_one] at hα
  exact cYu_odd hM1 hα

noncomputable def FXut2 (M : ℕ) (u : ℝ) : ℝ := cXu M 0 4/(8*√(ew2 M) ^ (4 : ℕ)) + cXu M 2 2/(4*√(ew2 M) ^ (4 : ℕ)) + cXu M 4 0/(8*√(ew2 M) ^ (4 : ℕ))

noncomputable def FXut4 (M : ℕ) (u : ℝ) : ℝ := 35*cXu M 0 4 ^ (2 : ℕ)/(384*√(ew2 M) ^ (8 : ℕ)) + 5*cXu M 0 4*cXu M 2 2/(32*√(ew2 M) ^ (8 : ℕ)) + cXu M 0 4*cXu M 4 0/(64*√(ew2 M) ^ (8 : ℕ)) - cXu M 0 4*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) - cXu M 0 6/(48*√(ew2 M) ^ (6 : ℕ)) + 9*cXu M 2 2 ^ (2 : ℕ)/(32*√(ew2 M) ^ (8 : ℕ)) + 5*cXu M 2 2*cXu M 4 0/(32*√(ew2 M) ^ (8 : ℕ)) - cXu M 2 2*u ^ (2 : ℕ)/(2*√(ew2 M) ^ (6 : ℕ)) - cXu M 2 4/(16*√(ew2 M) ^ (6 : ℕ)) + 35*cXu M 4 0 ^ (2 : ℕ)/(384*√(ew2 M) ^ (8 : ℕ)) - cXu M 4 0*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) - cXu M 4 2/(16*√(ew2 M) ^ (6 : ℕ)) - cXu M 6 0/(48*√(ew2 M) ^ (6 : ℕ))

noncomputable def FXuB (M : ℕ) (h u : ℝ) : ℝ := -35*cXu M 0 4 ^ (2 : ℕ)*u ^ (2 : ℕ)/(96*√(ew2 M) ^ (10 : ℕ)) + 35*cXu M 0 4 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(192*√(ew2 M) ^ (12 : ℕ)) - 7*cXu M 0 4 ^ (2 : ℕ)*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(288*√(ew2 M) ^ (14 : ℕ)) + cXu M 0 4 ^ (2 : ℕ)*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(1152*√(ew2 M) ^ (16 : ℕ)) - 5*cXu M 0 4*cXu M 2 2*u ^ (2 : ℕ)/(8*√(ew2 M) ^ (10 : ℕ)) + 5*cXu M 0 4*cXu M 2 2*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(8*√(ew2 M) ^ (12 : ℕ)) - cXu M 0 4*cXu M 2 2*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(6*√(ew2 M) ^ (14 : ℕ)) + cXu M 0 4*cXu M 2 2*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(96*√(ew2 M) ^ (16 : ℕ)) - cXu M 0 4*cXu M 4 0*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (10 : ℕ)) + 7*cXu M 0 4*cXu M 4 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(96*√(ew2 M) ^ (12 : ℕ)) - cXu M 0 4*cXu M 4 0*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(48*√(ew2 M) ^ (14 : ℕ)) + cXu M 0 4*cXu M 4 0*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(576*√(ew2 M) ^ (16 : ℕ)) + cXu M 0 4*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + cXu M 0 6*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (8 : ℕ)) - cXu M 0 6*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(48*√(ew2 M) ^ (10 : ℕ)) + cXu M 0 6*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(720*√(ew2 M) ^ (12 : ℕ)) - 9*cXu M 2 2 ^ (2 : ℕ)*u ^ (2 : ℕ)/(8*√(ew2 M) ^ (10 : ℕ)) + 21*cXu M 2 2 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(16*√(ew2 M) ^ (12 : ℕ)) - 3*cXu M 2 2 ^ (2 : ℕ)*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(8*√(ew2 M) ^ (14 : ℕ)) + cXu M 2 2 ^ (2 : ℕ)*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(32*√(ew2 M) ^ (16 : ℕ)) - 5*cXu M 2 2*cXu M 4 0*u ^ (2 : ℕ)/(8*√(ew2 M) ^ (10 : ℕ)) + 5*cXu M 2 2*cXu M 4 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(8*√(ew2 M) ^ (12 : ℕ)) - cXu M 2 2*cXu M 4 0*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(6*√(ew2 M) ^ (14 : ℕ)) + cXu M 2 2*cXu M 4 0*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(96*√(ew2 M) ^ (16 : ℕ)) + cXu M 2 2*u ^ (4 : ℕ)/(4*√(ew2 M) ^ (8 : ℕ)) + 3*cXu M 2 4*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (8 : ℕ)) - 7*cXu M 2 4*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(48*√(ew2 M) ^ (10 : ℕ)) + cXu M 2 4*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(48*√(ew2 M) ^ (12 : ℕ)) - 35*cXu M 4 0 ^ (2 : ℕ)*u ^ (2 : ℕ)/(96*√(ew2 M) ^ (10 : ℕ)) + 35*cXu M 4 0 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(192*√(ew2 M) ^ (12 : ℕ)) - 7*cXu M 4 0 ^ (2 : ℕ)*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(288*√(ew2 M) ^ (14 : ℕ)) + cXu M 4 0 ^ (2 : ℕ)*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(1152*√(ew2 M) ^ (16 : ℕ)) + cXu M 4 0*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + 3*cXu M 4 2*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (8 : ℕ)) - 7*cXu M 4 2*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(48*√(ew2 M) ^ (10 : ℕ)) + cXu M 4 2*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(48*√(ew2 M) ^ (12 : ℕ)) + cXu M 6 0*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (8 : ℕ)) - cXu M 6 0*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(48*√(ew2 M) ^ (10 : ℕ)) + cXu M 6 0*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(720*√(ew2 M) ^ (12 : ℕ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem FXu_decomp (hM : 2 ≤ M) (h u : ℝ) :
    ∑ r ∈ range 6, edgeP (pX M) (xiXu M) r ![u * h, u * h] * h ^ r =
      gaussDens (vcov (pX M) (xiXu M)) ![u * h, u * h] * (1 + h ^ (2 : ℕ) * FXut2 M u + h ^ (4 : ℕ) * FXut4 M u + h ^ (6 : ℕ) * FXuB M h u) := by
  have hM1 : 1 ≤ M := by omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, edgeP_zero, edgeP_Xu2 hM, edgeP_Xu4 hM,
    edgeP_Xu_odd hM (by decide : Odd 1), edgeP_Xu_odd hM (by decide : Odd 3), edgeP_Xu_odd hM (by decide : Odd 5)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, heP, Pi.zero_apply]
  unfold FXut2 FXut4 FXuB
  ring
noncomputable def FYut2 (M : ℕ) (u : ℝ) : ℝ := cYu M 4/(8*√(ew2 M) ^ (4 : ℕ))

noncomputable def FYut4 (M : ℕ) (u : ℝ) : ℝ := 35*cYu M 4 ^ (2 : ℕ)/(384*√(ew2 M) ^ (8 : ℕ)) - cYu M 4*u ^ (2 : ℕ)/(4*√(ew2 M) ^ (6 : ℕ)) - cYu M 6/(48*√(ew2 M) ^ (6 : ℕ))

noncomputable def FYuB (M : ℕ) (h u : ℝ) : ℝ := -35*cYu M 4 ^ (2 : ℕ)*u ^ (2 : ℕ)/(96*√(ew2 M) ^ (10 : ℕ)) + 35*cYu M 4 ^ (2 : ℕ)*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(192*√(ew2 M) ^ (12 : ℕ)) - 7*cYu M 4 ^ (2 : ℕ)*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(288*√(ew2 M) ^ (14 : ℕ)) + cYu M 4 ^ (2 : ℕ)*h ^ (6 : ℕ)*u ^ (8 : ℕ)/(1152*√(ew2 M) ^ (16 : ℕ)) + cYu M 4*u ^ (4 : ℕ)/(24*√(ew2 M) ^ (8 : ℕ)) + cYu M 6*u ^ (2 : ℕ)/(16*√(ew2 M) ^ (8 : ℕ)) - cYu M 6*h ^ (2 : ℕ)*u ^ (4 : ℕ)/(48*√(ew2 M) ^ (10 : ℕ)) + cYu M 6*h ^ (4 : ℕ)*u ^ (6 : ℕ)/(720*√(ew2 M) ^ (12 : ℕ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem FYu_decomp (hM : 2 ≤ M) (h u : ℝ) :
    ∑ r ∈ range 6, edgeP (pY M) (xiYu M) r ![u * h] * h ^ r =
      gaussDens (vcov (pY M) (xiYu M)) ![u * h] * (1 + h ^ (2 : ℕ) * FYut2 M u + h ^ (4 : ℕ) * FYut4 M u + h ^ (6 : ℕ) * FYuB M h u) := by
  have hM1 : 1 ≤ M := by omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, edgeP_zero, edgeP_Yu2 hM, edgeP_Yu4 hM,
    edgeP_Yu_odd hM (by decide : Odd 1), edgeP_Yu_odd hM (by decide : Odd 3), edgeP_Yu_odd hM (by decide : Odd 5)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, heP, Pi.zero_apply]
  unfold FYut2 FYut4 FYuB
  ring


/-! ### The constants and the vanishing of the low coefficients -/

/-- `κ_c` in standardized cumulants: `(χ_{0,2,2}/s⁴ − (χ_{1,0,2}/(σ s²))²)/4`. -/
noncomputable def KK2 (M : ℕ) : ℝ :=
  (cX M 0 2 2 / √(ew2 M) ^ (4 : ℕ) - (cX M 1 0 2 / (√(sig2 M) * √(ew2 M) ^ (2 : ℕ))) ^ (2 : ℕ)) / 4

/-- `γ_M` in standardized cumulants. -/
noncomputable def KK3 (M : ℕ) : ℝ :=
  -(2 * (cX M 0 2 2 / √(ew2 M) ^ (4 : ℕ)) * (cX M 1 0 2 / (√(sig2 M) * √(ew2 M) ^ (2 : ℕ))) -
    2 * (cX M 1 0 2 / (√(sig2 M) * √(ew2 M) ^ (2 : ℕ))) ^ (3 : ℕ) +
    2 * (cX M 1 0 2 / (√(sig2 M) * √(ew2 M) ^ (2 : ℕ))) * (cX M 2 0 2 / (√(sig2 M) ^ (2 : ℕ) * √(ew2 M) ^ (2 : ℕ))) -
    cX M 1 2 2 / (√(sig2 M) * √(ew2 M) ^ (4 : ℕ))) / 4

/-- `κ` (unconditional) in standardized cumulants. -/
noncomputable def KKu (M : ℕ) : ℝ := FXut2 M 0 - 2 * FYut2 M 0

/-- The coefficient of `m⁻²` (unconditional), as a function of `u`. -/
noncomputable def CCu (M : ℕ) (u : ℝ) : ℝ :=
  FXut4 M u - 2 * KKu M * FYut2 M u - FYut2 M u ^ (2 : ℕ) - 2 * FYut4 M u

set_option maxHeartbeats 4000000 in
theorem coef_e1 (hM : 2 ≤ M) (z u : ℝ) : FXt1 M z u + FSt1 M z u - 2 * FYt1 M z u = 0 := by
  have hM1 : 1 ≤ M := by omega
  unfold FXt1 FSt1 FYt1
  simp only [cX_100 hM1, cX_200 hM1, cX_120 hM1, cX_002 hM1, cX_020 hM1, cX_300 hM1, cX_102 hM1, cX_400 hM1, cX_202 hM1, cX_220 hM1, cX_004 hM1, cX_022 hM1, cX_040 hM1, cX_500 hM1, cX_302 hM1, cX_320 hM1, cX_104 hM1, cX_122 hM1, cX_140 hM1, cY_10 hM1, cY_20 hM1, cY_02 hM1, cY_30 hM1, cY_12 hM1, cY_40 hM1, cY_22 hM1, cY_04 hM1, cY_50 hM1, cY_32 hM1, cY_14 hM1, cS_1 hM1, cS_2 hM1, cS_3 hM1, cS_4 hM1, cS_5 hM1, cXu_20 hM1, cXu_02 hM1, cXu_40 hM1, cXu_22 hM1, cXu_04 hM1, cXu_60 hM1, cXu_42 hM1, cXu_24 hM1, cXu_06 hM1, cYu_2 hM1, cYu_4 hM1, cYu_6 hM1]
  ring

set_option maxHeartbeats 4000000 in
theorem coef_e2 (hM : 2 ≤ M) (z u : ℝ) :
    -KK2 M + FXt1 M z u * FSt1 M z u + FXt2 M z u - FYt1 M z u ^ 2 - 2 * FYt2 M z u + FSt2 M z u = 0 := by
  have hM1 : 1 ≤ M := by omega
  unfold KK2 FXt1 FSt1 FYt1 FXt2 FYt2 FSt2
  simp only [cX_100 hM1, cX_200 hM1, cX_120 hM1, cX_002 hM1, cX_020 hM1, cX_300 hM1, cX_102 hM1, cX_400 hM1, cX_202 hM1, cX_220 hM1, cX_004 hM1, cX_022 hM1, cX_040 hM1, cX_500 hM1, cX_302 hM1, cX_320 hM1, cX_104 hM1, cX_122 hM1, cX_140 hM1, cY_10 hM1, cY_20 hM1, cY_02 hM1, cY_30 hM1, cY_12 hM1, cY_40 hM1, cY_22 hM1, cY_04 hM1, cY_50 hM1, cY_32 hM1, cY_14 hM1, cS_1 hM1, cS_2 hM1, cS_3 hM1, cS_4 hM1, cS_5 hM1, cXu_20 hM1, cXu_02 hM1, cXu_40 hM1, cXu_22 hM1, cXu_04 hM1, cXu_60 hM1, cXu_42 hM1, cXu_24 hM1, cXu_06 hM1, cYu_2 hM1, cYu_4 hM1, cYu_6 hM1]
  ring

set_option maxHeartbeats 4000000 in
theorem coef_e3 (hM : 2 ≤ M) (z u : ℝ) :
    -2 * KK2 M * FYt1 M z u - KK3 M * z + FXt1 M z u * FSt2 M z u + FXt2 M z u * FSt1 M z u + FXt3 M z u -
      2 * FYt1 M z u * FYt2 M z u - 2 * FYt3 M z u + FSt3 M z u = 0 := by
  have hM1 : 1 ≤ M := by omega
  unfold KK2 KK3 FXt1 FSt1 FYt1 FXt2 FYt2 FSt2 FXt3 FYt3 FSt3
  simp only [cX_100 hM1, cX_200 hM1, cX_120 hM1, cX_002 hM1, cX_020 hM1, cX_300 hM1, cX_102 hM1, cX_400 hM1, cX_202 hM1, cX_220 hM1, cX_004 hM1, cX_022 hM1, cX_040 hM1, cX_500 hM1, cX_302 hM1, cX_320 hM1, cX_104 hM1, cX_122 hM1, cX_140 hM1, cY_10 hM1, cY_20 hM1, cY_02 hM1, cY_30 hM1, cY_12 hM1, cY_40 hM1, cY_22 hM1, cY_04 hM1, cY_50 hM1, cY_32 hM1, cY_14 hM1, cS_1 hM1, cS_2 hM1, cS_3 hM1, cS_4 hM1, cS_5 hM1, cXu_20 hM1, cXu_02 hM1, cXu_40 hM1, cXu_22 hM1, cXu_04 hM1, cXu_60 hM1, cXu_42 hM1, cXu_24 hM1, cXu_06 hM1, cYu_2 hM1, cYu_4 hM1, cYu_6 hM1]
  ring

theorem coefU_e2 (hM : 2 ≤ M) (u : ℝ) : -KKu M + FXut2 M u - 2 * FYut2 M u = 0 := by
  have hM1 : 1 ≤ M := by omega
  unfold KKu FXut2 FYut2
  simp only [cX_100 hM1, cX_200 hM1, cX_120 hM1, cX_002 hM1, cX_020 hM1, cX_300 hM1, cX_102 hM1, cX_400 hM1, cX_202 hM1, cX_220 hM1, cX_004 hM1, cX_022 hM1, cX_040 hM1, cX_500 hM1, cX_302 hM1, cX_320 hM1, cX_104 hM1, cX_122 hM1, cX_140 hM1, cY_10 hM1, cY_20 hM1, cY_02 hM1, cY_30 hM1, cY_12 hM1, cY_40 hM1, cY_22 hM1, cY_04 hM1, cY_50 hM1, cY_32 hM1, cY_14 hM1, cS_1 hM1, cS_2 hM1, cS_3 hM1, cS_4 hM1, cS_5 hM1, cXu_20 hM1, cXu_02 hM1, cXu_40 hM1, cXu_22 hM1, cXu_04 hM1, cXu_60 hM1, cXu_42 hM1, cXu_24 hM1, cXu_06 hM1, cYu_2 hM1, cYu_4 hM1, cYu_6 hM1]
  ring

theorem coefU_e4 (hM : 2 ≤ M) (u : ℝ) :
    -CCu M u - 2 * KKu M * FYut2 M u + FXut4 M u - FYut2 M u ^ 2 - 2 * FYut4 M u = 0 := by
  unfold CCu; ring

end ArcsAlgo.LLT
