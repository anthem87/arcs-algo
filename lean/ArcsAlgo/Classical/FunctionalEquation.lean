module

public import ArcsAlgo.Classical.TheoremS
public import ArcsAlgo.PrimeRaces
public import Mathlib.NumberTheory.MulChar.Lemmas
set_option autoImplicit false

/-!
# `β ≥ 1/2` by the functional equation (paper §4.2, end of the proof of Proposition 3)

* `LFunction_eq_primitive`: `L(s, χ) = L(s, χ*) Π_{p ∣ q}(1 − χ*(p) p^{−s})` (Mathlib's
  `LFunction_changeLevel`), with `χ*` the primitive character; the Euler factors do not vanish on
  `Re s > 0` (`eulerFactor_ne_zero`), nor does the gamma factor (`gammaFactor_ne_zero`).
* `LFunction_inv_one_sub_eq_zero`: a zero of `L(s, χ)` in the critical strip gives a zero of
  `L(s, χ̄)` at `1 − s` (Mathlib's `IsPrimitive.completedLFunction_one_sub` for `χ*`). This covers
  the imprimitive characters of the paper (conductor 5 at `q = 10`, 7 at `q = 14`).
* `grhFor_of_zeroFree`: for `X` closed under `χ ↦ χ̄`, no zero on `Re s > 1/2` gives `GRHFor X`.
* `charCoeff_inv`, `arcChars_inv`: for real weights `A_χ̄ = conj A_χ`, so `X(a/q)` is closed.
* `prop3_arc_two_imp_GRH`, `prop3_arc_three_imp_GRH`: Proposition 3, (2) ⇒ (1) and (3) ⇒ (1), with
  statement (1) in full: all zeros of `L(s, χ)`, `χ ∈ X(a/q)`, in `0 < Re s < 1` lie on `Re s = 1/2`.
* `real_zeroFree_of_half`: (R) on `[1/2, 1]` excludes real zeros on `(0, 1]` (the functional equation
  maps `(0, 1/2)` to `(1/2, 1)`); `thmS_not_eventually_upper'`, `thmS_not_eventually_lower'`,
  `thmS_sign_changes'`: Theorem S with the real-segment hypothesis reduced to (R) on `[1/2, 1]`, the
  interval certified by Arb in Table 4 (the point `σ = 1/2` is its own image and needs (R) itself).
-/

@[expose] public section

namespace ArcsAlgo.Classical

open Complex DirichletCharacter

/-- The Euler factors `1 − ψ(p) p^{−s}` do not vanish on `Re s > 0`. -/
theorem eulerFactor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 0 < s.re) : 1 - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hn := congrArg norm h1
  rw [norm_mul, norm_one, norm_natCast_cpow_of_pos hp.pos] at hn
  have h2 : (p : ℝ) ^ (-s).re < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simp; linarith)
  have h3 := ψ.norm_le_one p
  have h4 : 0 ≤ (p : ℝ) ^ (-s).re := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

/-- The gamma factor does not vanish on `Re s > 0`. -/
theorem gammaFactor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor ψ s ≠ 0 := by
  rcases ψ.even_or_odd with h | h
  · rw [Ne, gammaFactor_eq_zero_iff_of_even h]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  · rw [Ne, gammaFactor_eq_zero_iff_of_odd h]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith

/-- `L(χ, s) = L(χ*, s) · Π_{p ∣ q}(1 − χ*(p) p^{−s})`, `χ*` the primitive character. -/
theorem LFunction_eq_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) :
    haveI : NeZero χ.conductor := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd
      (h ▸ χ.conductor_dvd_level))⟩
    LFunction χ s = LFunction χ.primitiveCharacter s *
      ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  haveI : NeZero χ.conductor := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd
    (h ▸ χ.conductor_dvd_level))⟩
  have hp1 : χ.primitiveCharacter ≠ 1 := by
    intro h; apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  exact LFunction_changeLevel _ _ (Or.inl hp1)

/-- **The functional equation step** (paper §4.2, "the functional equation gives `β ≥ 1/2`"):
a zero of `L(s, χ)` with `0 < Re s < 1` gives a zero of `L(s, χ̄)` at `1 − s`. For imprimitive `χ`
it goes through the primitive character (`changeLevel`): the missing Euler factors vanish only on
`Re s = 0`. -/
theorem LFunction_inv_one_sub_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (h0 : LFunction χ s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    LFunction χ⁻¹ (1 - s) = 0 := by
  haveI : NeZero χ.conductor := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd
    (h ▸ χ.conductor_dvd_level))⟩
  set ψ := χ.primitiveCharacter
  have hψ : IsPrimitive ψ := χ.primitiveCharacter_isPrimitive
  have hψ1 : ψ ≠ 1 := by
    intro h; apply hχ
    rw [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from h, map_one]
  have hs' : s ≠ 0 := by rintro rfl; simp at hs0
  -- `L(ψ, s) = 0`
  have hL : LFunction ψ s = 0 := by
    have := LFunction_eq_primitive χ hχ s
    rw [h0] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact h
    · exact absurd h (Finset.prod_ne_zero_iff.2 fun p hp =>
        eulerFactor_ne_zero ψ (Nat.prime_of_mem_primeFactors hp) hs0)
  -- `Λ(ψ, s) = 0`
  have hΛ : completedLFunction ψ s = 0 := by
    have := LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs')
    rw [hL] at this
    exact (div_eq_zero_iff.1 this.symm).resolve_right (gammaFactor_ne_zero ψ hs0)
  -- the functional equation
  have hfe := IsPrimitive.completedLFunction_one_sub hψ (1 - s)
  rw [sub_sub_cancel, hΛ] at hfe
  have hN : ((χ.conductor : ℕ) : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast NeZero.ne χ.conductor)]
    exact Complex.exp_ne_zero _
  have hΛ' : completedLFunction ψ⁻¹ (1 - s) = 0 := by
    rcases mul_eq_zero.1 hfe.symm with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hN
      · exact absurd h' (rootNumber_ne_zero hψ)
    · exact h
  have h1s : 0 < (1 - s).re := by simp; linarith
  have h1s' : 1 - s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hL' : LFunction ψ⁻¹ (1 - s) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl h1s'), hΛ', zero_div]
  -- back to level `q`
  have hψinv1 : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ1
  have hcl : changeLevel χ.conductor_dvd_level ψ⁻¹ = χ⁻¹ := by
    rw [map_inv, χ.changeLevel_primitiveCharacter]
  rw [← hcl, LFunction_changeLevel _ _ (Or.inl hψinv1), hL', zero_mul]

/-- **From a zero-free half-plane to GRH for `X`**: if `X` is closed under `χ ↦ χ̄` and no
`L(s, χ)`, `χ ∈ X`, vanishes on `Re s > 1/2`, then `GRHFor X` (all zeros in the critical strip lie on
`Re s = 1/2`). -/
theorem grhFor_of_zeroFree {q : ℕ} [NeZero q] (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X)
    (h : ∀ χ ∈ X, ∀ ρ : ℂ, 1 / 2 < ρ.re → LFunction χ ρ ≠ 0) : ArcsAlgo.GRHFor X := by
  intro χ hχ s hs h0 h1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · exact h χ⁻¹ (hXinv χ hχ) (1 - s) (by simp; linarith)
      (LFunction_inv_one_sub_eq_zero χ (hX1 χ hχ) hs h0 h1)
  · exact h χ hχ s hgt hs

/-- `A_{χ̄} = conj A_χ` for real weights. -/
theorem charCoeff_inv {q : ℕ} [NeZero q] (w : ZMod q → ℝ) (χ : DirichletCharacter ℂ q) :
    charCoeff w χ⁻¹ = (starRingEnd ℂ) (charCoeff w χ) := by
  simp only [charCoeff, map_mul, map_inv₀, map_natCast, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← MulChar.star_apply']
  rfl

theorem arcChars_inv {q : ℕ} [NeZero q] (w : ZMod q → ℝ) :
    ∀ χ ∈ arcChars w, χ⁻¹ ∈ arcChars w := by
  classical
  intro χ hχ
  unfold arcChars at hχ ⊢
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hχ
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, inv_ne_one.2 h1, ?_⟩
  rw [charCoeff_inv]
  exact (map_ne_zero _).2 h2

/-- **Proposition 3, (2) ⇒ (1)** for the arc `a/q` (paper §4.2): under (R) on `(1/2, 1]` and (N),
the bounds `H_{a/q}(N) ≤ C_ε N^{1/2+ε}` give GRH for the characters `X(a/q)`. -/
theorem prop3_arc_two_imp_GRH {q : ℕ} [NeZero q] (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      primeRace (unitWeight (arcWeight q a)) N ≤ C * (N : ℝ) ^ (1 / 2 + ε)) :
    ArcsAlgo.GRHFor (arcChars (arcWeight q a)) :=
  grhFor_of_zeroFree _ (arcChars_ne_one _) (arcChars_inv _) (prop3_arc_two_imp_zeroFree a hR hN h2)

/-- **Proposition 3, (3) ⇒ (1)** for the arc `a/q`. -/
theorem prop3_arc_three_imp_GRH {q : ℕ} [NeZero q] (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(C * (N : ℝ) ^ (1 / 2 + ε)) ≤ primeRace (unitWeight (arcWeight q a)) N) :
    ArcsAlgo.GRHFor (arcChars (arcWeight q a)) :=
  grhFor_of_zeroFree _ (arcChars_ne_one _) (arcChars_inv _)
    (prop3_arc_three_imp_zeroFree a hR hN h3)

section ThmSHalf

variable {q : ℕ} [NeZero q]

/-- **The real segment `(1/3, 1]` from `[1/2, 1]`** (paper §4.3, proof of Theorem S): for `X` closed
under `χ ↦ χ̄`, condition (R) on `[1/2, 1]` excludes real zeros on `(0, 1]`; a zero at
`σ ∈ (0, 1/2)` would give, by the functional equation, a zero of `L(s, χ̄)` at `1 − σ ∈ (1/2, 1)`. -/
theorem real_zeroFree_of_half (X : Finset (DirichletCharacter ℂ q)) (hX1 : ∀ χ ∈ X, χ ≠ 1)
    (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0) :
    ∀ χ ∈ X, ∀ σ : ℝ, 0 < σ → σ ≤ 1 → LFunction χ σ ≠ 0 := by
  intro χ hχ σ h0 h1 hz
  rcases le_or_gt (1 / 2) σ with h | h
  · exact hR χ hχ σ h h1 hz
  · have := LFunction_inv_one_sub_eq_zero χ (hX1 χ hχ) hz (by simpa using h0)
      (by simp; linarith)
    exact hR χ⁻¹ (hXinv χ hχ) (1 - σ) (by linarith) (by linarith) (by push_cast; exact this)

/-- **Theorem S, `Ω₊`, with (R) only on `[1/2, 1]`**: for `X` closed under `χ ↦ χ̄` and `χ ↦ χ²`
(for `q = 14`: `X = {χ, χ̄}`, `χ² = χ̄`), the condition (R) on `[1/2, 1]` (the Arb certificate of
Table 4) replaces the two real-segment hypotheses of `thmS_not_eventually_upper`. -/
theorem thmS_not_eventually_upper' (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ := by
  have hall := real_zeroFree_of_half X hX1 hXinv hR
  exact thmS_not_eventually_upper X hX1 (fun χ hχ => hX1 _ (hXsq χ hχ)) A c hc
    (fun χ hχ σ hσ h1 => hall χ hχ σ (by linarith) h1)
    (fun χ hχ σ hσ h1 => hall _ (hXsq χ hχ) σ (by linarith) h1) hρ₀ hN₀ hθ

/-- **Theorem S, `Ω₋`, with (R) only on `[1/2, 1]`**. -/
theorem thmS_not_eventually_lower' (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ (C : ℝ) (x₀ : ℕ), ∀ N : ℕ, x₀ ≤ N → -(C * (N : ℝ) ^ θ) ≤ primeRace c N := by
  have hall := real_zeroFree_of_half X hX1 hXinv hR
  exact thmS_not_eventually_lower X hX1 (fun χ hχ => hX1 _ (hXsq χ hχ)) A c hc
    (fun χ hχ σ hσ h1 => hall χ hχ σ (by linarith) h1)
    (fun χ hχ σ hσ h1 => hall _ (hXsq χ hχ) σ (by linarith) h1) hρ₀ hN₀ hθ

/-- **Theorem S, sign changes, with (R) only on `[1/2, 1]`**. -/
theorem thmS_sign_changes' (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (hXinv : ∀ χ ∈ X, χ⁻¹ ∈ X) (hXsq : ∀ χ ∈ X, χ ^ 2 ∈ X)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re)
    (hN₀ : ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ₀ : ℂ) ≠ 0) :
    (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ 0 < primeRace c N) ∧
      (∀ x₀ : ℕ, ∃ N, x₀ ≤ N ∧ primeRace c N < 0) := by
  have hall := real_zeroFree_of_half X hX1 hXinv hR
  exact thmS_sign_changes X hX1 (fun χ hχ => hX1 _ (hXsq χ hχ)) A c hc
    (fun χ hχ σ hσ h1 => hall χ hχ σ (by linarith) h1)
    (fun χ hχ σ hσ h1 => hall _ (hXsq χ hχ) σ (by linarith) h1) hρ₀ hN₀

end ThmSHalf

end ArcsAlgo.Classical
