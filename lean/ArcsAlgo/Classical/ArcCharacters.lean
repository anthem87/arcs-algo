module

public import ArcsAlgo.Classical.ArcProp3
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false

/-!
# The character expansion of the arc weights (paper §4.1)

* `charCoeff w χ = φ(q)^{−1} Σ_{(r,q)=1} w_r χ(r^{−1})`, and `χ(r^{−1}) = χ̄(r)` on units.
* `sum_charCoeff_mul`: `w_b = Σ_χ A_χ χ(b)` for every unit `b` (orthogonality,
  Mathlib's `sum_char_inv_mul_char_eq`).
* `charCoeff_one`: the principal character drops out when `Σ_r w_r = 0`;
  `charCoeff_of_odd`: the odd characters drop out when `w(−r) = w(r)`.
* `isCharCombination_unitWeight`: the hypothesis `IsCharCombination` of `ArcProp3` holds for
  `X = arcChars w = {χ ≠ χ₀ : A_χ ≠ 0}`.
* The weights of the paper, `arcWeight q a r = log|cos(πra/q)| − w̄(q)`, have mean zero
  (`sum_arcWeight`) and are even (`arcWeight_neg`); `prop3_arc_two_imp_zeroFree`,
  `prop3_arc_three_imp_zeroFree` are Proposition 3 for the arc `a/q` with this expansion proved.
-/

@[expose] public section

namespace ArcsAlgo.Classical

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The units of `ZMod q`, as a finset. -/
noncomputable def unitsZMod (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun r => IsUnit r

theorem isUnit_zmod_inv {r : ZMod q} (hr : IsUnit r) : IsUnit r⁻¹ :=
  isUnit_iff_exists_inv.2 ⟨r, ZMod.inv_mul_of_unit r hr⟩

theorem zmod_inv_neg {r : ZMod q} (hr : IsUnit r) : (-r)⁻¹ = -r⁻¹ := by
  have h1 : (-r) * (-r⁻¹) = 1 := by rw [neg_mul_neg, ZMod.mul_inv_of_unit r hr]
  have h2 : (-r)⁻¹ * (-r) = 1 := ZMod.inv_mul_of_unit _ hr.neg
  calc (-r)⁻¹ = (-r)⁻¹ * ((-r) * (-r⁻¹)) := by rw [h1, mul_one]
    _ = -r⁻¹ := by rw [← mul_assoc, h2, one_mul]

/-- The character coefficients of a weight `w` on `ZMod q` (paper §4.1):
`A_χ = φ(q)^{−1} Σ_{(r,q)=1} w_r χ(r^{−1})`, and `χ(r^{−1}) = χ̄(r)` on units. -/
noncomputable def charCoeff (w : ZMod q → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ r ∈ unitsZMod q, (w r : ℂ) * χ r⁻¹

/-- **The character expansion** (orthogonality): `w_b = Σ_χ A_χ χ(b)` for every unit `b`. -/
theorem sum_charCoeff_mul (w : ZMod q → ℝ) {b : ZMod q} (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, charCoeff w χ * χ b = w b := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hb' : b ∈ unitsZMod q := by simp [unitsZMod, hb]
  calc ∑ χ : DirichletCharacter ℂ q, charCoeff w χ * χ b
      = ∑ χ : DirichletCharacter ℂ q, ∑ r ∈ unitsZMod q,
          (q.totient : ℂ)⁻¹ * ((w r : ℂ) * (χ r⁻¹ * χ b)) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [charCoeff, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ = ∑ r ∈ unitsZMod q, (q.totient : ℂ)⁻¹ * ((w r : ℂ) *
          ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * χ b) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ r ∈ unitsZMod q, if r = b then (w b : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hru : IsUnit r := (Finset.mem_filter.1 hr).2
        rw [sum_char_inv_mul_char_eq ℂ hru b]
        split_ifs with h
        · subst h; field_simp
        · simp
    _ = w b := by rw [Finset.sum_ite_eq' _ _ _, if_pos hb']

/-- The principal character drops out when the weights have mean zero on the units. -/
theorem charCoeff_one (w : ZMod q → ℝ) (hw : ∑ r ∈ unitsZMod q, w r = 0) :
    charCoeff w (1 : DirichletCharacter ℂ q) = 0 := by
  have : ∑ r ∈ unitsZMod q, (w r : ℂ) * (1 : DirichletCharacter ℂ q) r⁻¹ =
      ((∑ r ∈ unitsZMod q, w r : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun r hr => ?_
    have hru : IsUnit r := (Finset.mem_filter.1 hr).2
    rw [MulChar.one_apply (isUnit_zmod_inv hru), mul_one]
  rw [charCoeff, this, hw]; simp

/-- Every odd character drops out when the weights are even, `w(−r) = w(r)`. -/
theorem charCoeff_of_odd (w : ZMod q → ℝ) (hw : ∀ r, w (-r) = w r)
    {χ : DirichletCharacter ℂ q} (hχ : χ (-1) = -1) : charCoeff w χ = 0 := by
  set S := ∑ r ∈ unitsZMod q, (w r : ℂ) * χ r⁻¹
  have hS : S = -S := by
    calc S = ∑ r ∈ unitsZMod q, (w (-r) : ℂ) * χ (-r)⁻¹ := by
          refine Finset.sum_nbij' (fun r => -r) (fun r => -r) (fun r hr => ?_) (fun r hr => ?_)
            (fun r _ => neg_neg r) (fun r _ => neg_neg r) (fun r _ => by rw [neg_neg])
          · simpa [unitsZMod] using (Finset.mem_filter.1 hr).2.neg
          · simpa [unitsZMod] using (Finset.mem_filter.1 hr).2.neg
      _ = -S := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hru : IsUnit r := (Finset.mem_filter.1 hr).2
          rw [hw, zmod_inv_neg hru, neg_eq_neg_one_mul, map_mul, hχ]
          ring
  have : S = 0 := by linear_combination hS / 2
  show (q.totient : ℂ)⁻¹ * S = 0
  rw [this, mul_zero]

/-- The weights on the integers: `w_{n mod q}` when `(n, q) = 1`, `0` otherwise (the primes
`p ∣ q` are left out of `H_{a/q}`). -/
noncomputable def unitWeight (w : ZMod q → ℝ) (n : ℕ) : ℝ :=
  if IsUnit (n : ZMod q) then w n else 0

open _root_.Classical in
/-- The characters seen by the weights: `X = {χ ≠ χ₀ : A_χ ≠ 0}` (paper §4.1). -/
noncomputable def arcChars (w : ZMod q → ℝ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ => χ ≠ 1 ∧ charCoeff w χ ≠ 0

theorem arcChars_ne_one (w : ZMod q → ℝ) : ∀ χ ∈ arcChars w, χ ≠ 1 :=
  fun χ hχ => by
    classical
    unfold arcChars at hχ
    exact (Finset.mem_filter.1 hχ).2.1

/-- **The expansion of §4.1 as a lemma**: with mean-zero weights,
`c_p = Σ_{χ∈X} A_χ χ(p)` for every prime `p`, with `A_χ = φ(q)^{−1} Σ_r c_r χ̄(r)`. -/
theorem isCharCombination_unitWeight (w : ZMod q → ℝ) (hw : ∑ r ∈ unitsZMod q, w r = 0) :
    IsCharCombination (arcChars w) (charCoeff w) (unitWeight w) := by
  classical
  intro p _
  have hsum : ∑ χ ∈ arcChars w, charCoeff w χ * χ p =
      ∑ χ : DirichletCharacter ℂ q, charCoeff w χ * χ p := by
    unfold arcChars
    refine Finset.sum_filter_of_ne fun χ _ h => ⟨?_, ?_⟩
    · rintro rfl; rw [charCoeff_one w hw, zero_mul] at h; exact h rfl
    · intro h0; rw [h0, zero_mul] at h; exact h rfl
  rw [hsum, unitWeight]
  split_ifs with hu
  · rw [sum_charCoeff_mul w hu]
  · simp [MulChar.map_nonunit _ hu]

/-! ### The weights of the paper: `c_r = log|cos(π r a / q)| − w̄(q)` -/

/-- `log|cos(π r a / q)|` for a residue `r` (represented by `r.val`). -/
noncomputable def logCos (q a : ℕ) (r : ZMod q) : ℝ :=
  Real.log |Real.cos (Real.pi * r.val * a / q)|

/-- The arc weights `c_r = log|cos(πra/q)| − w̄(q)`, with `w̄(q)` the mean over the units. -/
noncomputable def arcWeight (q : ℕ) [NeZero q] (a : ℕ) (r : ZMod q) : ℝ :=
  logCos q a r - (∑ r' ∈ unitsZMod q, logCos q a r') / (unitsZMod q).card

theorem sum_arcWeight (a : ℕ) : ∑ r ∈ unitsZMod q, arcWeight q a r = 0 := by
  have hc : ((unitsZMod q).card : ℝ) ≠ 0 := by
    have : (1 : ZMod q) ∈ unitsZMod q := by simp [unitsZMod]
    exact_mod_cast (Finset.card_pos.2 ⟨1, this⟩).ne'
  simp only [arcWeight, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

theorem logCos_neg (a : ℕ) (r : ZMod q) : logCos q a (-r) = logCos q a r := by
  by_cases hr : r = 0
  · simp [hr]
  rw [logCos, logCos, ZMod.neg_val, if_neg hr]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hle : r.val ≤ q := (ZMod.val_lt r).le
  rw [Nat.cast_sub hle]
  have e : Real.pi * ((q : ℝ) - r.val) * a / q = (a : ℝ) * Real.pi - Real.pi * r.val * a / q := by
    field_simp
  rw [e, Real.cos_sub, Real.sin_nat_mul_pi, zero_mul, add_zero, Real.cos_nat_mul_pi, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem arcWeight_neg (a : ℕ) (r : ZMod q) : arcWeight q a (-r) = arcWeight q a r := by
  simp only [arcWeight, logCos_neg]

/-- The odd characters drop out of `X(a/q)` (paper §4.1). -/
theorem charCoeff_arcWeight_of_odd (a : ℕ) {χ : DirichletCharacter ℂ q} (hχ : χ (-1) = -1) :
    charCoeff (arcWeight q a) χ = 0 :=
  charCoeff_of_odd _ (arcWeight_neg a) hχ

/-- **Proposition 3, (2) ⇒ (1), for the arc `a/q`** (zero-free form; the expansion of §4.1 is now
proved): with `H_{a/q}(N) = Σ_{p ≤ N, p ∤ q} c_{p mod q}`, condition (R) on `(1/2, 1]` and (N),
the bounds `H_{a/q}(N) ≤ C_ε N^{1/2+ε}` imply that no `L(s, χ)`, `χ ∈ X(a/q)`, vanishes on
`Re s > 1/2`. -/
theorem prop3_arc_two_imp_zeroFree (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      primeRace (unitWeight (arcWeight q a)) N ≤ C * (N : ℝ) ^ (1 / 2 + ε)) :
    ∀ χ ∈ arcChars (arcWeight q a), ∀ ρ : ℂ, 1 / 2 < ρ.re → LFunction χ ρ ≠ 0 :=
  prop3_two_imp_zeroFree _ (arcChars_ne_one _) _ _
    (isCharCombination_unitWeight _ (sum_arcWeight a)) hR hN h2

/-- **Proposition 3, (3) ⇒ (1), for the arc `a/q`** (zero-free form). -/
theorem prop3_arc_three_imp_zeroFree (a : ℕ)
    (hR : ∀ χ ∈ arcChars (arcWeight q a), ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0)
    (hN : ConditionN (arcChars (arcWeight q a)) (charCoeff (arcWeight q a)) (1 / 2))
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(C * (N : ℝ) ^ (1 / 2 + ε)) ≤ primeRace (unitWeight (arcWeight q a)) N) :
    ∀ χ ∈ arcChars (arcWeight q a), ∀ ρ : ℂ, 1 / 2 < ρ.re → LFunction χ ρ ≠ 0 :=
  prop3_three_imp_zeroFree _ (arcChars_ne_one _) _ _
    (isCharCombination_unitWeight _ (sum_arcWeight a)) hR hN h3

end ArcsAlgo.Classical
