module

public import ArcsAlgo.SecondMoment.BPCondT
public import ArcsAlgo.Uniform.LemmaB3pp
set_option autoImplicit false

/-!
# Proposition B′, unconditional part: lattices, counts and the parity event

`minLat_Xu` (index 2), `minLat_Yu` (index 1), `lawXu_eq`, `lawYu_eq` (the counts without conditioning), the
conditional moments on the event `S_E ≡ u (mod 2)` (`m2U`, `lamU`, `parE`), and
`|Pr(S_E ≡ u (mod 2)) − 1/2| ≤ M^{−m}/2` (`parE_near`).
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-! ### The lattices of `X′ = (εw, ε′w)` and `Y′ = εw` -/

theorem closure_Xu (hM : 2 ≤ M) :
    AddSubgroup.closure {v | ∃ a b : Fin M × Bool × Bool, v = xiXu M a - xiXu M b} = parY.ker := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro v ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, mem_ker_parY]
    have h1 := sg_mul_sub a.2.1 ((a.1 : ℤ) + 1)
    have h2 := sg_mul_sub a.2.2 ((a.1 : ℤ) + 1)
    have h3 := sg_mul_sub b.2.1 ((b.1 : ℤ) + 1)
    have h4 := sg_mul_sub b.2.2 ((b.1 : ℤ) + 1)
    simp only [xiXu, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    omega
  · intro v hv
    rw [mem_ker_parY] at hv
    obtain ⟨k, hk⟩ := hv
    set S := {v | ∃ a b : Fin M × Bool × Bool, v = xiXu M a - xiXu M b}
    have i0 : (0 : ℕ) < M := by omega
    have i1 : (1 : ℕ) < M := by omega
    have g1 : ![1, 1] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨1, i1⟩, true, true), (⟨0, i0⟩, true, true), by ext j; fin_cases j <;> simp [xiXu, sg] <;> (try norm_num)⟩
    have g2 : ![0, 2] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨0, i0⟩, true, true), (⟨0, i0⟩, true, false), by ext j; fin_cases j <;> simp [xiXu, sg] <;> (try norm_num)⟩
    have : v = v 0 • ![1, 1] + k • ![0, 2] := by
      ext j; fin_cases j <;> simp <;> omega
    rw [this]
    exact add_mem (AddSubgroup.zsmul_mem _ g1 _) (AddSubgroup.zsmul_mem _ g2 _)

theorem closure_Yu (hM : 2 ≤ M) :
    AddSubgroup.closure {v | ∃ a b : Fin M × Bool, v = xiYu M a - xiYu M b} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have i0 : (0 : ℕ) < M := by omega
  have i1 : (1 : ℕ) < M := by omega
  have g1 : ![1] ∈ AddSubgroup.closure {v | ∃ a b : Fin M × Bool, v = xiYu M a - xiYu M b} :=
    AddSubgroup.subset_closure ⟨(⟨1, i1⟩, true), (⟨0, i0⟩, true), by ext j; fin_cases j; simp [xiYu, sg]; (try norm_num)⟩
  have : v = v 0 • ![1] := by ext j; fin_cases j; simp
  rw [this]; exact AddSubgroup.zsmul_mem _ g1 _

theorem minLat_Xu (hM : 2 ≤ M) : minLat (pX M) (xiXu M) = parY.ker := by
  rw [minLat_const (by have : (0 : ℝ) < M := (by exact_mod_cast (by omega : 0 < M)); positivity),
    closure_Xu hM]

theorem minLat_Yu (hM : 2 ≤ M) : minLat (pY M) (xiYu M) = ⊤ := by
  rw [minLat_const (by have : (0 : ℝ) < M := (by exact_mod_cast (by omega : 0 < M)); positivity),
    closure_Yu hM]

theorem posDef_Xu (hM : 2 ≤ M) : (vcov (pX M) (xiXu M)).PosDef := by
  rw [vcov_Xu (by omega), posDef_diagonal_iff]
  intro i; fin_cases i <;> simp [ew2_pos]

theorem posDef_Yu (hM : 2 ≤ M) : (vcov (pY M) (xiYu M)).PosDef := by
  rw [vcov_Yu (by omega), posDef_diagonal_iff]
  intro i; fin_cases i; simp [ew2_pos]

/-! ### The counts without conditioning -/

theorem card_Xu {m : ℕ} (u : ℤ) :
    (univ.filter fun ω : Fin m → Fin M × Bool × Bool => ∑ i, xiXu M (ω i) = ![u, u]).card =
      ∑ w : Fin m → Fin M, Zc w u ^ 2 := by
  let e : (Fin m → Fin M × Bool × Bool) ≃ (Fin m → Fin M) × ((Fin m → Bool) × (Fin m → Bool)) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2.1, fun i => (ω i).2.2)
      invFun := fun t i => (t.1 i, t.2.1 i, t.2.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_equiv e _ (fun t => if Tsg t.1 t.2.1 = u ∧ Tsg t.1 t.2.2 = u then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun w _ => ?_
    rw [sq, Zc, card_eq_sum_ones, sum_filter, sum_mul_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun ε _ => sum_congr rfl fun ε' _ => ?_
    by_cases h1 : Tsg w ε = u <;> by_cases h2 : Tsg w ε' = u <;> simp [h1, h2]
  · intro ω
    simp only [vec2_eq, Finset.sum_apply, xiXu, Tsg, e, Equiv.coe_fn_mk]
    simp

theorem card_Yu {m : ℕ} (u : ℤ) :
    (univ.filter fun ω : Fin m → Fin M × Bool => ∑ i, xiYu M (ω i) = ![u]).card =
      ∑ w : Fin m → Fin M, Zc w u := by
  let e : (Fin m → Fin M × Bool) ≃ (Fin m → Fin M) × (Fin m → Bool) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
      invFun := fun t i => (t.1 i, t.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_equiv e _ (fun t => if Tsg t.1 t.2 = u then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun w _ => ?_
    rw [Zc, card_eq_sum_ones, sum_filter]
  · intro ω
    simp only [vec1_eq, Finset.sum_apply, xiYu, Tsg, e, Equiv.coe_fn_mk]
    simp

theorem lawXu_eq (M m : ℕ) (u : ℤ) :
    lawPow (pX M) (xiXu M) m ![u, u] = (1 / (4 * M) : ℝ) ^ m * ∑ w : Fin m → Fin M, (Zc w u : ℝ) ^ 2 := by
  show lawPow (fun _ => (1 / (4 * M) : ℝ)) (xiXu M) m ![u, u] = _
  rw [lawPow_const, card_Xu]; push_cast; rfl

theorem lawYu_eq (M m : ℕ) (u : ℤ) :
    lawPow (pY M) (xiYu M) m ![u] = (1 / (2 * M) : ℝ) ^ m * ∑ w : Fin m → Fin M, (Zc w u : ℝ) := by
  show lawPow (fun _ => (1 / (2 * M) : ℝ)) (xiYu M) m ![u] = _
  rw [lawPow_const, card_Yu]; push_cast; rfl

/-! ### The event `S_E ≡ u (mod 2)` -/

/-- `Pr(S_E ≡ u (mod 2))`. -/
noncomputable def parE (M m : ℕ) (u : ℤ) : ℝ := prW M m (fun w => (2 : ℤ) ∣ Sw w - u)

/-- `E[Z(u)² | S_E ≡ u (mod 2)]`. -/
noncomputable def m2U (M m : ℕ) (u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => (2 : ℤ) ∣ Sw w - u), (Zc w u : ℝ) ^ 2) / (M : ℝ) ^ m / parE M m u

/-- `E[Z(u) | S_E ≡ u (mod 2)]`. -/
noncomputable def lamU (M m : ℕ) (u : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => (2 : ℤ) ∣ Sw w - u), (Zc w u : ℝ)) / (M : ℝ) ^ m / parE M m u

/-- `Z(u) = 0` off the event `S_E ≡ u (mod 2)`. -/
theorem Zc_off (w : Fin m → Fin M) (u : ℤ) (h : ¬ (2 : ℤ) ∣ Sw w - u) : Zc w u = 0 := by
  apply Zc_parity
  rintro ⟨a, ha⟩
  exact h ⟨a - u, by omega⟩

theorem sum_filter_par {f : (Fin m → Fin M) → ℝ} (u : ℤ) (hf : ∀ w, Zc w u = 0 → f w = 0) :
    ∑ w ∈ univ.filter (fun w : Fin m → Fin M => (2 : ℤ) ∣ Sw w - u), f w = ∑ w, f w := by
  rw [sum_filter]
  refine sum_congr rfl fun w _ => ?_
  split_ifs with h
  · rfl
  · exact (hf w (Zc_off w u h)).symm

/-- The alternating sum `Σ_{a=1}^{M} (−1)^a` is `0` or `−1`. -/
theorem alt_sum_abs (M : ℕ) : |∑ a : Fin M, (-1 : ℝ) ^ ((a : ℕ) + 1)| ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℝ) ^ (i + 1))]
  have : ∀ n : ℕ, ∑ i ∈ range n, (-1 : ℝ) ^ (i + 1) = if Even n then 0 else -1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih]
      rcases Nat.even_or_odd k with hk | hk
      · rw [if_pos hk, if_neg (by rw [Nat.not_even_iff_odd]; exact hk.add_one), Odd.neg_one_pow hk.add_one]; ring
      · rw [if_neg (Nat.not_even_iff_odd.mpr hk), if_pos hk.add_one, Even.neg_one_pow hk.add_one]; ring
  rw [this]; split_ifs <;> simp

theorem ind_two_dvd (n : ℕ) (u : ℤ) :
    (if (2 : ℤ) ∣ (n : ℤ) - u then (1 : ℝ) else 0) = (1 + (-1 : ℝ) ^ n * (-1) ^ u.natAbs) / 2 := by
  rcases Nat.even_or_odd n with hn | hn <;> rcases Nat.even_or_odd u.natAbs with hu | hu
  · rw [hn.neg_one_pow, hu.neg_one_pow, if_pos]; · norm_num
    obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hu
    rcases Int.natAbs_eq u with h | h <;> [exact ⟨a - b, by rw [h]; push_cast [ha, hb]; ring⟩;
      exact ⟨a + b, by rw [h]; push_cast [ha, hb]; ring⟩]
  · rw [hn.neg_one_pow, hu.neg_one_pow, if_neg]; · norm_num
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hu
    rcases Int.natAbs_eq u with h | h <;> rw [h] at hk <;> push_cast [ha, hb] at hk <;> omega
  · rw [hn.neg_one_pow, hu.neg_one_pow, if_neg]; · norm_num
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hu
    rcases Int.natAbs_eq u with h | h <;> rw [h] at hk <;> push_cast [ha, hb] at hk <;> omega
  · rw [hn.neg_one_pow, hu.neg_one_pow, if_pos]; · norm_num
    obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hu
    rcases Int.natAbs_eq u with h | h <;> [exact ⟨a - b, by rw [h]; push_cast [ha, hb]; ring⟩;
      exact ⟨a + b + 1, by rw [h]; push_cast [ha, hb]; ring⟩]

/-- **The parity of `S_E`**: `|Pr(S_E ≡ u (mod 2)) − 1/2| ≤ M^{−m}/2`. -/
theorem parE_near (hM : 1 ≤ M) (m : ℕ) (u : ℤ) : |parE M m u - 1 / 2| ≤ 1 / (2 * (M : ℝ) ^ m) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  unfold parE prW
  have hS : ∀ w : Fin m → Fin M, Sw w = ((∑ i, ((w i : ℕ) + 1) : ℕ) : ℤ) := fun w => by
    unfold Sw; push_cast; rfl
  simp only [hS, ind_two_dvd]
  rw [← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, ← sum_mul]
  have hp : ∀ w : Fin m → Fin M, (-1 : ℝ) ^ (∑ i, ((w i : ℕ) + 1)) = ∏ i, (-1 : ℝ) ^ ((w i : ℕ) + 1) :=
    fun w => (Finset.prod_pow_eq_pow_sum _ _ _).symm
  simp only [hp]
  rw [← Fintype.sum_pow (fun a : Fin M => (-1 : ℝ) ^ ((a : ℕ) + 1)) m]
  have hb := alt_sum_abs M
  have hpow : |(∑ a : Fin M, (-1 : ℝ) ^ ((a : ℕ) + 1)) ^ m| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hb
  have hu : |(-1 : ℝ) ^ u.natAbs| = 1 := by simp
  simp only [Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  rw [show ((M : ℝ) ^ m + (∑ a : Fin M, (-1 : ℝ) ^ ((a : ℕ) + 1)) ^ m * (-1) ^ u.natAbs) / 2 / (M : ℝ) ^ m - 1 / 2 =
    ((∑ a : Fin M, (-1 : ℝ) ^ ((a : ℕ) + 1)) ^ m * (-1) ^ u.natAbs) / (2 * (M : ℝ) ^ m) by field_simp; ring]
  have h2M : (0 : ℝ) < 2 * (M : ℝ) ^ m := mul_pos two_pos (pow_pos hM0 m)
  rw [abs_div, abs_of_pos h2M, abs_mul, hu, mul_one]
  exact div_le_div_of_nonneg_right hpow h2M.le

end ArcsAlgo.LLT
