module

public import ArcsAlgo.Uniform.LVRest
public import ArcsAlgo.Uniform.LemmaB3pp
public import ArcsAlgo.Uniform.Unif
public import ArcsAlgo.Uniform.LemV1
set_option autoImplicit false

/-!
# Theorem LV: few good weights, given the block sum (paper §6.6)

Writing each weight as a bit and a uniform variable on `M/2` values (`splitE`, `eH`, `eP`), given the
bits `S_E` is a sum of uniform variables, so by Lemma B0′
`Pr(20·#{i : b_i = b₀} < m, S_E = s) ≤ (5/8)^m · 13/(σ′√m)` (`prW_few_le`), with the count of
`b ∈ {0,1}^m` by a Chernoff bound (`card_few_le`).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

variable {m M : ℕ}

/-- `#{h ∈ {0,1}^m : 20·#{i : h_i = b₀} < m} ≤ (5/4)^m` (a Chernoff bound with `x = 23/20`). -/
theorem card_few_le (b₀ : Fin 2) :
    (∑ h : Fin m → Fin 2, if 20 * (univ.filter fun i => h i = b₀).card < m then (1 : ℝ) else 0) ≤
      (5 / 4 : ℝ) ^ m := by
  set x : ℝ := 23 / 20
  set y : ℝ := (20 / 23) ^ 20
  have hx : (1 : ℝ) ≤ x := by norm_num [x]
  have hxy : x ^ 20 * y = 1 := by simp only [x, y]; rw [← mul_pow]; norm_num
  have hy : 0 < y := by positivity
  have h1 : ∀ h : Fin m → Fin 2, (if 20 * (univ.filter fun i => h i = b₀).card < m then (1 : ℝ) else 0) ≤
      x ^ m * ∏ i, (if h i = b₀ then y else 1) := by
    intro h
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    set c := (univ.filter fun i => h i = b₀).card
    split_ifs with hc
    · have : x ^ (20 * c) ≤ x ^ m := pow_le_pow_right₀ hx (by omega)
      have e : x ^ m * y ^ c = x ^ m / x ^ (20 * c) := by
        rw [pow_mul, eq_div_iff (by positivity), mul_assoc, ← mul_pow, mul_comm y, hxy, one_pow, mul_one]
      rw [e, le_div_iff₀ (by positivity), one_mul]; exact this
    · positivity
  calc _ ≤ ∑ h : Fin m → Fin 2, x ^ m * ∏ i, (if h i = b₀ then y else 1) := sum_le_sum fun h _ => h1 h
    _ = x ^ m * (∑ b : Fin 2, if b = b₀ then y else 1) ^ m := by
        rw [← mul_sum, Fintype.sum_pow (fun b : Fin 2 => if b = b₀ then y else 1) m]
    _ = (x * (1 + y)) ^ m := by
        rw [mul_pow]; congr 2
        fin_cases b₀ <;> simp [Fin.sum_univ_two] <;> ring
    _ ≤ (5 / 4 : ℝ) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        norm_num [x, y]

/-- Splitting each weight through `e : {0,1} × {1,…,M′} ≃ {1,…,M}`. -/
def splitE {M' : ℕ} (e : Fin 2 × Fin M' ≃ Fin M) : (Fin m → Fin 2) × (Fin m → Fin M') ≃ (Fin m → Fin M) where
  toFun p i := e (p.1 i, p.2 i)
  invFun w := (fun i => (e.symm (w i)).1, fun i => (e.symm (w i)).2)
  left_inv p := by ext i <;> simp
  right_inv w := by funext i; simp

/-- The number of weights whose first coordinate under `e` is `b₀`. -/
def cntE {M' : ℕ} (e : Fin 2 × Fin M' ≃ Fin M) (b₀ : Fin 2) (w : Fin m → Fin M) : ℕ :=
  (univ.filter fun i => (e.symm (w i)).1 = b₀).card

set_option maxHeartbeats 1000000 in
/-- **Few weights of one kind, given `S_E = s`.** If `w = A(b) + B·y` with `y` uniform in
`{1, …, M′}` given the bit `b`, then
`Pr(20·#{i : b_i = b₀} < m, S_E = s) ≤ (5/8)^m · 13/(σ′√m)`. -/
theorem prW_few_le {M' : ℕ} (hM' : 2 ≤ M') (hM : M = 2 * M') (hm : 2 ≤ m) (e : Fin 2 × Fin M' ≃ Fin M)
    (A : Fin 2 → ℤ) (B : ℤ) (hB : 0 < B)
    (he : ∀ b y, (((e (b, y) : ℕ) : ℤ) + 1) = A b + B * (((y : ℕ) : ℤ) + 1)) (b₀ : Fin 2) (s : ℤ) :
    prW M m (fun w => 20 * cntE e b₀ w < m ∧ Sw w = s) ≤
      (5 / 8 : ℝ) ^ m * (13 / (√(sig2 M') * √(m : ℝ))) := by
  have hM'0 : (0 : ℝ) < M' := by exact_mod_cast (by omega : 0 < M')
  set K := 13 / (√(sig2 M') * √(m : ℝ))
  have hK : 0 ≤ K := by
    have := sig2_pos (by omega : 2 ≤ M'); positivity
  -- for fixed `h`, the sum over `y`
  have hy : ∀ r : ℤ, (∑ y : Fin m → Fin M', if B * Sw y = r then (1 : ℝ) else 0) ≤ (M' : ℝ) ^ m * K := by
    intro r
    have h1 : ∀ y : Fin m → Fin M', (if B * Sw y = r then (1 : ℝ) else 0) ≤ if Sw y = r / B then 1 else 0 := by
      intro y; split_ifs with h2 h3 <;> try norm_num
      exact h3 (by rw [← h2, Int.mul_ediv_cancel_left _ hB.ne'])
    refine (sum_le_sum fun y _ => h1 y).trans ?_
    have hl := lawS_le_max hM' hm (r / B)
    rw [lawS_eq_card, div_le_iff₀ (pow_pos hM'0 m)] at hl
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, mul_comm]
    exact hl
  have hM0 : (0 : ℝ) < M := by rw [show (M : ℝ) = 2 * M' by exact_mod_cast hM]; positivity
  unfold prW
  rw [div_le_iff₀ (pow_pos hM0 m)]
  rw [← (splitE (m := m) e).sum_comp, Fintype.sum_prod_type]
  have hS : ∀ h : Fin m → Fin 2, ∀ y : Fin m → Fin M', Sw (splitE e (h, y)) = ∑ i, A (h i) + B * Sw y := by
    intro h y
    unfold Sw splitE; simp only [Equiv.coe_fn_mk]
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => he _ _
  have hc : ∀ h : Fin m → Fin 2, ∀ y : Fin m → Fin M', cntE e b₀ (splitE e (h, y)) =
      (univ.filter fun i => h i = b₀).card := by
    intro h y; unfold cntE splitE; simp
  calc ∑ h : Fin m → Fin 2, ∑ y : Fin m → Fin M',
        (if 20 * cntE e b₀ (splitE e (h, y)) < m ∧ Sw (splitE e (h, y)) = s then (1 : ℝ) else 0)
      = ∑ h : Fin m → Fin 2, (if 20 * (univ.filter fun i => h i = b₀).card < m then (1 : ℝ) else 0) *
          ∑ y : Fin m → Fin M', (if B * Sw y = s - ∑ i, A (h i) then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun h _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [hc, hS]
        by_cases h1 : 20 * (univ.filter fun i => h i = b₀).card < m
        · by_cases h2 : B * Sw y = s - ∑ i, A (h i)
          · rw [if_pos ⟨h1, by linarith⟩, if_pos h1, if_pos h2, mul_one]
          · rw [if_neg (fun h3 => h2 (by linarith [h3.2])), if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg (fun h3 => h1 h3.1), if_neg h1, zero_mul]
    _ ≤ ∑ h : Fin m → Fin 2, (if 20 * (univ.filter fun i => h i = b₀).card < m then (1 : ℝ) else 0) *
          ((M' : ℝ) ^ m * K) := by
        refine sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hy _) (by positivity)
    _ ≤ (5 / 4 : ℝ) ^ m * ((M' : ℝ) ^ m * K) := by
        rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (card_few_le b₀) (by positivity)
    _ = (5 / 8 : ℝ) ^ m * K * (M : ℝ) ^ m := by
        have hMr : (M : ℝ) = 2 * M' := by exact_mod_cast hM
        rw [hMr, mul_pow, show (5 / 4 : ℝ) ^ m = (5 / 8) ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
        ring

/-! ### The two splittings for `M = 2M′` -/

/-- High half: `w = y + M′·b`. -/
def eH {M' : ℕ} (hM : M = 2 * M') : Fin 2 × Fin M' ≃ Fin M :=
  finProdFinEquiv.trans (finCongr hM.symm)

/-- Parity: `w = p + 2y`. -/
def eP {M' : ℕ} (hM : M = 2 * M') : Fin 2 × Fin M' ≃ Fin M :=
  (Equiv.prodComm (Fin 2) (Fin M')).trans (finProdFinEquiv.trans (finCongr (by rw [hM, mul_comm])))

theorem eH_val {M' : ℕ} (hM : M = 2 * M') (b : Fin 2) (y : Fin M') :
    ((eH hM (b, y) : ℕ)) = y + M' * b := by
  simp [eH, finProdFinEquiv_apply_val]

theorem eP_val {M' : ℕ} (hM : M = 2 * M') (b : Fin 2) (y : Fin M') :
    ((eP hM (b, y) : ℕ)) = b + 2 * y := by
  simp [eP, finProdFinEquiv_apply_val]

theorem eH_formula {M' : ℕ} (hM : M = 2 * M') (b : Fin 2) (y : Fin M') :
    (((eH hM (b, y) : ℕ) : ℤ) + 1) = (M' * (b : ℕ) : ℤ) + 1 * (((y : ℕ) : ℤ) + 1) := by
  rw [eH_val]; push_cast; ring

theorem eP_formula {M' : ℕ} (hM : M = 2 * M') (b : Fin 2) (y : Fin M') :
    (((eP hM (b, y) : ℕ) : ℤ) + 1) = (((b : ℕ) : ℤ) - 1) + 2 * (((y : ℕ) : ℤ) + 1) := by
  rw [eP_val]; push_cast; ring

/-- Weights in the high half are `> M/2`, so `V ≥ cnt·M²/4`. -/
theorem Vw_ge_cntH {M' : ℕ} (hM : M = 2 * M') (w : Fin m → Fin M) :
    (cntE (eH hM) 1 w : ℝ) * (M : ℝ) ^ 2 / 4 ≤ Vw w := by
  unfold Vw cntE
  have hsub : ∑ i ∈ univ.filter (fun i => ((eH hM).symm (w i)).1 = 1), (((w i : ℕ) : ℝ) + 1) ^ 2 ≤
      ∑ i, (((w i : ℕ) : ℝ) + 1) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  refine le_trans ?_ hsub
  rw [mul_div_assoc, ← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun i hi => ?_
  have hb := (mem_filter.mp hi).2
  have hv : ((w i : ℕ)) = (((eH hM).symm (w i)).2 : ℕ) + M' * 1 := by
    have := eH_val hM ((eH hM).symm (w i)).1 ((eH hM).symm (w i)).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply, hb] at this
    simpa using this
  have : (M : ℝ) / 2 ≤ ((w i : ℕ) : ℝ) + 1 := by
    have hMr : (M : ℝ) = 2 * M' := by exact_mod_cast hM
    rw [hv, hMr]; push_cast; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (((eH hM).symm (w i)).2 : ℕ))]
  calc (M : ℝ) ^ 2 / 4 = ((M : ℝ) / 2) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) this 2

/-- Parity bit `0` means an odd weight. -/
theorem cntP_le_odd {M' : ℕ} (hM : M = 2 * M') (w : Fin m → Fin M) : cntE (eP hM) 0 w ≤ oddCnt w := by
  unfold cntE oddCnt
  refine card_le_card fun i hi => ?_
  rw [mem_filter] at hi ⊢
  refine ⟨mem_univ _, ?_⟩
  have := eP_val hM ((eP hM).symm (w i)).1 ((eP hM).symm (w i)).2
  rw [Prod.mk.eta, Equiv.apply_symm_apply, hi.2] at this
  simp at this; omega

end ArcsAlgo.LLT
