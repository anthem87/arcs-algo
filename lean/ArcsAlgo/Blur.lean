module

public import ArcsAlgo.Exhaustive
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
set_option autoImplicit false

/-!
# Dummies, blur and de-blurring (paper §5.4)

Counts of subset sums are the coefficients of `F_W(z) = ∏_{w ∈ W} (1 + z^w)`.

* `count W T`: the number of sub-multisets of `W` (subsets of indices) with sum `T`, and
  `coeff_F`: it is the coefficient of `z^T` in `F_W`.
* `blur_identity`: with the dummies `D = {1, 2, …, 2^{k−1}}`, `F_{W ∪ D} (1 − z) = F_W (1 − z^M)`,
  `M = 2^k`.
* `blur_recovery`: `r_W(T) − r_W(T − M) = r_{W∪D}(T) − r_{W∪D}(T − 1)`.
* `gap_lemma`: Lemma 5.1.
* `blur_factor_singular`: the second reading of Remark 5.2 (`1 + x^d` is a zero divisor in
  `ℤ[x]/(x^q − 1)` iff the cycle length `q / gcd(q, d)` is even).
-/

@[expose] public section

namespace ArcsAlgo

open Polynomial Finset

/-- Number of sub-multisets of `W` (counted by positions) with sum `T`: the count `r_W(T)` of
paper §3.1 and §5.4. -/
def count (W : List ℕ) (T : ℕ) : ℕ := W.sublists'.countP (fun L => L.sum = T)

/-- The generating polynomial `F_W(z) = ∏_{w ∈ W} (1 + z^w)` (paper §3.1). -/
noncomputable def F (W : List ℕ) : ℤ[X] := (W.map fun w => (1 + X ^ w : ℤ[X])).prod

/-- The dummies `1, 2, …, 2^{k−1}` of paper §5.4. -/
def dummies (k : ℕ) : List ℕ := (List.range k).map (2 ^ ·)

theorem count_nil (T : ℕ) : count [] T = if T = 0 then 1 else 0 := by
  by_cases h : T = 0 <;> simp [count, h, eq_comm]

private theorem countP_cons_sum (w T : ℕ) (l : List (List ℕ)) :
    (l.map (List.cons w)).countP (fun L => L.sum = T) =
      if w ≤ T then l.countP (fun L => L.sum = T - w) else 0 := by
  rw [List.countP_map]
  split_ifs with h
  · apply List.countP_congr
    intro L _
    constructor
    · intro h'
      have := of_decide_eq_true h'
      rw [List.sum_cons] at this
      exact decide_eq_true (by omega)
    · intro h'
      have := of_decide_eq_true h'
      show decide ((w :: L).sum = T) = true
      exact decide_eq_true (by rw [List.sum_cons]; omega)
  · rw [List.countP_eq_zero]
    intro L _ h'
    have := of_decide_eq_true h'
    rw [List.sum_cons] at this
    omega

theorem count_cons (w : ℕ) (W : List ℕ) (T : ℕ) :
    count (w :: W) T = count W T + if w ≤ T then count W (T - w) else 0 := by
  rw [count, List.sublists'_cons, List.countP_append, countP_cons_sum]
  rfl

/-- Counts are coefficients of the generating polynomial (paper §3.1, Remark 3.1). -/
theorem coeff_F (W : List ℕ) (T : ℕ) : (F W).coeff T = count W T := by
  induction W generalizing T with
  | nil => simp [F, count_nil, coeff_one]
  | cons w W ih =>
    simp only [F, List.map_cons, List.prod_cons] at ih ⊢
    rw [add_mul, one_mul, coeff_add, coeff_X_pow_mul', ih, count_cons]
    split_ifs <;> simp [ih]

/-- A count is positive exactly when the target is a subset sum. -/
theorem count_pos_iff (W : List ℕ) (T : ℕ) : 0 < count W T ↔ IsSubsetSum W T := by
  rw [count, List.countP_pos_iff, isSubsetSum_iff_sublist]
  simp [List.mem_sublists']

theorem F_append (A B : List ℕ) : F (A ++ B) = F A * F B := by
  simp [F, List.prod_append]

theorem F_dummies_mul (k : ℕ) : F (dummies k) * (1 - X) = 1 - X ^ (2 ^ k) := by
  induction k with
  | zero => simp [F, dummies]
  | succ k ih =>
    have : F (dummies (k + 1)) = F (dummies k) * (1 + X ^ (2 ^ k)) := by
      simp [F, dummies, List.range_succ, List.prod_append]
    rw [this, mul_right_comm, ih, pow_succ, pow_mul]
    ring

/-- **Blur identity** (paper §5.4): with the dummies `D = {1, 2, …, 2^{k−1}}`,
`F_{W ∪ D}(z)(1 − z) = F_W(z)(1 − z^M)`, `M = 2^k`, that is
`F_{W∪D} = F_W (1 − z^M)/(1 − z)`. -/
theorem blur_identity (W : List ℕ) (k : ℕ) :
    F (W ++ dummies k) * (1 - X) = F W * (1 - X ^ (2 ^ k)) := by
  rw [F_append, mul_assoc, F_dummies_mul]

/-- Counts extended by zero to negative targets. -/
def countZ (W : List ℕ) (T : ℤ) : ℤ := if T < 0 then 0 else (count W T.toNat : ℤ)

private theorem countZ_nat (W : List ℕ) (t : ℕ) : countZ W t = count W t := by
  simp [countZ]

private theorem countZ_sub (W : List ℕ) (t n : ℕ) :
    countZ W ((t : ℤ) - n) = if n ≤ t then (count W (t - n) : ℤ) else 0 := by
  unfold countZ
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · rw [show ((t : ℤ) - n).toNat = t - n by omega]
  · omega

private theorem coeff_mul_one_sub_X_pow (p : ℤ[X]) (n T : ℕ) :
    (p * (1 - X ^ n)).coeff T = p.coeff T - if n ≤ T then p.coeff (T - n) else 0 := by
  rw [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']

/-- **Exact recovery** (paper §5.4): the dummy-free counts are recovered from the blurred ones,
`r_W(T) − r_W(T − M) = r_{W∪D}(T) − r_{W∪D}(T − 1)` for every integer `T`. -/
theorem blur_recovery (W : List ℕ) (k : ℕ) (T : ℤ) :
    countZ W T - countZ W (T - 2 ^ k) =
      countZ (W ++ dummies k) T - countZ (W ++ dummies k) (T - 1) := by
  rcases lt_or_ge T 0 with hT | hT
  · have h2 : (0 : ℤ) < 2 ^ k := by positivity
    simp [countZ, hT, show T - 2 ^ k < 0 by omega, show T - 1 < 0 by omega]
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hT
  have h := congrArg (fun p => p.coeff t) (blur_identity W k)
  have h1 := coeff_mul_one_sub_X_pow (F (W ++ dummies k)) 1 t
  have h2 := coeff_mul_one_sub_X_pow (F W) (2 ^ k) t
  rw [pow_one] at h1
  simp only [h1, h2, coeff_F] at h
  have e1 : ((t : ℤ) - 2 ^ k) = (t : ℤ) - ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((t : ℤ) - 1) = (t : ℤ) - ((1 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, countZ_sub, countZ_sub, countZ_nat, countZ_nat]
  have := h
  split_ifs at h ⊢ <;> linarith

/-- **Lemma 5.1 (gap lemma)** (paper §5.4): if `W ∪ D` is complete (every integer of
`[0, Σ_W + Σ_D]` is a subset sum), every interval `[a, a + Σ_D] ⊆ [0, Σ_W]` of length
`Σ_D + 1` contains a subset sum of `W`. -/
theorem gap_lemma (W D : List ℕ)
    (hcomplete : ∀ T ≤ (W ++ D).sum, IsSubsetSum (W ++ D) T) (a : ℕ) (ha : a + D.sum ≤ W.sum) :
    ∃ t, a ≤ t ∧ t ≤ a + D.sum ∧ IsSubsetSum W t := by
  obtain ⟨sW, sD, hW, hD, hsum⟩ :=
    isSubsetSum_append.1 (hcomplete (a + D.sum) (by simp [List.sum_append]; omega))
  exact ⟨sW, by have := le_sum_of_isSubsetSum hD; omega, by omega, hW⟩

/-! ### Remark 5.2: the factor `1 + x^d` on `ℤ[x]/(x^q − 1)`

An element of `ℤ[x]/(x^q − 1)` is a function `v : ZMod q → ℤ` (its coefficients), and
multiplication by `1 + x^d` is `v ↦ (c ↦ v c + v (c − d))`, that is `I + P^d` with `P` the cyclic
shift. -/

/-- Multiplication by `1 + x^d` in `ℤ[x]/(x^q − 1)`, on coefficient functions. -/
def blurFactor (q d : ℕ) (v : ZMod q → ℤ) : ZMod q → ℤ := fun c => v c + v (c - d)

private theorem iterate_relation {q d : ℕ} {v : ZMod q → ℤ} (hv : ∀ c, v c + v (c - d) = 0)
    (c : ZMod q) (t : ℕ) : v (c - t • (d : ZMod q)) = (-1) ^ t * v c := by
  induction t with
  | zero => simp
  | succ t ih =>
    have := hv (c - t • (d : ZMod q))
    rw [succ_nsmul, ← sub_sub, pow_succ]
    linarith

/-- **Remark 5.2** (paper §5.4, second reading of the blur): `I + P^d` is singular on
`ℤ[x]/(x^q − 1)` (multiplication by `1 + x^d` has a non-zero kernel) if and only if the cycle
length `q / gcd(q, d)` of `Cay(ℤ/q, {d})` is even. When it is odd the map is injective, so the
exact division of §5.4 is well defined. -/
theorem blur_factor_singular (q d : ℕ) [NeZero q] :
    (∃ v : ZMod q → ℤ, v ≠ 0 ∧ blurFactor q d v = 0) ↔ Even (q / Nat.gcd q d) := by
  have hL : addOrderOf (d : ZMod q) = q / Nat.gcd q d := ZMod.addOrderOf_coe d (NeZero.ne q)
  rw [← hL]
  set L := addOrderOf (d : ZMod q) with hLdef
  have hLpos : 0 < L := addOrderOf_pos _
  have hLd : L • (d : ZMod q) = 0 := addOrderOf_nsmul_eq_zero _
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hv' : ∀ c, v c + v (c - d) = 0 := fun c => congrFun hv c
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    apply hv0
    funext c
    have := iterate_relation hv' c L
    rw [hLd, sub_zero, hodd.neg_one_pow] at this
    simp only [Pi.zero_apply]
    linarith
  · intro heven
    let a : ZMod q → ℕ → ℤ := fun c t => (-1) ^ t * if c = t • (d : ZMod q) then 1 else 0
    refine ⟨fun c => ∑ t ∈ range L, a c t, ?_, ?_⟩
    · intro h0
      have h := congrFun h0 0
      simp only [Pi.zero_apply] at h
      rw [Finset.sum_eq_single 0] at h
      · simp [a] at h
      · intro t ht ht0
        have hne : (0 : ZMod q) ≠ t • (d : ZMod q) := by
          intro h'
          have := addOrderOf_le_of_nsmul_eq_zero (Nat.pos_of_ne_zero ht0) h'.symm
          rw [Finset.mem_range] at ht
          omega
        rw [nsmul_eq_mul] at hne
        simp [a, hne]
      · intro h; exact absurd (Finset.mem_range.2 hLpos) h
    · funext c
      simp only [blurFactor, Pi.zero_apply]
      have hshift : ∀ t, a (c - d) t = - a c (t + 1) := by
        intro t
        simp only [a, succ_nsmul, sub_eq_iff_eq_add, pow_succ]
        split_ifs <;> ring
      simp only [hshift, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
      simp only [a, hLd, heven.neg_one_pow, zero_smul, pow_zero]
      ring

end ArcsAlgo
