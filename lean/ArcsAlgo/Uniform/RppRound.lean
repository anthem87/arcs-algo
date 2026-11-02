module

public import ArcsAlgo.Uniform.LemV2
public import ArcsAlgo.Classical.PropK
set_option autoImplicit false

/-!
# Theorem R″: one round (paper §6.7)

The filtered endgame on a block `E` of `m` weights conditioned on `S_E = s`, with the scheme `𝒫₁`
(halves `A`, `B = E ∖ A`): `P` uniform among the primes of `[P₀, 2P₀)`, `r` uniform in `ℤ/P`; the
round succeeds iff some `x ⊆ E` has `S_x = a` and `S_{x∩A} ≡ r (mod P)` (`succB`).

* `sum_eqPairs`: `E#{(x, x′) hitting a, S_{x∩A} = S_{x′∩A}} = λ + D_eq` (diagonal and Lemma V).
* `succB_ge`: Lemma J (`roundSuccess_ge`) and Proposition K′ (`kprime`) give
  `Pr(round succeeds) ≥ λ²/(2P₀(λ + D_eq) + 6 ln(mM)·E Z²)`.
* `p_alg`, `succB_unif`: with Lemmas B(1), B(2) and V, uniformly in `M ≥ 2`, in the window and in
  `P₀ ≥ 100`, `Pr(round succeeds) ≥ p/(1 + ε)` for `m ≥ m₀(g, ε)`, with
  `p⁻¹ = (2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m)` (`pRpp`).
  The paper writes `ρ_m` for `λ_m` and `e^{λ²/2}` for `e^{g²/2}`.

The only hypothesis is that of Lemma K (`RosserSchoenfeld`, cited).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LLT

open ArcsAlgo.PrimeK ArcsAlgo.RandomWeights

variable {m M : ℕ}

/-- The hits of the scheme `𝒫₁`: the `x ⊆ E` with `S_x = a`. -/
def hits (w : Fin m → Fin M) (a : ℤ) : Finset (Finset (Fin m)) := univ.filter fun x => SJ x w = a

/-- `S_{x ∩ A}`, as a natural number. -/
def halfS (A : Finset (Fin m)) (w : Fin m → Fin M) (x : Finset (Fin m)) : ℕ := (SJ (x ∩ A) w).toNat

/-- `Z_r = #{x : S_x = a, S_{x∩A} ≡ r (mod p)}`. -/
def Zr (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) (p r : ℕ) : ℕ :=
  ((hits w a).filter fun x => halfS A w x % p = r).card

/-- The live residues `R_p = {r < p : Z_r > 0}`. -/
def live (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) (p : ℕ) : ℕ :=
  ((range p).filter fun r => 0 < Zr A w a p r).card

/-- `Pr(round succeeds | S_E = s)`: the weights uniform on `S_E = s`, `P` uniform among the primes
of `[P₀, 2P₀)`, `r` uniform in `ℤ/P`; the round succeeds iff `Z_r > 0`. -/
noncomputable def succB (M m P₀ : ℕ) (A : Finset (Fin m)) (s a : ℤ) : ℝ :=
  (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), ∑ p ∈ primesIn P₀, (live A w a p : ℝ) / p) /
    (cntS M m s * (primesIn P₀).card)

theorem sum_Zr (A : Finset (Fin m)) (w : Fin m → Fin M) (a : ℤ) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, (Zr A w a p r : ℝ) = (hits w a).card := by
  unfold Zr
  rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := fun x => halfS A w x % p) (t := range p)
    (fun x _ => mem_range.mpr (Nat.mod_lt _ hp))]

theorem Zc_hits (w : Fin m → Fin M) {s u a : ℤ} (hs : Sw w = s) (ha : 2 * a = s + u) :
    (Zc w u : ℝ) = (hits w a).card := by
  rw [Zc_eq w hs ha, hits, card_eq_sum_ones, Nat.cast_sum, sum_filter]; simp

theorem halfS_eq_iff (A : Finset (Fin m)) (w : Fin m → Fin M) (x y : Finset (Fin m)) :
    halfS A w x = halfS A w y ↔ SJ (x ∩ A) w = SJ (y ∩ A) w := by
  unfold halfS
  have h1 := (SJ_le (x ∩ A) w).1
  have h2 := (SJ_le (y ∩ A) w).1
  omega

theorem lawS_cntS (M m : ℕ) (s : ℤ) : lawS M m s = cntS M m s / (M : ℝ) ^ m := rfl

/-- The pairs with equal half-sums, the diagonal included: `E#{(x, x′)} = λ + D_eq`. -/
theorem sum_eqPairs (hM : 0 < M) (A : Finset (Fin m)) {s u a : ℤ} (ha : 2 * a = s + u)
    (hc : 0 < (cntS M m s : ℝ)) :
    (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s),
        ((((hits w a) ×ˢ (hits w a)).filter fun x => halfS A w x.1 = halfS A w x.2).card : ℝ)) /
      cntS M m s = lamB M m s u + DeqA M m A a s := by
  have hM' : (0 : ℝ) < (M : ℝ) ^ m := by positivity
  -- each `w` as a double sum over the pairs
  have h1 : ∀ w : Fin m → Fin M, ((((hits w a) ×ˢ (hits w a)).filter
      fun x => halfS A w x.1 = halfS A w x.2).card : ℝ) =
      ∑ x : Finset (Fin m), ∑ y : Finset (Fin m),
        if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w then (1 : ℝ) else 0 := by
    intro w
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, hits, sum_product, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_filter]
    by_cases hx : SJ x w = a
    · rw [if_pos hx]; refine sum_congr rfl fun y _ => ?_
      by_cases hy : SJ y w = a <;> simp [hx, hy, halfS_eq_iff]
    · rw [if_neg hx]; symm; exact sum_eq_zero fun y _ => by simp [hx]
  -- split the diagonal
  have h2 : ∀ w : Fin m → Fin M, (∑ x : Finset (Fin m), ∑ y : Finset (Fin m),
        if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w then (1 : ℝ) else 0) =
      (hits w a).card + ∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x,
        if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w then (1 : ℝ) else 0 := by
    intro w
    rw [hits, card_eq_sum_ones, Nat.cast_sum, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← add_sum_erase _ _ (mem_univ x)]
    congr 1
    by_cases hx : SJ x w = a <;> simp [hx]
  have hl : lamB M m s u = (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s),
      ((hits w a).card : ℝ)) / cntS M m s := by
    unfold lamB
    congr 1
    exact sum_congr rfl fun w hw => Zc_hits w (mem_filter.mp hw).2 ha
  have hD : DeqA M m A a s = (∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s),
      ∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x,
        if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w then (1 : ℝ) else 0) /
      cntS M m s := by
    unfold DeqA pairPA prW
    rw [lawS_cntS]
    simp_rw [← Finset.sum_div]
    rw [div_div_div_cancel_right₀ hM'.ne']
    congr 1
    rw [sum_filter]
    have e : ∀ w : Fin m → Fin M, (if Sw w = s then ∑ x : Finset (Fin m),
        ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x,
        (if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w then (1 : ℝ) else 0) else 0) =
        ∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x,
        (if SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s then (1 : ℝ) else 0) := by
      intro w; by_cases hs : Sw w = s
      · rw [if_pos hs]; simp [hs]
      · rw [if_neg hs]; simp [hs]
    symm
    rw [sum_congr rfl fun w _ => e w, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_comm]
  rw [hl, hD, ← add_div, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun w _ => by rw [h1, h2]

set_option maxHeartbeats 1000000 in
/-- **Lemmas J and K′ for the filtered endgame of `𝒫₁`** (paper §6.7): conditionally on `S_E = s`,
`Pr(round succeeds) ≥ λ²/(2P₀(λ + D_eq) + 6 ln(mM)·E[Z²])`. The only hypothesis is that of Lemma K
(Rosser–Schoenfeld). -/
theorem succB_ge (hRS : RosserSchoenfeld) {P₀ : ℕ} (hP : 100 ≤ P₀) (hM : 0 < M) (hm : 0 < m)
    (A : Finset (Fin m)) {s u a : ℤ} (ha : 2 * a = s + u) :
    lamB M m s u ^ 2 /
        (2 * P₀ * (lamB M m s u + DeqA M m A a s) + 6 * log (m * M) * m2B M m s u) ≤
      succB M m P₀ A s a := by
  set F := univ.filter (fun w : Fin m → Fin M => Sw w = s)
  set Q := primesIn P₀
  have hQ := card_primesIn_ge hRS hP
  have hP' : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
  have hl4 : 4 < log P₀ := lt_of_lt_of_le log_100_gt (log_le_log (by norm_num) hP')
  have hQ0 : 0 < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQ
  have hsucc0 : 0 ≤ succB M m P₀ A s a := by unfold succB; positivity
  have hl0 : 0 ≤ lamB M m s u := by unfold lamB; positivity
  rcases hl0.eq_or_lt with hl | hl
  · rw [← hl]; simpa using hsucc0
  have hc : 0 < (cntS M m s : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) (cntS M m s)).eq_or_lt with h | h
    · exfalso; unfold lamB at hl; rw [← h, div_zero] at hl; exact lt_irrefl _ hl
    · exact h
  set c : ℝ := 1 / (cntS M m s * Q.card) with hcdef
  have hc0 : 0 ≤ c := by positivity
  -- Lemma J on `Ω = weights × primes`
  have hJ := roundSuccess_ge (F ×ˢ Q) (fun _ => c) (fun _ _ => hc0) (fun ω => ω.2)
    (fun ω h => primesIn_pos (mem_product.mp h).2) (fun ω r => Zr A ω.1 a ω.2 r)
  -- the numerator is `λ`
  have hN : ∑ ω ∈ F ×ˢ Q, c * ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ) = lamB M m s u := by
    rw [sum_product]
    have : ∀ w ∈ F, ∑ p ∈ Q, c * ∑ r ∈ range p, (Zr A w a p r : ℝ) = Q.card * c * (hits w a).card := by
      intro w _
      rw [sum_congr rfl fun p hp => by rw [sum_Zr A w a (primesIn_pos hp)], sum_const, nsmul_eq_mul]
      ring
    rw [sum_congr rfl this, ← mul_sum]
    unfold lamB
    rw [sum_congr rfl fun w hw => Zc_hits w (mem_filter.mp hw).2 ha]
    rw [hcdef]; field_simp; rfl
  -- the success probability
  have hS : ∑ ω ∈ F ×ˢ Q, c * ((((range ω.2).filter fun r => 0 < Zr A ω.1 a ω.2 r).card : ℕ) : ℝ) /
      (ω.2 : ℝ) = succB M m P₀ A s a := by
    rw [sum_product]; unfold succB live
    rw [div_eq_mul_one_div _ ((cntS M m s : ℝ) * Q.card), mul_comm, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun p _ => ?_
    rw [hcdef]; ring
  -- the denominator, by Proposition K′
  set Dt := ∑ ω ∈ F ×ˢ Q, c * (ω.2 : ℝ) * ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ) ^ 2
  have hX1 : (1 : ℝ) ≤ m * M := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hK := kprime hRS hP F (fun _ => 1 / (cntS M m s : ℝ)) (fun _ _ => by positivity)
    (fun w => hits w a) (fun w => halfS A w) hX1 (by
      intro w _ x _ y _
      have hx := SJ_le (x ∩ A) w
      have hy := SJ_le (y ∩ A) w
      have ex : ((halfS A w x : ℕ) : ℝ) = (SJ (x ∩ A) w : ℝ) := by
        unfold halfS; exact_mod_cast Int.toNat_of_nonneg hx.1
      have ey : ((halfS A w y : ℕ) : ℝ) = (SJ (y ∩ A) w : ℝ) := by
        unfold halfS; exact_mod_cast Int.toNat_of_nonneg hy.1
      have hx' : (SJ (x ∩ A) w : ℝ) ≤ m * M := by exact_mod_cast hx.2
      have hy' : (SJ (y ∩ A) w : ℝ) ≤ m * M := by exact_mod_cast hy.2
      have hx0 : (0 : ℝ) ≤ SJ (x ∩ A) w := by exact_mod_cast hx.1
      have hy0 : (0 : ℝ) ≤ SJ (y ∩ A) w := by exact_mod_cast hy.1
      have key : |((halfS A w x : ℕ) : ℝ) - ((halfS A w y : ℕ) : ℝ)| ≤ m * M := by
        rw [ex, ey, abs_le]; constructor <;> linarith
      exact_mod_cast key)
  have hDt : Dt = ∑ w ∈ F, 1 / (cntS M m s : ℝ) * ((∑ p ∈ Q, (p : ℝ) *
      ∑ r ∈ range p, ((((hits w a).filter fun τ => halfS A w τ % p = r).card : ℕ) : ℝ) ^ 2) / Q.card) := by
    simp only [Dt]; rw [sum_product]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_div, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [hcdef]; unfold Zr; ring
  have hEq := sum_eqPairs hM A ha hc
  have hm2 : ∑ w ∈ F, 1 / (cntS M m s : ℝ) * ((hits w a).card : ℝ) ^ 2 = m2B M m s u := by
    unfold m2B
    rw [← mul_sum, sum_congr rfl fun w hw => by rw [← Zc_hits w (mem_filter.mp hw).2 ha]]
    ring
  have hEq' : ∑ w ∈ F, 1 / (cntS M m s : ℝ) *
      ((((hits w a) ×ˢ (hits w a)).filter fun x => halfS A w x.1 = halfS A w x.2).card : ℝ) =
      lamB M m s u + DeqA M m A a s := by
    rw [← mul_sum, ← hEq]; ring
  have hDle : Dt ≤ 2 * P₀ * (lamB M m s u + DeqA M m A a s) + 6 * log (m * M) * m2B M m s u := by
    rw [hDt, ← hEq', ← hm2]; exact hK
  -- `Dt ≥ λ > 0`
  have hDge : lamB M m s u ≤ Dt := by
    rw [← hN]
    refine sum_le_sum fun ω hω => ?_
    have hp1 : (1 : ℝ) ≤ ω.2 := by exact_mod_cast (primesIn_pos (mem_product.mp hω).2)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    calc ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ)
        ≤ ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ) ^ 2 := sum_le_sum fun r _ => by
          rcases Nat.eq_zero_or_pos (Zr A ω.1 a ω.2 r) with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ Zr A ω.1 a ω.2 r := by exact_mod_cast h
            nlinarith
      _ ≤ (ω.2 : ℝ) * ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ) ^ 2 := by
          have : 0 ≤ ∑ r ∈ range ω.2, (Zr A ω.1 a ω.2 r : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
          nlinarith
  have hDt0 : 0 < Dt := lt_of_lt_of_le hl hDge
  rw [hN, hS] at hJ
  refine le_trans ?_ hJ
  exact div_le_div_of_nonneg_left (sq_nonneg _) hDt0 hDle

/-- The algebra of `p`: with `κ = (1 + e)/(1 − e)`, from `λ ≥ (1 − e)λ_m`, `D_eq ≤ λV(1 + e)` and
`E Z² ≤ 2λ + λ²(1 + e)`, `λ²/(P(λ + D_eq) + ℓ E Z²) ≥ 1/(κ(P(1 + V)/λ_m + ℓ(1 + 2/λ_m)))`. -/
theorem p_alg {l L P V lg D m2 e : ℝ} (hL : 0 < L) (hP : 0 < P) (hV : 0 ≤ V) (hlg : 0 ≤ lg)
    (he0 : 0 ≤ e) (he1 : e < 1) (hl : (1 - e) * L ≤ l) (hD0 : 0 ≤ D) (hD : D ≤ l * V * (1 + e))
    (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 2 * l + l ^ 2 * (1 + e)) :
    1 / ((1 + e) / (1 - e) * (P / L * (1 + V) + lg * (1 + 2 / L))) ≤ l ^ 2 / (P * (l + D) + lg * m2) := by
  have h1e : 0 < 1 - e := by linarith
  have hl0 : 0 < l := lt_of_lt_of_le (mul_pos h1e hL) hl
  set κ := (1 + e) / (1 - e) with hκ
  have hκ1 : 1 + e ≤ κ := by rw [hκ, le_div_iff₀ h1e]; nlinarith
  have hκl : 1 + e ≤ κ * l / L := by
    rw [le_div_iff₀ hL, hκ, div_mul_eq_mul_div, le_div_iff₀ h1e]
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 1 + e)
    nlinarith
  have hκl1 : 1 ≤ κ * l / L := by linarith
  have hA : P * (l + D) ≤ κ * l ^ 2 * (P / L * (1 + V)) := by
    have h1 : P * (l + D) ≤ P * l * (1 + V) * (1 + e) := by
      have : l + D ≤ l * (1 + V) * (1 + e) := by nlinarith [mul_nonneg hl0.le hV]
      nlinarith
    have e2 : κ * l ^ 2 * (P / L * (1 + V)) = P * l * (1 + V) * (κ * l / L) := by
      field_simp
    rw [e2]
    exact h1.trans (mul_le_mul_of_nonneg_left hκl (by positivity))
  have hB : lg * m2 ≤ κ * l ^ 2 * (lg * (1 + 2 / L)) := by
    have h1 : m2 ≤ κ * l ^ 2 * (1 + 2 / L) := by
      have e2 : κ * l ^ 2 * (1 + 2 / L) = κ * l ^ 2 + 2 * l * (κ * l / L) := by field_simp
      rw [e2]
      have : l ^ 2 * (1 + e) ≤ κ * l ^ 2 := by nlinarith [sq_nonneg l]
      have : 2 * l ≤ 2 * l * (κ * l / L) := by nlinarith
      linarith
    calc lg * m2 ≤ lg * (κ * l ^ 2 * (1 + 2 / L)) := mul_le_mul_of_nonneg_left h1 hlg
      _ = κ * l ^ 2 * (lg * (1 + 2 / L)) := by ring
  have hDen0 : 0 < P * (l + D) + lg * m2 := by
    have : 0 < P * (l + D) := mul_pos hP (by linarith)
    have : 0 ≤ lg * m2 := mul_nonneg hlg hm20
    linarith
  have hκ0 : 0 < κ := by linarith
  have e3 : 1 / (κ * (P / L * (1 + V) + lg * (1 + 2 / L))) =
      l ^ 2 / (κ * l ^ 2 * (P / L * (1 + V)) + κ * l ^ 2 * (lg * (1 + 2 / L))) := by
    field_simp
  rw [e3]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hDen0 (by linarith)

/-- `p` of Theorem R″ (paper §6.7), with `λ_m` for the paper's `ρ_m` and `e^{g²/2}` for `e^{λ²/2}`:
`p⁻¹ = (2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m)`, `ψ = 2^{m/2}/M`. -/
noncomputable def pRpp (g : ℝ) (M m P₀ : ℕ) : ℝ :=
  1 / (2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) + 6 * log (m * M) * (1 + 2 / lamM M m))

theorem DeqA_nonneg (M m : ℕ) (A : Finset (Fin m)) (a s : ℤ) : 0 ≤ DeqA M m A a s := by
  unfold DeqA pairPA prW
  exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity) (lawS_nonneg _ _ _)

set_option maxHeartbeats 1000000 in
/-- **A round of Theorem R″** (paper §6.7): for fixed `g ≥ 0` and every `ε > 0` there is `m₀` such
that, for all `M ≥ 2`, `m ≥ m₀`, `P₀ ≥ 100`, `|A| = ⌊m/2⌋`, and `s` in the window with
`|u| ≤ M`, `u ≡ s (mod 2)`: `Pr(round succeeds | S_E = s) ≥ p/(1 + ε)`. Lemmas J, K′, B and V; the
only hypothesis is that of Lemma K (Rosser–Schoenfeld). -/
theorem succB_unif (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      (2 : ℤ) ∣ u - s → pRpp g M m P₀ / (1 + ε) ≤ succB M m P₀ A s a := by
  set e := min ε 1 / 4 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 4 := by rw [he]; have := min_le_right ε 1; linarith
  have hκ : (1 + e) / (1 - e) ≤ 1 + ε := by
    have hm : 4 * e ≤ ε := by rw [he]; have := min_le_left ε 1; linarith
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨m₁, h₁⟩ := lemmaB1_unif hg he0
  obtain ⟨m₂, h₂⟩ := lemmaB2_unif hg he0
  obtain ⟨m₃, h₃⟩ := lemmaV hg he0
  refine ⟨max (max m₁ m₂) (max m₃ 1), fun M m P₀ hM hm hP A hA s u a ha hw hu hsu => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : m₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm0 : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hL := lamM_pos hM hm0
  have hl := (abs_le.mp (h₁ M m hM hm1 s u hw hu hsu)).1
  rw [div_sub_one hL.ne', le_div_iff₀ hL] at hl
  have hl' : (1 - e) * lamM M m ≤ lamB M m s u := by linarith
  have hl0 : 0 < lamB M m s u := lt_of_lt_of_le (mul_pos (by linarith) hL) hl'
  have hV := h₃ M m hM hm3 A hA s u a ha hw hu
  rw [div_le_iff₀ hl0] at hV
  have hB2 := h₂ M m hM hm2 s u hw hu hsu
  have hi : (if u = 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hm2' : m2B M m s u ≤ 2 * lamB M m s u + lamB M m s u ^ 2 * (1 + e) := by nlinarith
  have hm20 : 0 ≤ m2B M m s u := by unfold m2B; positivity
  have hP0 : (0 : ℝ) < 2 * P₀ := by have : (100 : ℝ) ≤ P₀ := by exact_mod_cast hP
                                    linarith
  have hlg : 0 ≤ log (m * M) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith)
  have hV0 : 0 ≤ 0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) := by
    positivity
  have halg := p_alg (P := 2 * P₀) (lg := 6 * log (m * M)) hL hP0 hV0 (by positivity) he0.le
    (by linarith) hl' (DeqA_nonneg M m A a s) (by linarith) hm20 hm2'
  have hS := succB_ge hRS hP (by omega : 0 < M) (by omega : 0 < m) A ha
  have hQ : 0 < 2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) + 6 * log (m * M) * (1 + 2 / lamM M m) := by
    have : 0 < 2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) := by positivity
    have : 0 ≤ 6 * log (m * M) * (1 + 2 / lamM M m) := by positivity
    linarith
  have hfin := halg.trans hS
  have hκ0 : 0 < (1 + e) / (1 - e) := div_pos (by linarith) (by linarith)
  refine le_trans ?_ hfin
  unfold pRpp
  rw [div_div, one_div_le_one_div (mul_pos hQ (by linarith)) (mul_pos hκ0 hQ)]
  nlinarith

end ArcsAlgo.LLT
