module

public import ArcsAlgo.LemmaQ
public import ArcsAlgo.LemmaWSW
set_option autoImplicit false

/-!
# Lemma L, part 1 (paper §3.5)

* `norm_cyc_prod_cos`: `|Φ_q(−e(x))| = Π_{(r,q)=1} 2|cos π(ra/q + x)|` for `(a, q) = 1`.
* `FN_reduce`: `|F_N(e(a/q + β))| ≤ 2^{|W_N|} exp(Σ_{(r,q)=1} Σ_{M<p≤N, p≡r} G_r(p))`,
  `G_r(t) = log max(|cos π(ra/q + tβ)|, ε)`: the weight 1, the primes `≤ M` and those dividing `q`
  contribute `≤ 1`.
-/

open Finset Real Polynomial

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-- The residues prime to `q`. -/
def resQ (q : ℕ) : Finset ℕ := (range q).filter (fun r => r.Coprime q)

theorem card_resQ (q : ℕ) : (resQ q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]; unfold resQ; congr 1; ext r; simp [Nat.coprime_comm]

theorem ee_add (u v : ℝ) : ee (u + v) = ee u * ee v := by
  unfold ee; rw [← Complex.exp_add]; push_cast; ring_nf

theorem ee_neg (u : ℝ) : ee (-u) = (ee u)⁻¹ := by
  unfold ee; rw [← Complex.exp_neg]; push_cast; ring_nf

theorem ee_nat_div (k q : ℕ) (hq : 0 < q) :
    ee ((k : ℝ) / q) = Complex.exp (2 * π * Complex.I / q) ^ k := by
  unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp

/-- **`|Φ_q(−e(x))| = Π_{(r,q)=1} 2|cos π(ra/q + x)|`** for `(a, q) = 1`. -/
theorem norm_cyc_prod_cos {q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (x : ℝ) :
    ‖(cyclotomic q ℂ).eval (-ee x)‖ = ∏ r ∈ resQ q, 2 * |cos (π * ((r * a : ℕ) / q + x))| := by
  have hq0 : 0 < q := by omega
  set ζ := Complex.exp (2 * π * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq0.ne'
  set g : ℕ → ℂ := fun r => (ζ ^ (r * a))⁻¹
  have hg : ∀ r ∈ resQ q, g r ∈ primitiveRoots q ℂ := by
    intro r hr
    rw [mem_primitiveRoots hq0]
    exact (hζ.pow_of_coprime _ (Nat.coprime_mul_iff_left.mpr ⟨(mem_filter.mp hr).2, ha⟩)).inv
  have hinj : Set.InjOn g (resQ q) := by
    intro r hr s hs h
    simp only [g, inv_inj] at h
    have hr' := mem_range.mp (mem_filter.mp hr).1
    have hs' := mem_range.mp (mem_filter.mp hs).1
    have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
    have key : ∀ r s : ℕ, r ≤ s → s < q → ζ ^ (r * a) = ζ ^ (s * a) → r = s := by
      intro r s hrs hsq h
      have e : ζ ^ (s * a) = ζ ^ (r * a) * ζ ^ ((s - r) * a) := by
        rw [← pow_add]; congr 1; rw [← add_mul, Nat.add_sub_cancel' hrs]
      rw [← h] at e
      have h1 : ζ ^ ((s - r) * a) = 1 :=
        (mul_left_cancel₀ (pow_ne_zero _ hz) (e.symm.trans (mul_one _).symm))
      have hd := (hζ.pow_eq_one_iff_dvd _).mp h1
      have hd' : q ∣ s - r := Nat.Coprime.dvd_of_dvd_mul_right ha.symm hd
      have := Nat.eq_zero_of_dvd_of_lt hd' (by omega)
      omega
    rcases le_total r s with hrs | hrs
    · exact key r s hrs hs' h
    · exact (key s r hrs hr' h.symm).symm
  have hcard : (primitiveRoots q ℂ).card ≤ (resQ q).card := by
    rw [Complex.card_primitiveRoots, card_resQ]
  have hP := prod_eq_prod_of_inj g hg hinj hcard (fun μ => ((‖ee x + μ‖ : ℝ) : ℂ))
  rw [← Complex.ofReal_prod, ← Complex.ofReal_prod] at hP
  rw [norm_cyc_neg_prod q hq0.ne', Complex.ofReal_injective hP]
  refine prod_congr rfl fun r hr => ?_
  have e1 : g r = ee (-((r * a : ℕ) / q : ℝ)) := by
    simp only [g]; rw [ee_neg, ee_nat_div _ _ hq0]
  rw [e1, show ee x + ee (-((r * a : ℕ) / q : ℝ)) = ee x * (1 + ee (-((r * a : ℕ) / q : ℝ) - x)) by
    rw [mul_add, mul_one, ← ee_add]; ring_nf, norm_mul, norm_ee, one_mul, norm_one_add_ee]
  rw [show π * (-((r * a : ℕ) / q : ℝ) - x) = -(π * ((r * a : ℕ) / q + x)) by ring, Real.cos_neg]

/-! ### Step A: from `F_N` to the primes of `(M, N]`, by classes -/

/-- `G_r(t) = log max(|cos π(ra/q + tβ)|, ε)`. -/
noncomputable def Gq (q a r : ℕ) (β ε t : ℝ) : ℝ := Real.log (max |cos (π * ((r * a : ℕ) / q + t * β))| ε)

theorem norm_FW (W : Finset ℕ) (θ : ℝ) : ‖FW W θ‖ = 2 ^ W.card * ∏ w ∈ W, |cos (π * (w * θ))| := by
  unfold FW
  rw [norm_prod, show ∏ b ∈ W, ‖1 + ee (b * θ)‖ = ∏ w ∈ W, (2 * |cos (π * (w * θ))|) from
    prod_congr rfl fun w _ => norm_one_add_ee _, prod_mul_distrib, prod_const]

/-- For `p ≡ r (mod q)`: `|cos(πp(a/q + β))| = |cos π(ra/q + pβ)|`. -/
theorem cos_class {q a p : ℕ} (hq : 0 < q) (β : ℝ) :
    |cos (π * (p * ((a : ℝ) / q + β)))| = |cos (π * (((p % q) * a : ℕ) / q + p * β))| := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : π * (p * ((a : ℝ) / q + β)) = π * (((p % q) * a : ℕ) / q + p * β) + ((p / q * a : ℕ) : ℝ) * π := by
    have h := Nat.div_add_mod p q
    have : (p : ℝ) = q * (p / q : ℕ) + (p % q : ℕ) := by exact_mod_cast h.symm
    rw [this]; push_cast; field_simp; ring
  rw [e, Real.cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **Step A**: for `0 < ε ≤ 1`, `‖F_N(e(a/q + β))‖ ≤ 2^{|W_N|} exp(Σ_{(r,q)=1} Σ_{M<p≤N, p≡r} G_r(p))`. -/
theorem FN_reduce {q a : ℕ} (hq : 3 ≤ q) (M N : ℕ) (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖FW (WN N) ((a : ℝ) / q + β)‖ ≤ 2 ^ (WN N).card *
      Real.exp (∑ r ∈ resQ q, ∑ p ∈ (Ioc M N).filter (fun n => n.Prime ∧ n % q = r), Gq q a r β ε p) := by
  have hq0 : 0 < q := by omega
  rw [norm_FW]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set P := (Ioc M N).filter (fun n => n.Prime ∧ n.Coprime q)
  have hPW : P ⊆ WN N := by
    intro n hn
    simp only [P, mem_filter, mem_Ioc] at hn
    simp only [WN, mem_filter, mem_range]; exact ⟨by omega, Or.inr hn.2.1⟩
  have hc1 : ∀ w, |cos (π * (w * ((a : ℝ) / q + β)))| ≤ 1 := fun w => abs_cos_le_one _
  have hc0 : ∀ w, 0 ≤ |cos (π * (w * ((a : ℝ) / q + β)))| := fun w => abs_nonneg _
  have h1 : ∏ w ∈ WN N, |cos (π * (w * ((a : ℝ) / q + β)))| ≤ ∏ w ∈ P, |cos (π * (w * ((a : ℝ) / q + β)))| := by
    rw [← prod_sdiff hPW]
    have : ∏ w ∈ WN N \ P, |cos (π * (w * ((a : ℝ) / q + β)))| ≤ 1 :=
      prod_le_one₀ (fun w _ => hc0 w) fun w _ => hc1 w
    have h0 : 0 ≤ ∏ w ∈ P, |cos (π * (w * ((a : ℝ) / q + β)))| := prod_nonneg fun w _ => hc0 w
    nlinarith
  refine h1.trans ?_
  have h2 : ∏ w ∈ P, |cos (π * (w * ((a : ℝ) / q + β)))| ≤
      ∏ w ∈ P, max |cos (π * (w * ((a : ℝ) / q + β)))| ε :=
    Finset.prod_le_prod₀ (fun w _ => hc0 w) fun w _ => le_max_left _ _
  refine h2.trans (le_of_eq ?_)
  rw [Real.exp_sum]
  -- regroup by classes
  have hcopmod : ∀ n, (n % q).Coprime q ↔ n.Coprime q := by
    intro n; rw [Nat.Coprime, Nat.Coprime, ← Nat.gcd_rec q n, Nat.gcd_comm q n]
  rw [← prod_fiberwise_of_maps_to (g := fun n => n % q) (t := resQ q) (s := P) (fun n hn => by
    simp only [P, mem_filter] at hn
    simp only [resQ, mem_filter, mem_range]; exact ⟨Nat.mod_lt _ hq0, (hcopmod n).mpr hn.2.2⟩)]
  refine prod_congr rfl fun r hr => ?_
  rw [Real.exp_sum]
  have hset : P.filter (fun n => n % q = r) = (Ioc M N).filter (fun n => n.Prime ∧ n % q = r) := by
    ext n; simp only [P, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2, ?_⟩, h3⟩
      rw [← hcopmod n, h3]; exact (mem_filter.mp hr).2
  rw [hset]
  refine prod_congr rfl fun p hp => ?_
  have hpr : p % q = r := (mem_filter.mp hp).2.2
  unfold Gq
  rw [Real.exp_log (lt_of_lt_of_le hε (le_max_right _ _)), cos_class hq0, hpr]

end ArcsAlgo.Core
