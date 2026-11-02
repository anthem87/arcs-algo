module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Field.GeomSum
set_option autoImplicit false

/-!
# Lemma C (paper §6.5)

Weights `w_1, …, w_n`, `d ≥ 2`, `r(c) = #{x : Σ_{i∈x} w_i ≡ c (mod d)}`, `k(d′) = #{i : d′ ∤ w_i}`.

* `rC_fourier`: `d·r(c) = Σ_{a<d} e(−ac/d) Π_i (1 + e(aw_i/d))` (orthogonality `sum_eC`), and
  `‖1 + e(θ)‖ = 2|cos πθ|` (`norm_one_add_eC`).
* `lemmaC1`: `|d·r(c)/2^n − 1| ≤ Σ_{a=1}^{d−1} Π_i|cos(πaw_i/d)| ≤ Σ_{d′|d, d′>1} φ(d′) e^{−π²k(d′)/(2d′²)}`:
  for `a/d = a′/d′` in lowest terms a factor with `d′ ∤ w_i` has modulus `≤ cos(π/d′)`
  (`abs_cos_le`) `≤ e^{−π²/(2d′²)}` (`cos_le_exp_neg`), and the arcs with `gcd(d, a) = d/d′` number
  `φ(d′)` (`Nat.totient_div_of_dvd`).
* `lemmaC2`: if `2^{k(d)} < d`, at least `d − 2^{k(d)}` classes are empty, and some arc `a/d`,
  `a ≠ 0`, has `Π_i|cos(πaw_i/d)| ≥ 1/(d − 1)`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.LemC

/-- `cos x ≤ e^{−x²/2}` on `[0, π/2]`: `cos x · e^{x²/2}` decreases, since `x cos x ≤ sin x`. -/
theorem cos_le_exp_neg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 2) : cos x ≤ exp (-(x ^ 2 / 2)) := by
  set g : ℝ → ℝ := fun y => cos y * exp (y ^ 2 / 2)
  have hcont : ContinuousOn g (Set.Icc 0 (π / 2)) := by fun_prop
  have hder : ∀ y ∈ interior (Set.Icc (0 : ℝ) (π / 2)),
      HasDerivWithinAt g (exp (y ^ 2 / 2) * (y * cos y - sin y)) (interior (Set.Icc 0 (π / 2))) y := by
    intro y _
    have h0 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) (y) y := by
      have := HasDerivAt.div_const (hasDerivAt_pow 2 y) 2
      convert this using 1; push_cast; ring
    have h1 := HasDerivAt.mul (hasDerivAt_cos y) (HasDerivAt.exp h0)
    refine (h1.congr_deriv ?_).hasDerivWithinAt
    ring
  have hneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) (π / 2)), exp (y ^ 2 / 2) * (y * cos y - sin y) ≤ 0 := by
    intro y hy
    rw [interior_Icc] at hy
    have ht := lt_tan hy.1 hy.2
    have hc : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith [hy.1, pi_pos], hy.2⟩
    rw [tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
    exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith)
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (π / 2)) hcont hder hneg
  have hle : g x ≤ g 0 := hanti ⟨le_refl 0, by linarith [pi_pos]⟩ ⟨h0, h1⟩ h0
  simp only [g, cos_zero, one_mul, zero_pow two_ne_zero, zero_div, exp_zero] at hle
  have he := exp_pos (x ^ 2 / 2)
  rw [exp_neg, ← one_div, le_div_iff₀ he]
  linarith

/-- `|cos(πt/d′)| ≤ cos(π/d′)` for `d′ ∤ t`. -/
theorem abs_cos_le {d' t : ℕ} (hd : 2 ≤ d') (ht : ¬ d' ∣ t) :
    |cos (π * t / d')| ≤ cos (π / d') := by
  have hd0 : (0 : ℝ) < d' := by exact_mod_cast (by omega : 0 < d')
  set q := t / d'
  set r := t % d'
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h => ht (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r < d' := Nat.mod_lt _ (by omega)
  have htqr : (t : ℝ) = q * d' + r := by exact_mod_cast (Nat.div_add_mod' t d').symm
  have e : π * t / d' = π * r / d' + (q : ℤ) * π := by
    rw [htqr]; push_cast; field_simp; ring
  rw [e, cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℝ) ≤ d' - 1 := by
    have : (r : ℝ) + 1 ≤ d' := by exact_mod_cast hr2
    linarith
  have hpi := pi_pos
  have ha : π / d' ≤ π * r / d' := by
    have : π ≤ π * r := by nlinarith
    exact div_le_div_of_nonneg_right this hd0.le
  have hb : π * r / d' ≤ π - π / d' := by
    rw [div_le_iff₀ hd0]; field_simp; nlinarith
  have hb0 : 0 ≤ π / d' := by positivity
  rw [abs_le]; constructor
  · have := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hb
    rw [cos_pi_sub] at this; linarith
  · exact cos_le_cos_of_nonneg_of_le_pi hb0 (by linarith) ha

variable {n : ℕ} (w : Fin n → ℕ)

/-- `S_x = Σ_{i ∈ x} w_i`. -/
def Sx (x : Finset (Fin n)) : ℕ := ∑ i ∈ x, w i

/-- `r(c) = #{x : S_x ≡ c (mod d)}`. -/
def rC (d : ℕ) (c : ℤ) : ℕ := (univ.filter fun x : Finset (Fin n) => (d : ℤ) ∣ (Sx w x : ℤ) - c).card

/-- `k(d′) = #{i : d′ ∤ w_i}`. -/
def kC (d' : ℕ) : ℕ := (univ.filter fun i : Fin n => ¬ d' ∣ w i).card

/-- `e(θ) = e^{2πiθ}`. -/
noncomputable def eC (θ : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * θ)

theorem eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem eC_int (t : ℤ) : eC t = 1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℝ) = t * (2 * π * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I t

theorem eC_eq_one_iff {d : ℕ} (hd : 0 < d) (t : ℤ) : eC (t / d) = 1 ↔ (d : ℤ) ∣ t := by
  constructor
  · intro h
    unfold eC at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (((t : ℝ) / d : ℝ) : ℂ) = k := by
      apply mul_left_cancel₀ h2; linear_combination hk
    push_cast at h3
    have h4 : (t : ℂ) = ((k * d : ℤ) : ℂ) := by
      rw [div_eq_iff hd'] at h3; push_cast; exact h3
    have h5 : t = k * d := by exact_mod_cast h4
    exact ⟨k, by rw [h5]; ring⟩
  · rintro ⟨k, rfl⟩
    have : ((d * k : ℤ) : ℝ) / d = (k : ℤ) := by
      push_cast; field_simp
    rw [this]; exact eC_int k

/-- Orthogonality: `Σ_{a<d} e(at/d) = d·1[d | t]`. -/
theorem sum_eC {d : ℕ} (hd : 0 < d) (t : ℤ) :
    ∑ a ∈ range d, eC (a * t / d) = if (d : ℤ) ∣ t then (d : ℂ) else 0 := by
  have hpow : ∀ a : ℕ, eC (a * t / d) = eC (t / d) ^ a := by
    intro a; unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  simp only [hpow]
  split_ifs with h
  · rw [(eC_eq_one_iff hd t).mpr h]; simp
  · have hne : eC (t / d) ≠ 1 := fun h' => h ((eC_eq_one_iff hd t).mp h')
    rw [geom_sum_eq hne]
    have : eC (t / d) ^ d = 1 := by
      rw [← hpow d]
      have : (d : ℝ) * t / d = (t : ℤ) := by field_simp
      rw [this]; exact eC_int t
    rw [this, sub_self, zero_div]

/-- `‖1 + e(θ)‖ = 2|cos πθ|`. -/
theorem norm_one_add_eC (θ : ℝ) : ‖1 + eC θ‖ = 2 * |cos (π * θ)| := by
  set z : ℂ := ((π * θ : ℝ) : ℂ)
  have e : 1 + eC θ = Complex.exp (z * Complex.I) *
      (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) := by
    unfold eC
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add,
      show z * Complex.I + -z * Complex.I = 0 by ring, Complex.exp_zero, add_comm]
    congr 2; simp only [z]; push_cast; ring
  rw [e, ← Complex.two_cos, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul,
    show Complex.cos z = ((cos (π * θ) : ℝ) : ℂ) by simp only [z]; push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs]
  simp

/-- The finite Fourier formula: `d·r(c) = Σ_{a<d} e(−ac/d) Π_i (1 + e(aw_i/d))`. -/
theorem rC_fourier {d : ℕ} (hd : 0 < d) (c : ℤ) :
    ((d : ℂ) * rC w d c) = ∑ a ∈ range d, eC (-(a * c) / d) * ∏ i, (1 + eC (a * w i / d)) := by
  have h1 : ((d : ℂ) * rC w d c) = ∑ x : Finset (Fin n), ∑ a ∈ range d,
      eC (a * (((Sx w x : ℤ) - c : ℤ) : ℝ) / d) := by
    unfold rC
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_eC hd]; split_ifs <;> simp
  rw [h1, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [prod_one_add, ← powerset_univ, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have e1 : (a : ℝ) * (((Sx w x : ℤ) - c : ℤ) : ℝ) / d = -(a * c) / d + ∑ i ∈ x, (a : ℝ) * w i / d := by
    unfold Sx; push_cast
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]; ring
  rw [e1, eC_add]
  congr 1
  unfold eC
  rw [← Complex.exp_sum]; congr 1; push_cast; rw [mul_sum]

/-- **Lemma C (1), first inequality** (paper §6.5):
`|d·r(c)/2^n − 1| ≤ Σ_{a=1}^{d−1} Π_i |cos(πaw_i/d)|`. -/
theorem lemmaC1_a {d : ℕ} (hd : 0 < d) (c : ℤ) :
    |(d : ℝ) * rC w d c / 2 ^ n - 1| ≤ ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| := by
  have hF := rC_fourier w hd c
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ d)] at hF
  simp only [Ico_self, Nat.Ico_succ_singleton, sum_singleton, Nat.cast_zero, zero_mul, neg_zero,
    zero_div] at hF
  have h0 : eC 0 * ∏ i : Fin n, (1 + eC 0) = 2 ^ n := by
    unfold eC; simp; norm_num
  rw [h0] at hF
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hnorm : ‖((d : ℂ) * rC w d c) - 2 ^ n‖ ≤ 2 ^ n * ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| := by
    rw [hF, add_sub_cancel_left, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_prod]
    have hu : ‖eC (-(a * c) / d)‖ = 1 := by
      unfold eC
      rw [show (2 * π * Complex.I * ((-(a * c) / d : ℝ) : ℂ)) = (((2 * π * (-(a * c) / d)) : ℝ) : ℂ) *
        Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hu, one_mul]
    simp only [norm_one_add_eC]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  have : ((d : ℂ) * rC w d c) - 2 ^ n = (((d : ℝ) * rC w d c - 2 ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [div_sub_one h2n.ne', abs_div, abs_of_pos h2n, div_le_iff₀ h2n]
  linarith

/-- The bound of one arc `a/d`: with `d′ = d/gcd(d, a)`, `Π_i |cos(πaw_i/d)| ≤ e^{−π²k(d′)/(2d′²)}`. -/
theorem arc_bound {d a : ℕ} (hd : 0 < d) (ha : a ∈ Ico 1 d) :
    ∏ i, |cos (π * (a * w i / d))| ≤
      exp (-(π ^ 2 * kC w (d / d.gcd a) / (2 * ((d / d.gcd a : ℕ) : ℝ) ^ 2))) := by
  obtain ⟨ha1, ha2⟩ := mem_Ico.mp ha
  set g := d.gcd a
  set d' := d / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hgd : g ∣ d := Nat.gcd_dvd_left d a
  have hga : g ∣ a := Nat.gcd_dvd_right d a
  have hgle : g ≤ a := Nat.le_of_dvd (by omega) hga
  have hd2 : 2 ≤ d' := by
    have hdd : d = g * d' := (Nat.mul_div_cancel' hgd).symm
    by_contra h; push Not at h
    have : g * d' ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    omega
  obtain ⟨a', ha'⟩ := hga
  have hdd : d = g * d' := (Nat.mul_div_cancel' hgd).symm
  have hcop : Nat.Coprime a' d' := by
    have h := Nat.coprime_div_gcd_div_gcd (m := a) (n := d) (by rw [Nat.gcd_comm]; exact hg0)
    rw [Nat.gcd_comm a d] at h
    have e : a / g = a' := by rw [ha']; exact Nat.mul_div_cancel_left a' hg0
    rw [← e]; exact h
  have hd'0 : (0 : ℝ) < d' := by exact_mod_cast (by omega : 0 < d')
  have hcos : 0 ≤ cos (π / d') := cos_nonneg_of_mem_Icc ⟨by
    have : 0 < π / d' := by positivity
    linarith [pi_pos], by
    rw [div_le_iff₀ hd'0]
    have : (2 : ℝ) ≤ d' := by exact_mod_cast hd2
    nlinarith [pi_pos]⟩
  have hterm : ∀ i, |cos (π * (a * w i / d))| ≤ if d' ∣ w i then 1 else cos (π / d') := by
    intro i
    split_ifs with hdi
    · exact abs_cos_le_one _
    · have hnd : ¬ d' ∣ a' * w i := fun h => hdi (hcop.symm.dvd_of_dvd_mul_left h)
      have := abs_cos_le hd2 hnd
      have e : π * (a * w i / d) = π * ((a' * w i : ℕ) : ℝ) / d' := by
        rw [ha', hdd]; push_cast
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
        field_simp
      rw [e]; exact this
  calc ∏ i, |cos (π * (a * w i / d))| ≤ ∏ i, (if d' ∣ w i then (1 : ℝ) else cos (π / d')) :=
        prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hterm i
    _ = cos (π / d') ^ kC w d' := by
        rw [prod_ite, prod_const_one, one_mul, prod_const]; rfl
    _ ≤ exp (-((π / d') ^ 2 / 2)) ^ kC w d' := by
        apply pow_le_pow_left₀ hcos
        apply cos_le_exp_neg (by positivity)
        rw [div_le_div_iff₀ hd'0 (by norm_num)]
        have : (2 : ℝ) ≤ d' := by exact_mod_cast hd2
        nlinarith [pi_pos]
    _ = exp (-(π ^ 2 * kC w d' / (2 * ((d' : ℕ) : ℝ) ^ 2))) := by
        rw [← exp_nat_mul]; congr 1; field_simp

/-- **Lemma C (1)** (paper §6.5): for `d ≥ 2`,
`|d·r(c)/2^n − 1| ≤ Σ_{a=1}^{d−1} Π_i|cos(πaw_i/d)| ≤ Σ_{d′ | d, d′ > 1} φ(d′) e^{−π²k(d′)/(2d′²)}`. -/
theorem lemmaC1 {d : ℕ} (hd : 2 ≤ d) (c : ℤ) :
    |(d : ℝ) * rC w d c / 2 ^ n - 1| ≤ ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| ∧
      ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| ≤
        ∑ d' ∈ d.divisors.filter (1 < ·), (d'.totient : ℝ) *
          exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2))) := by
  have hd0 : 0 < d := by omega
  refine ⟨lemmaC1_a w hd0 c, ?_⟩
  set B : ℕ → ℝ := fun d' => exp (-(π ^ 2 * kC w d' / (2 * (d' : ℝ) ^ 2)))
  have h1 : ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| ≤ ∑ a ∈ Ico 1 d, B (d / d.gcd a) :=
    sum_le_sum fun a ha => arc_bound w hd0 ha
  refine h1.trans ?_
  -- group the arcs by `g = gcd(d, a)`
  have hmaps : ∀ a ∈ Ico 1 d, d.gcd a ∈ d.divisors.filter (· ≠ d) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := mem_Ico.mp ha
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.gcd_dvd_left d a, by omega⟩, ?_⟩
    intro h; have := Nat.le_of_dvd (by omega) (h ▸ Nat.gcd_dvd_right d a); omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  have h2 : ∀ g ∈ d.divisors.filter (· ≠ d),
      ∑ a ∈ (Ico 1 d).filter (fun a => d.gcd a = g), B (d / d.gcd a) ≤ ((d / g).totient : ℝ) * B (d / g) := by
    intro g hg
    rw [sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]]
    rw [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    have hgd : g ∣ d := (Nat.mem_divisors.mp (mem_filter.mp hg).1).1
    rw [Nat.totient_div_of_dvd hgd]
    exact_mod_cast card_le_card fun a ha => by
      simp only [mem_filter, mem_Ico, mem_range] at ha ⊢; exact ⟨ha.1.2, ha.2⟩
  refine (sum_le_sum h2).trans (le_of_eq ?_)
  -- reindex `d′ = d/g`
  apply Finset.sum_nbij' (fun g => d / g) (fun d' => d / d')
  · intro g hg
    simp only [mem_filter, Nat.mem_divisors, coe_filter, Set.mem_setOf_eq] at hg ⊢
    obtain ⟨⟨hgd, -⟩, hne⟩ := hg
    have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgd hd0
    refine ⟨⟨Nat.div_dvd_of_dvd hgd, by omega⟩, ?_⟩
    by_contra h; push Not at h
    have h1 : d / g ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hd0 hgd) hg0).ne'
    have h2 : d / g = 1 := le_antisymm h (Nat.pos_of_ne_zero h1)
    apply hne; have := Nat.div_mul_cancel hgd; rw [h2, one_mul] at this; exact this
  · intro d' hd'
    simp only [mem_filter, Nat.mem_divisors, coe_filter, Set.mem_setOf_eq] at hd' ⊢
    obtain ⟨⟨hdd, -⟩, h1⟩ := hd'
    refine ⟨⟨Nat.div_dvd_of_dvd hdd, by omega⟩, ?_⟩
    intro h
    have := Nat.div_mul_cancel hdd
    rw [h] at this
    have : d * 1 = d * d' := by linarith
    have := Nat.eq_of_mul_eq_mul_left hd0 this
    omega
  · intro g hg
    simp only [mem_filter, Nat.mem_divisors, coe_filter, Set.mem_setOf_eq] at hg
    exact Nat.div_div_self hg.1.1 (by omega)
  · intro d' hd'
    simp only [mem_filter, Nat.mem_divisors, coe_filter, Set.mem_setOf_eq] at hd'
    exact Nat.div_div_self hd'.1.1 (by omega)
  · intro g _; rfl

/-- **Lemma C (2)** (paper §6.5): if all but `k` weights are divisible by `d` and `2^k < d`, at least
`d − 2^k` classes are empty, and some arc `a/d`, `a ≠ 0`, has `Π_i|cos(πaw_i/d)| ≥ 1/(d − 1)`. -/
theorem lemmaC2 {d : ℕ} (hd : 2 ≤ d) (hk : 2 ^ kC w d < d) :
    d - 2 ^ kC w d ≤ ((range d).filter fun c : ℕ => rC w d (c : ℤ) = 0).card ∧
      ∃ a ∈ Ico 1 d, 1 / ((d : ℝ) - 1) ≤ ∏ i, |cos (π * (a * w i / d))| := by
  set A := univ.filter fun i : Fin n => ¬ d ∣ w i
  have hsub : (range d).filter (fun c : ℕ => ¬ rC w d (c : ℤ) = 0) ⊆
      A.powerset.image fun y => Sx w y % d := by
    intro c hc
    simp only [mem_filter, mem_range] at hc
    obtain ⟨hcd, hc0⟩ := hc
    unfold rC at hc0
    obtain ⟨x, hx⟩ := card_ne_zero.mp hc0
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [mem_image]
    refine ⟨x ∩ A, mem_powerset.mpr inter_subset_right, ?_⟩
    have hsplit : Sx w x = Sx w (x ∩ A) + Sx w (x \ A) := by
      unfold Sx; rw [sum_inter_add_sum_sdiff]
    have hdiv : (d : ℤ) ∣ (Sx w (x \ A) : ℤ) := by
      apply Int.natCast_dvd_natCast.mpr
      unfold Sx; apply dvd_sum; intro i hi
      simp only [mem_sdiff, A, mem_filter, mem_univ, true_and, not_not] at hi; exact hi.2
    rw [hsplit] at hx; push_cast at hx
    have h1 : (d : ℤ) ∣ (Sx w (x ∩ A) : ℤ) - c := by
      have := dvd_sub hx hdiv
      rwa [show (Sx w (x ∩ A) : ℤ) + Sx w (x \ A) - c - Sx w (x \ A) = Sx w (x ∩ A) - c by ring] at this
    have h2 : ((Sx w (x ∩ A) : ℤ)) % d = (c : ℤ) % d := (Int.modEq_iff_dvd.mpr h1).symm
    have h3 : (c : ℤ) % d = c := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hcd)
    have : ((Sx w (x ∩ A) % d : ℕ) : ℤ) = (c : ℤ) := by push_cast; rw [h2, h3]
    exact_mod_cast this
  have hcard : ((range d).filter fun c : ℕ => ¬ rC w d (c : ℤ) = 0).card ≤ 2 ^ kC w d :=
    (card_le_card hsub).trans (card_image_le.trans (by rw [card_powerset]; rfl))
  have hsum := card_filter_add_card_filter_not (s := range d) (fun c : ℕ => rC w d (c : ℤ) = 0)
  rw [card_range] at hsum
  refine ⟨by omega, ?_⟩
  have hex : ∃ c ∈ range d, rC w d (c : ℤ) = 0 := by
    by_contra h; push Not at h
    have : (range d).filter (fun c : ℕ => rC w d (c : ℤ) = 0) = ∅ :=
      filter_eq_empty_iff.mpr fun c hc => h c hc
    rw [this, card_empty] at hsum; omega
  obtain ⟨c, -, hc⟩ := hex
  have h1 := lemmaC1_a w (by omega : 0 < d) (c : ℤ)
  rw [hc, Nat.cast_zero, mul_zero, zero_div, zero_sub, abs_neg, abs_one] at h1
  by_contra hno; push Not at hno
  have hd1 : (0 : ℝ) < d - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlt : ∑ a ∈ Ico 1 d, ∏ i, |cos (π * (a * w i / d))| < ∑ _a ∈ Ico 1 d, 1 / ((d : ℝ) - 1) :=
    sum_lt_sum_of_nonempty ⟨1, mem_Ico.mpr ⟨le_refl 1, by omega⟩⟩ hno
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega)] at hlt
  push_cast at hlt
  rw [mul_one_div_cancel hd1.ne'] at hlt
  linarith

end ArcsAlgo.LemC
