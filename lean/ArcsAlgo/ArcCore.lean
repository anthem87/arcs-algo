module

public import ArcsAlgo.ArcLevels
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
set_option autoImplicit false

/-!
# Lemma L₀: the core of an arc (paper §3.5)

`F_W(e(θ)) = Π_{w∈W}(1 + e(wθ))` (`FW`); the factor of `w` vanishes at `a/q` iff `2q ∣ 2wa − q`
(`vanish`), and `F*_W(a/q)` is the product of the other factors (`Fstar`).

* `sin_lower`, `cos_lower`: a factor that does not vanish has `|cos(πwa/q)| ≥ sin(π/(2q)) ≥ 1/q`.
* `factor_le`: then `|1 + e(w(a/q + β))| ≤ |1 + e(wa/q)|(1 + πqw|β|)`.
* `L0_gen`: `|F_W(e(a/q + β))| ≤ 2^{#V}|F*_W(a/q)| exp(πq|β|Σ_W w)` for any weights.
* `vanish_eq`, `card_vanish_WN`: for `W_N = {1} ∪ {p ≤ N}` and `q ≥ 3`, only `w = q/2` can vanish.
* `sum_WN_le`: `Σ_{w∈W_N} w ≤ π(N)N` for `N ≥ 3`.
* `lemmaL0`: for `|β| ≤ N^{−3/2}`, `|F_N(e(a/q + β))| ≤ 2|F*_N(a/q)| exp(πq π(N) N^{−1/2})`.

Stated multiplicatively: the paper's `log|F_N(e(θ))| ≤ …` reads `log 0 = −∞` where `F_N(e(θ)) = 0`.
No hypothesis; `q ≤ 𝔓` is not needed.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

/-- `e(x) = e^{2πix}`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `F_W(e(θ)) = Π_{w ∈ W} (1 + e(wθ))`. -/
noncomputable def FW (W : Finset ℕ) (θ : ℝ) : ℂ := ∏ w ∈ W, (1 + ee (w * θ))

/-- The factor of `w` vanishes at `a/q`: `wa/q ≡ 1/2 (mod 1)`, i.e. `2q ∣ 2wa − q`. -/
def vanish (q a w : ℕ) : Prop := (2 * q : ℤ) ∣ 2 * w * a - q

instance (q a : ℕ) : DecidablePred (vanish q a) := fun w => by unfold vanish; infer_instance

/-- `F*_W(a/q)`: the product of the factors that do not vanish at `a/q`. -/
noncomputable def Fstar (W : Finset ℕ) (q a : ℕ) : ℂ :=
  ∏ w ∈ W.filter (fun w => ¬ vanish q a w), (1 + ee (w * ((a : ℝ) / q)))

theorem norm_one_add_ee (t : ℝ) : ‖1 + ee t‖ = 2 * |cos (π * t)| := norm_one_add_exp t

/-- `|sin(πn/K)| ≥ sin(π/K)` for `K ∤ n`. -/
theorem sin_lower {K : ℕ} (hK : 2 ≤ K) {n : ℤ} (hn : ¬ (K : ℤ) ∣ n) :
    sin (π / K) ≤ |sin (π * n / K)| := by
  have hK0 : (0 : ℤ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK' : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  set r := n % K with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hK0.ne'
  have hrK : r < K := Int.emod_lt_of_pos _ hK0
  have hr1 : r ≠ 0 := fun h => hn (Int.dvd_of_emod_eq_zero h)
  have hn' : n = K * (n / K) + r := by have := Int.emod_def n K; linarith
  have e : π * n / K = π * r / K + (n / K : ℤ) * π := by
    have hn'' : (n : ℝ) = K * ((n / K : ℤ) : ℝ) + r := by exact_mod_cast hn'
    rw [hn'']; field_simp; ring
  rw [e, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |((-1 : ℝ)) ^ (n / (K : ℤ))| = 1 := by simp
  rw [h1, one_mul]
  have hrR1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : (1 : ℤ) ≤ r)
  have hrRK : (r : ℝ) ≤ K - 1 := by
    have : r ≤ (K : ℤ) - 1 := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hsin_pos : 0 ≤ sin (π * r / K) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    rw [div_le_iff₀ hK']; nlinarith
  rw [abs_of_nonneg hsin_pos]
  by_cases h2 : 2 * (r : ℝ) ≤ K
  · apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : 0 ≤ π / K := by positivity
      linarith [Real.pi_div_two_pos]
    · rw [div_le_iff₀ hK']; field_simp; nlinarith
    · rw [div_le_div_iff_of_pos_right hK']; nlinarith
  · rw [show sin (π * r / K) = sin (π * (K - r) / K) by
      rw [← Real.sin_pi_sub]; congr 1; field_simp]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : 0 ≤ π / K := by positivity
      linarith [Real.pi_div_two_pos]
    · rw [div_le_iff₀ hK']; push Not at h2; field_simp; nlinarith
    · rw [div_le_div_iff_of_pos_right hK']; nlinarith

/-- For a factor that does not vanish at `a/q`, `|cos(πwa/q)| ≥ sin(π/(2q)) ≥ 1/q`. -/
theorem cos_lower {q a w : ℕ} (hq : 1 ≤ q) (hv : ¬ vanish q a w) :
    1 / (q : ℝ) ≤ |cos (π * (w * ((a : ℝ) / q)))| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h2q : 2 ≤ 2 * q := by omega
  have hnd : ¬ ((2 * q : ℕ) : ℤ) ∣ (2 * w * a + q : ℤ) := by
    intro h; apply hv; unfold vanish
    have : ((2 * q : ℕ) : ℤ) ∣ (2 * w * a + q : ℤ) - 2 * q := dvd_sub h (dvd_refl _)
    push_cast at this ⊢
    have e : (2 * w * a + q - 2 * q : ℤ) = 2 * w * a - q := by ring
    rwa [e] at this
  have hs := sin_lower h2q hnd
  have e : π * w * (a / q) + π / 2 = π * ((2 * w * a + q : ℤ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    push_cast; field_simp
  have hc : |cos (π * (w * ((a : ℝ) / q)))| = |sin (π * ((2 * w * a + q : ℤ) : ℝ) / ((2 * q : ℕ) : ℝ))| := by
    rw [← e, Real.sin_add_pi_div_two]; ring_nf
  rw [hc]
  refine le_trans ?_ hs
  have hj := Real.mul_le_sin (x := π / ((2 * q : ℕ) : ℝ)) (by positivity) (by
    push_cast; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [Real.pi_pos])
  have : 2 / π * (π / ((2 * q : ℕ) : ℝ)) = 1 / q := by push_cast; field_simp
  linarith

/-- **One factor near the arc**: `|1 + e(w(a/q + β))| ≤ |1 + e(wa/q)|·(1 + πqw|β|)` when the factor
does not vanish at `a/q`. -/
theorem factor_le {q a w : ℕ} (hq : 1 ≤ q) (hv : ¬ vanish q a w) (β : ℝ) :
    ‖1 + ee (w * ((a : ℝ) / q + β))‖ ≤ ‖1 + ee (w * ((a : ℝ) / q))‖ * (1 + π * q * w * |β|) := by
  rw [norm_one_add_ee, norm_one_add_ee]
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc := cos_lower hq hv
  set c := |cos (π * (w * ((a : ℝ) / q)))|
  have h1 : |cos (π * (w * ((a : ℝ) / q + β)))| ≤ c + π * w * |β| := by
    have := Real.abs_cos_sub_cos_le (π * (w * ((a : ℝ) / q + β))) (π * (w * ((a : ℝ) / q)))
    have e : π * (w * ((a : ℝ) / q + β)) - π * (w * ((a : ℝ) / q)) = π * w * β := by ring
    rw [e, abs_mul, abs_mul, abs_of_pos Real.pi_pos, Nat.abs_cast] at this
    have := abs_sub_abs_le_abs_sub (cos (π * (w * ((a : ℝ) / q + β)))) (cos (π * (w * ((a : ℝ) / q))))
    linarith
  have h2 : π * w * |β| ≤ c * (π * q * w * |β|) := by
    have hqc : 1 ≤ c * q := by rwa [div_le_iff₀ hq'] at hc
    have : 0 ≤ π * w * |β| := by positivity
    nlinarith
  nlinarith

/-- **Lemma L₀, general form** (paper §3.5): for any set of weights `W`, `q ≥ 1` and `β`,
`|F_W(e(a/q + β))| ≤ 2^{#V}·|F*_W(a/q)|·exp(πq|β|Σ_{w∈W} w)`, `V` the weights vanishing at `a/q`. -/
theorem L0_gen (W : Finset ℕ) {q a : ℕ} (hq : 1 ≤ q) (β : ℝ) :
    ‖FW W ((a : ℝ) / q + β)‖ ≤ 2 ^ (W.filter (vanish q a)).card * ‖Fstar W q a‖ *
      exp (π * q * |β| * ∑ w ∈ W, (w : ℝ)) := by
  unfold FW Fstar
  rw [← prod_filter_mul_prod_filter_not W (vanish q a), norm_mul, norm_prod, norm_prod, norm_prod]
  have hV : ∏ w ∈ W.filter (vanish q a), ‖1 + ee (w * ((a : ℝ) / q + β))‖ ≤
      2 ^ (W.filter (vanish q a)).card := by
    rw [← prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun w _ => ?_
    rw [norm_one_add_ee]; nlinarith [abs_cos_le_one (π * (w * ((a : ℝ) / q + β)))]
  have hN : ∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q + β))‖ ≤
      (∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q))‖) *
        exp (π * q * |β| * ∑ w ∈ W, (w : ℝ)) := by
    calc ∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q + β))‖
        ≤ ∏ w ∈ W.filter (fun w => ¬ vanish q a w),
            (‖1 + ee (w * ((a : ℝ) / q))‖ * exp (π * q * w * |β|)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun w hw =>
            (factor_le hq (mem_filter.mp hw).2 β).trans
              (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (π * q * w * |β|)])
                (norm_nonneg _))
      _ = (∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q))‖) *
            exp (∑ w ∈ W.filter (fun w => ¬ vanish q a w), π * q * w * |β|) := by
          rw [prod_mul_distrib, Real.exp_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (prod_nonneg fun _ _ => norm_nonneg _)
          calc ∑ w ∈ W.filter (fun w => ¬ vanish q a w), π * q * w * |β|
              ≤ ∑ w ∈ W, π * q * w * |β| :=
                sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
            _ = π * q * |β| * ∑ w ∈ W, (w : ℝ) := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  calc (∏ w ∈ W.filter (vanish q a), ‖1 + ee (w * ((a : ℝ) / q + β))‖) *
        ∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q + β))‖
      ≤ 2 ^ (W.filter (vanish q a)).card *
        ((∏ w ∈ W.filter (fun w => ¬ vanish q a w), ‖1 + ee (w * ((a : ℝ) / q))‖) *
          exp (π * q * |β| * ∑ w ∈ W, (w : ℝ))) :=
        mul_le_mul hV hN (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The weights `W_N = {1} ∪ {p ≤ N}`. -/
def WN (N : ℕ) : Finset ℕ := (range (N + 1)).filter fun w => w = 1 ∨ w.Prime

/-- For `q ≥ 3`, `(a, q) = 1`, a weight `1` or prime vanishes at `a/q` only if `w = q/2`. -/
theorem vanish_eq {q a w : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hw : w = 1 ∨ w.Prime)
    (hv : vanish q a w) : 2 * w = q := by
  obtain ⟨c, hc⟩ := hv
  -- `q ∣ 2wa`, hence `q ∣ 2w`
  have hdz : (q : ℤ) ∣ 2 * w * a := ⟨2 * c + 1, by linarith⟩
  have hd : q ∣ 2 * w * a := by exact_mod_cast hdz
  have hd2 : q ∣ 2 * w := (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm ha) hd)
  obtain ⟨k, hk⟩ := hd2
  -- `ka = 2c + 1`, so `k` is odd
  have hka : (k : ℤ) * a = 2 * c + 1 := by
    have h1 : (2 * w * a : ℤ) = q * (k * a) := by
      have : (2 * w : ℤ) = q * k := by exact_mod_cast hk
      rw [this]; ring
    have h2 : (q : ℤ) * (k * a) = q * (2 * c + 1) := by linarith
    exact mul_left_cancel₀ (by exact_mod_cast (by omega : q ≠ 0)) h2
  have hkodd : Odd k := by
    have : Odd ((k : ℤ) * a) := ⟨c, by linarith⟩
    exact_mod_cast (Int.odd_mul.mp this).1
  rcases hw with rfl | hp
  · exfalso
    have : q * k = 2 := by omega
    have hk0 : 1 ≤ k := by rcases hkodd with ⟨j, rfl⟩; omega
    nlinarith
  · obtain ⟨j, rfl⟩ := hkodd
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · omega
    · exfalso
      -- `q (2j + 1) = 2w` with `2j + 1` odd: `q = 2q'`, `w = q'(2j + 1)`, not prime
      have hqe : 2 ∣ q := by
        have : 2 ∣ q * (2 * j + 1) := ⟨w, by omega⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
        · exact h
        · exfalso; omega
      obtain ⟨q', rfl⟩ := hqe
      have hw' : w = q' * (2 * j + 1) := by nlinarith
      rw [hw'] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨_, h⟩ | ⟨_, h⟩
      · omega
      · omega

theorem card_vanish_WN {q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (N : ℕ) :
    ((WN N).filter (vanish q a)).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  simp only [WN, mem_filter] at hx hy
  have := vanish_eq hq ha hx.1.2 hx.2
  have := vanish_eq hq ha hy.1.2 hy.2
  omega

theorem card_primes_eq (N : ℕ) : ((range (N + 1)).filter Nat.Prime).card = Nat.primeCounting N := by
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- `Σ_{w ∈ W_N} w ≤ π(N)·N` for `N ≥ 3`. -/
theorem sum_WN_le {N : ℕ} (hN : 3 ≤ N) : ∑ w ∈ WN N, (w : ℝ) ≤ Nat.primeCounting N * N := by
  set P := (range (N + 1)).filter Nat.Prime
  have hWN : WN N = insert 1 P := by
    ext w; simp only [WN, P, mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨h, rfl | h'⟩
      · left; rfl
      · right; exact ⟨h, h'⟩
    · rintro (rfl | ⟨h, h'⟩)
      · exact ⟨by omega, Or.inl rfl⟩
      · exact ⟨h, Or.inr h'⟩
  have h1 : 1 ∉ P := by simp [P, Nat.not_prime_one]
  have h2 : 2 ∈ P := by simp [P, Nat.prime_two]; omega
  rw [hWN, sum_insert h1, ← card_primes_eq, ← add_sum_erase _ _ h2]
  have hle : ∑ w ∈ P.erase 2, (w : ℝ) ≤ (P.erase 2).card * N := by
    have := sum_le_card_nsmul (P.erase 2) (fun w => (w : ℝ)) N (fun w hw => by
      have := (mem_filter.mp (mem_of_mem_erase hw)).1
      rw [mem_range] at this
      exact_mod_cast (by omega : w ≤ N))
    rwa [nsmul_eq_mul] at this
  have hc : ((P.erase 2).card : ℝ) = P.card - 1 := by
    rw [card_erase_of_mem h2, Nat.cast_sub (card_pos.mpr ⟨2, h2⟩)]; simp
  rw [hc] at hle
  have : (3 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  nlinarith

/-- **Lemma L₀ (the core of an arc)** (paper §3.5): for `q ≥ 3`, `(a, q) = 1`, `N ≥ 3` and
`|β| ≤ N^{−3/2}`, `|F_N(e(a/q + β))| ≤ 2·|F*_N(a/q)|·exp(πq·π(N)·N^{−1/2})`, i.e.
`log|F_N(e(θ))| ≤ log 2 + log|F*_N(a/q)| + πq π(N) N^{−1/2}`. No hypothesis. -/
theorem lemmaL0 {q a N : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hN : 3 ≤ N) {β : ℝ}
    (hβ : |β| ≤ (N : ℝ) ^ (-(3 / 2 : ℝ))) :
    ‖FW (WN N) ((a : ℝ) / q + β)‖ ≤
      2 * ‖Fstar (WN N) q a‖ * exp (π * q * Nat.primeCounting N * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine (L0_gen (WN N) (by omega) β).trans ?_
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h2 : (2 : ℝ) ^ ((WN N).filter (vanish q a)).card ≤ 2 := by
    calc (2 : ℝ) ^ ((WN N).filter (vanish q a)).card ≤ 2 ^ 1 :=
          pow_le_pow_right₀ (by norm_num) (card_vanish_WN hq ha N)
      _ = 2 := by norm_num
  have hexp : π * q * |β| * ∑ w ∈ WN N, (w : ℝ) ≤ π * q * Nat.primeCounting N * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hs := sum_WN_le hN
    have e : (N : ℝ) ^ (-(3 / 2 : ℝ)) * N = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add_one hN'.ne']; norm_num
    have hq0 : (0 : ℝ) ≤ π * q := by positivity
    calc π * q * |β| * ∑ w ∈ WN N, (w : ℝ) ≤ π * q * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (Nat.primeCounting N * N) := by
          have : 0 ≤ ∑ w ∈ WN N, (w : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
          have : 0 ≤ |β| := abs_nonneg _
          have : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
          gcongr
      _ = π * q * Nat.primeCounting N * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * N) := by ring
      _ = _ := by rw [e]
  have : 0 ≤ ‖Fstar (WN N) q a‖ := norm_nonneg _
  calc (2 : ℝ) ^ ((WN N).filter (vanish q a)).card * ‖Fstar (WN N) q a‖ *
        exp (π * q * |β| * ∑ w ∈ WN N, (w : ℝ))
      ≤ 2 * ‖Fstar (WN N) q a‖ * exp (π * q * Nat.primeCounting N * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        gcongr

end ArcsAlgo.Core
