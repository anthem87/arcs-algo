module

public import ArcsAlgo.ThmE3
public import ArcsAlgo.Classical.LemmaM
public import ArcsAlgo.Classical.VinogradovVaughan
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
set_option autoImplicit false

/-!
# Theorem E(1): the minor arcs (paper §3.5)

* `minorArc B N θ`: `|θ − r| > 𝔓/(den(r) N)` for every rational `r` with `den(r) ≤ 𝔓`.
* `abel_ineq`: Abel's inequality for an antitone nonnegative weight.
* `card_ppow_le`: at most `(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)` prime powers `p^k ≤ N`, `k ≥ 2`.
* `primeSum_le`: from Vinogradov–Vaughan by partial summation (weight `1/log n`) and removal of the
  prime powers, `|Σ_{p≤N} e(αp)| ≤ C(Nk^{−1/2} + N^{4/5} + N^{1/2}k^{1/2})(log N)^4 + O(√N log N)`.
* `dirichlet_minor`: on `𝔪`, Dirichlet's theorem gives `b/k` with `|mθ − b/k| ≤ k^{−2}` and
  `𝔓/M < k ≤ NM/𝔓` (otherwise `θ ∈ 𝔐(b/(mk))`).
* `trig_sum_le`: `Σ_p K_M(pθ) ≤ K̂_M(0)π(N) + 2CM max_m |Σ_p e(mpθ)|`.
* `thmE1`: the bound on `𝔪`, for every `B > 0`.
* `ev_log_rpow_neg`, `thmE1_B40`: for `B > 40` (`5 − B/8 < 0`, the paper's "Fix B > 40") the error tends to
  `0`: `sup_𝔪 |F_N(e(θ))| ≤ 2^n exp((−log 2 + δ)π(N))` for every `δ > 0` and `N ≥ N₀`.

Hypotheses: `SiegelWalfisz`, `VinogradovVaughan`, `JacksonThm` (all cited).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical ArcsAlgo.ArcM
open scoped ArithmeticFunction.vonMangoldt

/-- The minor arcs `𝔪`: `θ ∉ 𝔐(r)` for every rational `r` with denominator `≤ 𝔓`. -/
def minorArc (B : ℝ) (N : ℕ) (θ : ℝ) : Prop :=
  ∀ r : ℚ, (r.den : ℝ) ≤ PP B N → PP B N / (r.den * N) < |θ - r|

/-- **Abel's inequality**: for `f` antitone and `≥ 0`, `|Σ_{i<n} f_i g_i| ≤ f_0 max_{k≤n} |Σ_{i<k} g_i|`. -/
theorem abel_ineq (f : ℕ → ℝ) (g : ℕ → ℂ) (hf : Antitone f) (hf0 : ∀ i, 0 ≤ f i) (n : ℕ) {M : ℝ}
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, g i‖ ≤ M) :
    ‖∑ i ∈ range n, (f i : ℂ) * g i‖ ≤ f 0 * M := by
  have hM0 : 0 ≤ M := by have := hM 0 (Nat.zero_le _); simpa using this
  have e : ∑ i ∈ range n, (f i : ℂ) * g i = ∑ i ∈ range n, f i • g i := by
    simp [Complex.real_smul]
  rw [e, sum_range_by_parts]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖f (n - 1) • ∑ i ∈ range n, g i‖ ≤ f (n - 1) * M := by
    rw [norm_smul, Real.norm_of_nonneg (hf0 _)]
    exact mul_le_mul_of_nonneg_left (hM n le_rfl) (hf0 _)
  have h2 : ‖∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤ (f 0 - f (n - 1)) * M := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ range (n - 1), ‖(f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤ (f i - f (i + 1)) * M := by
      intro i hi
      have hd : 0 ≤ f i - f (i + 1) := by linarith [hf (Nat.le_succ i)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      have := hM (i + 1) (by have := mem_range.mp hi; omega)
      calc -(f (i + 1) - f i) * ‖∑ j ∈ range (i + 1), g j‖ = (f i - f (i + 1)) * ‖∑ j ∈ range (i + 1), g j‖ := by ring
        _ ≤ (f i - f (i + 1)) * M := mul_le_mul_of_nonneg_left this hd
    refine (sum_le_sum this).trans (le_of_eq ?_)
    rw [← sum_mul, sum_range_sub' f (n - 1)]
  linarith

/-- The prime powers `p^k ≤ N` with `k ≥ 2`: at most `(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)` of them. -/
theorem card_ppow_le (N : ℕ) :
    ((range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  have hsub : (range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
      ((range (Nat.sqrt N + 1)) ×ˢ (range (Nat.log 2 N + 1))).image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hnN, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    rw [mem_image]
    refine ⟨(p, k), mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, rfl⟩
    · have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      have : p * p ≤ N := by nlinarith [sq p]
      exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr this)
    · have h2 : 2 ^ k ≤ N := le_trans (Nat.pow_le_pow_left hp.two_le k) (by omega)
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) h2)
  exact (card_le_card hsub).trans (card_image_le.trans (by rw [card_product, card_range, card_range]))

theorem ee_eq_exp (x : ℝ) : ee x = Complex.exp (2 * π * Complex.I * x) := rfl

/-- **Prime exponential sums** (from Vinogradov–Vaughan by partial summation): if `|α − r| ≤ den(r)^{−2}`,
`|Σ_{p≤N} e(αp)| ≤ C (N k^{−1/2} + N^{4/5} + N^{1/2} k^{1/2}) (log N)^4 + (⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)`,
`k = den(r)`. -/
theorem primeSum_le (hVV : VinogradovVaughan) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ (α : ℝ) (r : ℚ),
    |α - r| ≤ 1 / (r.den : ℝ) ^ 2 →
    ‖∑ p ∈ (range (N + 1)).filter Nat.Prime, ee (α * p)‖ ≤
      C * (N / √(r.den : ℝ) + (N : ℝ) ^ (4 / 5 : ℝ) + √(N : ℝ) * √(r.den : ℝ)) * Real.log N ^ 4 +
        (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  obtain ⟨C, hC, hV⟩ := hVV
  have hl2 := log_two_pos'
  refine ⟨C / Real.log 2, by positivity, fun N hN α r hr => ?_⟩
  set k : ℝ := ((r.den : ℕ) : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast r.pos
  set V := C * (N / √k + (N : ℝ) ^ (4 / 5 : ℝ) + √(N : ℝ) * √k) * Real.log N ^ 4 with hVdef
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hV0 : 0 ≤ V := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    positivity
  set a : ℕ → ℂ := fun n => (Λ n : ℂ) * ee (α * n) with ha
  set f : ℕ → ℝ := fun n => 1 / Real.log (max (n : ℝ) 2) with hf
  have hlogmax : ∀ n : ℕ, Real.log 2 ≤ Real.log (max (n : ℝ) 2) :=
    fun n => Real.log_le_log (by norm_num) (le_max_right _ _)
  have hfanti : Antitone f := by
    intro i j hij
    simp only [hf]
    refine one_div_le_one_div_of_le (lt_of_lt_of_le hl2 (hlogmax i)) (Real.log_le_log
      (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) (max_le_max (by exact_mod_cast hij) le_rfl))
  have hf0 : ∀ i, 0 ≤ f i := fun i => by simp only [hf]; exact (one_div_pos.mpr (lt_of_lt_of_le hl2 (hlogmax i))).le
  have hf00 : f 0 = 1 / Real.log 2 := by simp [hf]
  -- partial sums of `Λ(n) e(αn)`
  have hpart : ∀ j ≤ N + 1, ‖∑ i ∈ range j, a i‖ ≤ V := by
    intro j hj
    rcases lt_or_ge j 3 with hj3 | hj3
    · have : ∑ i ∈ range j, a i = 0 := by
        refine sum_eq_zero fun i hi => ?_
        have : i = 0 ∨ i = 1 := by have := mem_range.mp hi; omega
        rcases this with rfl | rfl <;> simp [ha]
      rw [this, norm_zero]; exact hV0
    · have hsub : Icc 1 (j - 1) ⊆ range j := fun i hi => by
        simp only [mem_Icc] at hi; exact mem_range.mpr (by omega)
      rw [← sum_subset hsub fun i hi hni => by
        have : i = 0 := by simp only [mem_Icc, mem_range] at hi hni; omega
        subst this; simp [ha]]
      have hx : 2 ≤ j - 1 := by omega
      have h := hV (j - 1) hx α r hr
      have e : ∀ i ∈ Icc 1 (j - 1), a i = (Λ i : ℂ) * Complex.exp (2 * π * Complex.I * (α * i)) := by
        intro i _; simp only [ha, ee_eq_exp]; push_cast; ring_nf
      rw [sum_congr rfl e]
      refine h.trans ?_
      have hx' : ((j - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : j - 1 ≤ N)
      have hx2 : (2 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by exact_mod_cast hx
      rw [hVdef, ← hk]
      have hl : 0 ≤ Real.log ((j - 1 : ℕ) : ℝ) := Real.log_nonneg (by linarith)
      have hlog : Real.log ((j - 1 : ℕ) : ℝ) ≤ Real.log N := Real.log_le_log (by linarith) hx'
      have hb : ((j - 1 : ℕ) : ℝ) / √k + ((j - 1 : ℕ) : ℝ) ^ (4 / 5 : ℝ) + √((j - 1 : ℕ) : ℝ) * √k ≤
          N / √k + (N : ℝ) ^ (4 / 5 : ℝ) + √(N : ℝ) * √k := by
        have h1 : ((j - 1 : ℕ) : ℝ) / √k ≤ N / √k := div_le_div_of_nonneg_right hx' (Real.sqrt_nonneg _)
        have h2 : ((j - 1 : ℕ) : ℝ) ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hx' (by norm_num)
        have h3 : √((j - 1 : ℕ) : ℝ) * √k ≤ √(N : ℝ) * √k :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx') (Real.sqrt_nonneg _)
        linarith
      have hb0 : 0 ≤ ((j - 1 : ℕ) : ℝ) / √k + ((j - 1 : ℕ) : ℝ) ^ (4 / 5 : ℝ) + √((j - 1 : ℕ) : ℝ) * √k := by
        positivity
      have hp4 : Real.log ((j - 1 : ℕ) : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ hl hlog 4
      calc C * (((j - 1 : ℕ) : ℝ) / √k + ((j - 1 : ℕ) : ℝ) ^ (4 / 5 : ℝ) + √((j - 1 : ℕ) : ℝ) * √k) *
            Real.log ((j - 1 : ℕ) : ℝ) ^ 4
          ≤ C * (N / √k + (N : ℝ) ^ (4 / 5 : ℝ) + √(N : ℝ) * √k) * Real.log N ^ 4 := by gcongr
        _ = _ := rfl
  have hAbel := abel_ineq f a hfanti hf0 (N + 1) hpart
  rw [hf00] at hAbel
  -- split `Σ f a` into the primes and the higher prime powers
  have hsplit : ∑ i ∈ range (N + 1), (f i : ℂ) * a i =
      ∑ p ∈ (range (N + 1)).filter Nat.Prime, ee (α * p) +
        ∑ n ∈ (range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (f n : ℂ) * a n := by
    have hz : ∀ n ∈ range (N + 1), ¬ IsPrimePow n → (f n : ℂ) * a n = 0 := by
      intro n _ hn
      simp only [ha, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]; simp
    rw [← sum_filter_of_ne (p := IsPrimePow) fun n hn h => by_contra fun hc => h (hz n hn hc)]
    rw [← sum_filter_add_sum_filter_not ((range (N + 1)).filter IsPrimePow) Nat.Prime, filter_filter, filter_filter]
    congr 1
    · have e1 : (range (N + 1)).filter (fun n => IsPrimePow n ∧ n.Prime) = (range (N + 1)).filter Nat.Prime := by
        congr 1; ext n; exact ⟨fun h => h.2, fun h => ⟨h.isPrimePow, h⟩⟩
      rw [e1]
      refine sum_congr rfl fun p hp => ?_
      have hpp := (mem_filter.mp hp).2
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hlp : Real.log p ≠ 0 := (Real.log_pos (by linarith)).ne'
      simp only [hf, ha, ArithmeticFunction.vonMangoldt_apply_prime hpp, max_eq_left h2]
      rw [← mul_assoc, ← Complex.ofReal_mul, one_div_mul_cancel hlp, Complex.ofReal_one, one_mul]
  have hrest : ‖∑ n ∈ (range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (f n : ℂ) * a n‖ ≤
      (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ n ∈ (range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), ‖(f n : ℂ) * a n‖ ≤ 1 := by
      intro n hn
      have hpp := (mem_filter.mp hn).2.1
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hpp.two_le
      have hln : 0 < Real.log n := Real.log_pos (by linarith)
      simp only [ha, hf, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, max_eq_left h2]
      rw [abs_of_pos (one_div_pos.mpr hln), abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        one_div_mul_eq_div, div_le_one hln]
      exact ArithmeticFunction.vonMangoldt_le_log
    refine (sum_le_sum h1).trans ?_
    rw [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_ppow_le N
  rw [hsplit] at hAbel
  set Sp := ∑ p ∈ (range (N + 1)).filter Nat.Prime, ee (α * p)
  set R := ∑ n ∈ (range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (f n : ℂ) * a n
  have hfin : ‖Sp‖ ≤ ‖Sp + R‖ + ‖R‖ := by
    calc ‖Sp‖ = ‖(Sp + R) - R‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hV' : 1 / Real.log 2 * V = C / Real.log 2 * (N / √k + (N : ℝ) ^ (4 / 5 : ℝ) + √(N : ℝ) * √k) *
      Real.log N ^ 4 := by rw [hVdef]; ring
  linarith

/-- **Dirichlet on the minor arcs**: for `θ ∈ 𝔪` and `1 ≤ m ≤ M` there is `b/k` (lowest terms) with
`|mθ − b/k| ≤ k^{−2}` and `𝔓/M < k ≤ NM/𝔓`. -/
theorem dirichlet_minor {B : ℝ} {N Mi m : ℕ} {θ : ℝ} (hθ : minorArc B N θ) (hP : 0 < PP B N)
    (hm1 : 1 ≤ m) (hmM : m ≤ Mi) (hN : 0 < N) (hD : 1 ≤ (N : ℝ) * Mi / PP B N) :
    ∃ r : ℚ, |m * θ - r| ≤ 1 / (r.den : ℝ) ^ 2 ∧ PP B N / Mi < r.den ∧ (r.den : ℝ) ≤ N * Mi / PP B N := by
  set nD := ⌊(N : ℝ) * Mi / PP B N⌋₊
  have hnD : 0 < nD := Nat.floor_pos.mpr hD
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le (m * θ) hnD
  have hk : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hnD1 : (N : ℝ) * Mi / PP B N ≤ nD + 1 := (Nat.lt_floor_add_one _).le
  have hdenR : (r.den : ℝ) ≤ nD := by exact_mod_cast hden
  have hnDle : (nD : ℝ) ≤ N * Mi / PP B N := Nat.floor_le (by positivity)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hMi1 : (1 : ℝ) ≤ Mi := by exact_mod_cast le_trans hm1 hmM
  have hMi0 : (0 : ℝ) < Mi := by linarith
  refine ⟨r, ?_, ?_, hdenR.trans hnDle⟩
  · refine hr.trans ?_
    rw [one_div_le_one_div (by positivity) (by positivity), sq]
    exact mul_le_mul_of_nonneg_right (by linarith) hk.le
  · by_contra hcon
    push Not at hcon
    set s : ℚ := r * (m : ℚ)⁻¹ with hs
    have hsden : (s.den : ℝ) ≤ r.den * m := by
      have h1 := Rat.mul_den_dvd r (m : ℚ)⁻¹
      rw [Rat.inv_natCast_den, if_neg (by omega)] at h1
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos r.pos (by omega)) h1
    have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.pos
    have hs1 : (s.den : ℝ) ≤ PP B N := by
      calc (s.den : ℝ) ≤ r.den * m := hsden
        _ ≤ PP B N / Mi * Mi := mul_le_mul hcon (by exact_mod_cast hmM) hm0.le (by positivity)
        _ = PP B N := by field_simp
    have hcl := hθ s hs1
    have hsR : ((s : ℚ) : ℝ) = (r : ℝ) / m := by rw [hs]; push_cast; ring
    have hsθ : |θ - s| = |m * θ - r| / m := by
      rw [hsR, show θ - (r : ℝ) / m = (m * θ - r) / m by field_simp, abs_div, abs_of_pos hm0]
    have h2 : |m * θ - r| ≤ PP B N / (r.den * N * Mi) := by
      refine hr.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have h3 : (N : ℝ) * Mi ≤ PP B N * (nD + 1) := by
        have := (div_le_iff₀ hP).mp hnD1; linarith
      nlinarith
    have h3 : |θ - s| ≤ PP B N / (s.den * N) := by
      rw [hsθ, div_le_iff₀ hm0]
      refine h2.trans ?_
      have h4 : (s.den : ℝ) * N ≤ r.den * N * Mi * m := by
        have : (r.den : ℝ) * m ≤ r.den * m * Mi := le_mul_of_one_le_right (by positivity) hMi1
        nlinarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem ee_re (x : ℝ) : (ee x).re = cos (2 * π * x) := by
  rw [ee_eq_exp, show 2 * π * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

theorem ee_im (x : ℝ) : (ee x).im = sin (2 * π * x) := by
  rw [ee_eq_exp, show 2 * π * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

/-- `Σ_{p∈P} K(pθ) ≤ a₀|P| + 2CMS` for a trigonometric polynomial `K` of degree `M` with coefficients
`|a_k|, |b_k| ≤ C` (`k ≥ 1`), when `|Σ_{p∈P} e(kθp)| ≤ S` for `1 ≤ k ≤ M`. -/
theorem trig_sum_le (P : Finset ℕ) (M : ℕ) (a b : ℕ → ℝ) {C S θ : ℝ}
    (hab : ∀ k, 1 ≤ k → |a k| ≤ C ∧ |b k| ≤ C)
    (hS : ∀ k, 1 ≤ k → k ≤ M → ‖∑ p ∈ P, ee ((k * θ) * p)‖ ≤ S) :
    ∑ p ∈ P, trigPoly M a b (p * θ) ≤ a 0 * P.card + 2 * C * M * S := by
  unfold trigPoly
  rw [sum_comm, sum_range_succ']
  have h0 : ∑ p ∈ P, (a 0 * cos (2 * π * ((0 : ℕ) : ℝ) * (p * θ)) + b 0 * sin (2 * π * ((0 : ℕ) : ℝ) * (p * θ))) =
      a 0 * P.card := by simp [sum_const, nsmul_eq_mul, mul_comm]
  rw [h0]
  have hk : ∀ i ∈ range M, ∑ p ∈ P, (a (i + 1) * cos (2 * π * ((i + 1 : ℕ) : ℝ) * (p * θ)) +
      b (i + 1) * sin (2 * π * ((i + 1 : ℕ) : ℝ) * (p * θ))) ≤ 2 * C * S := by
    intro i hi
    have hi1 : i + 1 ≤ M := by have := mem_range.mp hi; omega
    have hSi := hS (i + 1) (by omega) hi1
    obtain ⟨ha, hb⟩ := hab (i + 1) (by omega)
    set Z := ∑ p ∈ P, ee (((i + 1 : ℕ) * θ) * p)
    have hre : ∑ p ∈ P, cos (2 * π * ((i + 1 : ℕ) : ℝ) * (p * θ)) = Z.re := by
      rw [Complex.re_sum]; refine sum_congr rfl fun p _ => ?_; rw [ee_re]; ring_nf
    have him : ∑ p ∈ P, sin (2 * π * ((i + 1 : ℕ) : ℝ) * (p * θ)) = Z.im := by
      rw [Complex.im_sum]; refine sum_congr rfl fun p _ => ?_; rw [ee_im]; ring_nf
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hre, him]
    have h1 : a (i + 1) * Z.re ≤ C * S := by
      calc a (i + 1) * Z.re ≤ |a (i + 1) * Z.re| := le_abs_self _
        _ = |a (i + 1)| * |Z.re| := abs_mul _ _
        _ ≤ C * S := mul_le_mul ha ((Complex.abs_re_le_norm Z).trans hSi) (abs_nonneg _)
            (le_trans (abs_nonneg _) ha)
    have h2 : b (i + 1) * Z.im ≤ C * S := by
      calc b (i + 1) * Z.im ≤ |b (i + 1) * Z.im| := le_abs_self _
        _ = |b (i + 1)| * |Z.im| := abs_mul _ _
        _ ≤ C * S := mul_le_mul hb ((Complex.abs_im_le_norm Z).trans hSi) (abs_nonneg _)
            (le_trans (abs_nonneg _) hb)
    linarith
  have := sum_le_sum hk
  rw [sum_const, card_range, nsmul_eq_mul] at this
  linarith

set_option maxHeartbeats 8000000 in
/-- **Theorem E(1) (minor arcs)** (paper §3.5): fix `B > 0`, `𝔓 = (log N)^B`, `M = (log N)^{B/4}`. There
are `C` and `N₀` such that for `N ≥ N₀` and `θ ∈ 𝔪`:
`|F_N(e(θ))| ≤ 2^n exp((−log 2 + C((log N)^{5−B/8} + M^{−1/2}))π(N))`. Lemma M at degree `⌊M⌋`, Dirichlet
with parameter `N⌊M⌋/𝔓`, Vinogradov–Vaughan and partial summation. Proved for every `B > 0`; the error
tends to `0` exactly when `5 − B/8 < 0`, i.e. `B > 40` (`thmE1_B40`). Hypotheses: Siegel–Walfisz (only for `π(N) ≥ N/(2 log N)`), Vinogradov–Vaughan,
Jackson (through Lemma M). -/
theorem thmE1 (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, minorArc B N θ →
      ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 +
        C * (Real.log N ^ (5 - B / 8) + (Real.log N ^ (B / 4)) ^ (-(1 / 2 : ℝ)))) * Nat.primeCounting N) := by
  have hl2 := log_two_pos'
  obtain ⟨CM, hCM, hLM⟩ := lemmaM hJ
  obtain ⟨CV, hCV, hPS⟩ := primeSum_le hVV
  obtain ⟨N₂, hlow⟩ := pi_lower hSW
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp B one_pos 1
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp (3 * B / 8) (by norm_num : (0 : ℝ) < 1 / 5) (4 * CM * CV)
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (3 * B / 8) (by norm_num : (0 : ℝ) < 1 / 2) (24 * CM)
  set K := max (max K₁ K₂) (max K₃ (Real.exp (8 * Real.log 2 / B)))
  refine ⟨2 * CM + 8 * CM * CV + 2, N₂ + ⌈Real.exp K⌉₊ + 16, fun N hN θ hθ => ?_⟩
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : K ≤ L := by
    have : Real.exp K ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp K⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKL
  have hL3 : K₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKL
  have hL4 : Real.exp (8 * Real.log 2 / B) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set P := (Nat.primeCounting N : ℝ) with hPdef
  have hPlow : Nr / (2 * L) ≤ P := hlow N (by omega)
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPlow
  -- `x = L^{B/8}`, `M = ⌊x²⌋`, `𝔓 = x⁸`
  set x := L ^ (B / 8) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hL0 _
  have hxpow : ∀ t : ℕ, x ^ t = L ^ (B / 8 * t) := by
    intro t; rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hx2 : x ^ 2 = L ^ (B / 4) := by rw [hxpow]; congr 1; push_cast; ring
  have hx3 : x ^ 3 = L ^ (3 * B / 8) := by rw [hxpow]; congr 1; push_cast; ring
  have hx8 : x ^ 8 = L ^ B := by rw [hxpow]; congr 1; push_cast; ring
  have hxx : 4 ≤ x ^ 2 := by
    -- `L ≥ e^{8 log 2/B}` gives `L^{B/4} ≥ 4`
    rw [hx2, Real.rpow_def_of_pos hL0]
    have h1 : 8 * Real.log 2 / B ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hL4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : Real.log 4 ≤ Real.log L * (B / 4) := by
      rw [h2]; have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ B / 4)
      have e : 8 * Real.log 2 / B * (B / 4) = 2 * Real.log 2 := by field_simp; try ring
      linarith
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr h3
  set Mi := ⌊x ^ 2⌋₊ with hMi
  have hMile : (Mi : ℝ) ≤ x ^ 2 := Nat.floor_le (by positivity)
  have hMige : x ^ 2 / 2 ≤ Mi := by
    have := Nat.lt_floor_add_one (x ^ 2); rw [← hMi] at this; linarith
  have hMi2 : 2 ≤ Mi := by
    have : (2 : ℝ) ≤ Mi := by linarith
    exact_mod_cast this
  have hMi0 : (0 : ℝ) < Mi := by exact_mod_cast (by omega : 0 < Mi)
  have hPP : PP B N = x ^ 8 := by unfold PP; rw [← hNr, ← hLdef, hx8]
  have hPN : x ^ 8 ≤ Nr := by
    have := hk1 L hL1; rw [one_mul] at this; rw [hx8]
    exact this.trans (by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
  have hP8 : 0 < x ^ 8 := by positivity
  -- Lemma M at degree `M`
  obtain ⟨ca, cb, hmaj, ha0, hab⟩ := hLM Mi hMi2
  -- the bound on each prime exponential sum
  set Epp : ℝ := (Nat.sqrt N + 1) * (Nat.log 2 N + 1) with hEpp
  set Smax := CV * (2 * Nr / x ^ 3 + Nr ^ (4 / 5 : ℝ)) * L ^ 4 + Epp with hSmax
  have hSk : ∀ m, 1 ≤ m → m ≤ Mi → ‖∑ p ∈ (range (N + 1)).filter Nat.Prime, ee ((m * θ) * p)‖ ≤ Smax := by
    intro m hm1 hmM
    have hD : 1 ≤ (N : ℝ) * Mi / PP B N := by
      rw [← hNr, hPP, le_div_iff₀ hP8, one_mul]
      nlinarith
    obtain ⟨r, hr, hlo, hhi⟩ := dirichlet_minor hθ (by rw [hPP]; exact hP8) hm1 hmM (by omega) hD
    rw [hPP] at hlo hhi
    have hk0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
    have h1 := hPS N (by omega) (m * θ) r hr
    refine h1.trans ?_
    rw [← hNr, ← hLdef]
    -- `k > x⁶` and `k ≤ N x^{−6}`
    have hk6 : x ^ 6 ≤ r.den := by
      have : x ^ 8 / Mi ≥ x ^ 6 := by
        rw [ge_iff_le, le_div_iff₀ hMi0]
        calc x ^ 6 * Mi ≤ x ^ 6 * x ^ 2 := mul_le_mul_of_nonneg_left hMile (by positivity)
          _ = x ^ 8 := by ring
      linarith
    have hkN : (r.den : ℝ) ≤ Nr / x ^ 6 := by
      refine hhi.trans ?_
      rw [div_le_div_iff₀ hP8 (by positivity)]
      have : Nr * Mi * x ^ 6 ≤ Nr * x ^ 2 * x ^ 6 := by
        have := mul_le_mul_of_nonneg_left hMile hNpos.le
        nlinarith [pow_pos hx0 6]
      nlinarith
    have hs1 : x ^ 3 ≤ √(r.den : ℝ) := by
      rw [Real.le_sqrt (by positivity) hk0.le]; nlinarith
    have hA : Nr / √(r.den : ℝ) ≤ Nr / x ^ 3 :=
      div_le_div_of_nonneg_left hNpos.le (by positivity) hs1
    have hB' : √Nr * √(r.den : ℝ) ≤ Nr / x ^ 3 := by
      rw [← Real.sqrt_mul hNpos.le]
      rw [Real.sqrt_le_left (by positivity)]
      calc Nr * r.den ≤ Nr * (Nr / x ^ 6) := mul_le_mul_of_nonneg_left hkN hNpos.le
        _ = (Nr / x ^ 3) ^ 2 := by field_simp; try ring
    have hl4 : 0 ≤ L ^ 4 := by positivity
    have : CV * (Nr / √(r.den : ℝ) + Nr ^ (4 / 5 : ℝ) + √Nr * √(r.den : ℝ)) * L ^ 4 ≤
        CV * (2 * Nr / x ^ 3 + Nr ^ (4 / 5 : ℝ)) * L ^ 4 := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCV) hl4
      have e : 2 * Nr / x ^ 3 = Nr / x ^ 3 + Nr / x ^ 3 := by ring
      linarith
    rw [hSmax]; linarith
  -- the sum over the primes
  set Pr := (range (N + 1)).filter Nat.Prime with hPr
  have hPcard : (Pr.card : ℝ) = P := by rw [hPr, card_primes_eq]
  have hPW : Pr ⊆ WN N := by
    intro n hn; simp only [hPr, mem_filter, mem_range] at hn
    simp only [WN, mem_filter, mem_range]; exact ⟨hn.1, Or.inr hn.2⟩
  have hSmax0 : 0 ≤ Smax := le_trans (norm_nonneg _) (hSk 1 le_rfl (by omega))
  have htrig := trig_sum_le Pr Mi ca cb hab (θ := θ) (fun k hk1 hkM => hSk k hk1 hkM)
  rw [hPcard] at htrig
  rw [norm_FW]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hz : ∃ w ∈ WN N, cos (π * (w * θ)) = 0
  · obtain ⟨w, hw, hcw⟩ := hz
    rw [prod_eq_zero hw (by rw [hcw, abs_zero])]; positivity
  push Not at hz
  -- `Π_{W_N} |cos| ≤ Π_P |cos| = exp Σ_P log|cos|`
  have hprod : ∏ w ∈ WN N, |cos (π * (w * θ))| ≤ ∏ p ∈ Pr, |cos (π * (p * θ))| := by
    rw [← prod_sdiff hPW]
    have h1 : ∏ w ∈ WN N \ Pr, |cos (π * (w * θ))| ≤ 1 :=
      prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_cos_le_one _
    have h0 : 0 ≤ ∏ p ∈ Pr, |cos (π * (p * θ))| := prod_nonneg fun _ _ => abs_nonneg _
    nlinarith
  refine hprod.trans ?_
  have hpos : ∀ p ∈ Pr, 0 < |cos (π * (p * θ))| := fun p hp => abs_pos.mpr (hz p (hPW hp))
  rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun p hp => (hpos p hp).ne')]
  refine Real.exp_le_exp.mpr ?_
  have hmaj' : ∑ p ∈ Pr, Real.log |cos (π * (p * θ))| ≤ ∑ p ∈ Pr, trigPoly Mi ca cb (p * θ) :=
    sum_le_sum fun p hp => hmaj _ (hz p (hPW hp))
  refine hmaj'.trans (htrig.trans ?_)
  -- the final comparison
  have e5 : L ^ (5 - B / 8) = L ^ 5 / x := by
    rw [Real.rpow_sub hL0, hx]; norm_cast
  have e2 : (L ^ (B / 4)) ^ (-(1 / 2 : ℝ)) = 1 / x := by
    rw [← Real.rpow_mul hL0.le, hx, show B / 4 * -(1 / 2 : ℝ) = -(B / 8) by ring, Real.rpow_neg hL0.le, one_div]
  rw [e5, e2]
  -- the coefficient `a₀ ≤ −log 2 + C_M/√M ≤ −log 2 + 2C_M/x`
  have hsM : x / 2 ≤ √(Mi : ℝ) := by
    rw [Real.le_sqrt (by positivity) hMi0.le]; nlinarith
  have ha0' : ca 0 ≤ -Real.log 2 + 2 * CM / x := by
    refine ha0.trans ?_
    have : CM / √(Mi : ℝ) ≤ 2 * CM / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
    linarith
  have hT1 : ca 0 * P ≤ (-Real.log 2 + 2 * CM / x) * P := mul_le_mul_of_nonneg_right ha0' hP0.le
  -- `2 C_M M S_max ≤ (8 C_M C_V + 2) P L⁵/x`
  have hNL : Nr ≤ 2 * L * P := by
    have := hPlow; rw [div_le_iff₀ (by positivity)] at this; linarith
  have hT2 : 2 * CM * Mi * (CV * (2 * Nr / x ^ 3) * L ^ 4) ≤ 8 * CM * CV * (P * (L ^ 5 / x)) := by
    have h1 : 2 * CM * Mi * (CV * (2 * Nr / x ^ 3) * L ^ 4) ≤ 2 * CM * x ^ 2 * (CV * (2 * Nr / x ^ 3) * L ^ 4) := by
      gcongr
    have h2 : 2 * CM * x ^ 2 * (CV * (2 * Nr / x ^ 3) * L ^ 4) = 4 * CM * CV * (Nr * L ^ 4 / x) := by
      field_simp; try ring
    have h3 : 4 * CM * CV * (Nr * L ^ 4 / x) ≤ 4 * CM * CV * (2 * L * P * L ^ 4 / x) := by gcongr
    have h4 : 4 * CM * CV * (2 * L * P * L ^ 4 / x) = 8 * CM * CV * (P * (L ^ 5 / x)) := by ring
    linarith
  have hT3 : 2 * CM * Mi * (CV * Nr ^ (4 / 5 : ℝ) * L ^ 4) ≤ P * (L ^ 5 / x) := by
    have h1 := hk2 L hL2
    rw [← hx3] at h1
    have h1' : 4 * CM * CV * x ^ 3 ≤ Real.exp (L / 5) := h1.trans (Real.exp_le_exp.mpr (by linarith))
    have hr45 : Nr ^ (4 / 5 : ℝ) = Real.exp (L * (4 / 5)) := by rw [Real.rpow_def_of_pos hNpos]
    have he : Real.exp (L / 5) * Real.exp (L * (4 / 5)) = Nr := by rw [← Real.exp_add, ← hexpL]; ring_nf
    have h5 : 4 * CM * CV * x ^ 3 * Nr ^ (4 / 5 : ℝ) ≤ Nr := by
      rw [hr45, ← he]; exact mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
    have h6 : 2 * CM * Mi * (CV * Nr ^ (4 / 5 : ℝ) * L ^ 4) ≤ 2 * CM * x ^ 2 * (CV * Nr ^ (4 / 5 : ℝ) * L ^ 4) := by
      gcongr
    have h7 : 2 * CM * x ^ 2 * (CV * Nr ^ (4 / 5 : ℝ) * L ^ 4) = (4 * CM * CV * x ^ 3 * Nr ^ (4 / 5 : ℝ)) * (L ^ 4 / (2 * x)) := by
      field_simp; try ring
    have h8 : (4 * CM * CV * x ^ 3 * Nr ^ (4 / 5 : ℝ)) * (L ^ 4 / (2 * x)) ≤ Nr * (L ^ 4 / (2 * x)) :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    have h9 : Nr * (L ^ 4 / (2 * x)) ≤ 2 * L * P * (L ^ 4 / (2 * x)) := mul_le_mul_of_nonneg_right hNL (by positivity)
    have h10 : 2 * L * P * (L ^ 4 / (2 * x)) = P * (L ^ 5 / x) := by field_simp; try ring
    linarith
  have hT4 : 2 * CM * Mi * Epp ≤ P * (L ^ 5 / x) := by
    have hsq : (Nat.sqrt N : ℝ) ≤ √Nr := by
      rw [Real.le_sqrt (by positivity) hNpos.le, hNr]; exact_mod_cast Nat.sqrt_le' N
    have hs1 : (1 : ℝ) ≤ √Nr := by rw [Real.le_sqrt (by norm_num) hNpos.le]; linarith
    have hlg : (Nat.log 2 N : ℝ) * Real.log 2 ≤ L := by
      have h := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      have h' : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast h
      have := Real.log_le_log (by positivity) h'
      rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
    have hl2' : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlg' : (Nat.log 2 N : ℝ) ≤ 2 * L := by nlinarith
    have hE : Epp ≤ 6 * L * √Nr := by
      rw [hEpp]
      have h1 : (Nat.sqrt N : ℝ) + 1 ≤ 2 * √Nr := by linarith
      have h2 : (Nat.log 2 N : ℝ) + 1 ≤ 3 * L := by linarith
      calc ((Nat.sqrt N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1) ≤ (2 * √Nr) * (3 * L) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 6 * L * √Nr := by ring
    have h1 := hk3 L hL3
    rw [← hx3] at h1
    have h1' : 24 * CM * x ^ 3 ≤ Real.exp (L / 2) := h1.trans (Real.exp_le_exp.mpr (by linarith))
    have hsN : √Nr = Real.exp (L / 2) := by
      rw [← hexpL, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    have hsN2 : √Nr * √Nr = Nr := Real.mul_self_sqrt hNpos.le
    have h5 : 24 * CM * x ^ 3 * √Nr ≤ Nr := by
      calc 24 * CM * x ^ 3 * √Nr ≤ Real.exp (L / 2) * √Nr := mul_le_mul_of_nonneg_right h1' (Real.sqrt_nonneg _)
        _ = √Nr * √Nr := by rw [hsN]
        _ = Nr := hsN2
    have hEpp0 : 0 ≤ Epp := by rw [hEpp]; positivity
    calc 2 * CM * Mi * Epp ≤ 2 * CM * x ^ 2 * (6 * L * √Nr) := by gcongr
      _ = (24 * CM * x ^ 3 * √Nr) * (L / (2 * x)) := by field_simp; try ring
      _ ≤ Nr * (L / (2 * x)) := mul_le_mul_of_nonneg_right h5 (by positivity)
      _ ≤ 2 * L * P * (L / (2 * x)) := mul_le_mul_of_nonneg_right hNL (by positivity)
      _ = P * (L ^ 2 / x) := by field_simp; try ring
      _ ≤ P * (L ^ 5 / x) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (pow_le_pow_right₀ hLone (by norm_num)) hx0.le) hP0.le
  have hMS : 2 * CM * Mi * Smax = 2 * CM * Mi * (CV * (2 * Nr / x ^ 3) * L ^ 4) +
      2 * CM * Mi * (CV * Nr ^ (4 / 5 : ℝ) * L ^ 4) + 2 * CM * Mi * Epp := by rw [hSmax]; ring
  have hfin : (-Real.log 2 + 2 * CM / x) * P + (8 * CM * CV * (P * (L ^ 5 / x)) + P * (L ^ 5 / x) + P * (L ^ 5 / x)) ≤
      (-Real.log 2 + (2 * CM + 8 * CM * CV + 2) * (L ^ 5 / x + 1 / x)) * P := by
    have hL5 : 0 ≤ L ^ 5 / x := by positivity
    have : 2 * CM / x * P ≤ 2 * CM * (L ^ 5 / x + 1 / x) * P := by
      have : 2 * CM / x ≤ 2 * CM * (L ^ 5 / x + 1 / x) := by
        rw [show 2 * CM / x = 2 * CM * (1 / x) by ring]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right this hP0.le
    have h2 : (8 * CM * CV + 2) * (P * (L ^ 5 / x)) ≤ (8 * CM * CV + 2) * ((L ^ 5 / x + 1 / x) * P) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : 0 ≤ 1 / x * P := by positivity
      linarith [show (L ^ 5 / x + 1 / x) * P = P * (L ^ 5 / x) + 1 / x * P by ring]
    nlinarith
  rw [hMS]
  nlinarith

/-- `L^{−γ} → 0`: for `γ > 0` and `ε > 0`, `(log N)^{−γ} ≤ ε` for `N` large. -/
theorem ev_log_rpow_neg {γ : ℝ} (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Real.log N ^ (-γ) ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_neg_atTop hγ).eventually (ge_mem_nhds hε))
  refine ⟨⌈Real.exp (max L₀ 1)⌉₊ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : max L₀ 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈Real.exp (max L₀ 1)⌉₊ ≤ N))
  exact hL₀ _ (le_trans (le_max_left _ _) hL)

/-- **Theorem E(1) for `B > 40`** (paper §3.5, "Fix `B > 40`"): since `5 − B/8 < 0`, for every `δ > 0`
and `N ≥ N₀`, `sup_{θ∈𝔪} |F_N(e(θ))| ≤ 2^n exp((−log 2 + δ)π(N))`. -/
theorem thmE1_B40 (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 40 < B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, minorArc B N θ →
      ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 + δ) * Nat.primeCounting N) := by
  obtain ⟨C, N₁, hE⟩ := thmE1 hSW hVV hJ (by linarith : (0 : ℝ) < B)
  set ε := δ / (2 * (|C| + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨N₂, h2⟩ := ev_log_rpow_neg (by linarith : (0 : ℝ) < B / 8 - 5) hε
  obtain ⟨N₃, h3⟩ := ev_log_rpow_neg (by linarith : (0 : ℝ) < B / 8) hε
  refine ⟨N₁ + N₂ + N₃ + 3, fun N hN θ hθ => (hE N (by omega) θ hθ).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have e1 : Real.log N ^ (5 - B / 8) = Real.log N ^ (-(B / 8 - 5)) := by congr 1; ring
  have e2 : (Real.log N ^ (B / 4)) ^ (-(1 / 2 : ℝ)) = Real.log N ^ (-(B / 8)) := by
    rw [← Real.rpow_mul hL0]; congr 1; ring
  rw [e1, e2]
  have ha := h2 N (by omega)
  have hb := h3 N (by omega)
  have ht0 : 0 ≤ Real.log N ^ (-(B / 8 - 5)) + Real.log N ^ (-(B / 8)) := by positivity
  have hC : C * (Real.log N ^ (-(B / 8 - 5)) + Real.log N ^ (-(B / 8))) ≤
      |C| * (Real.log N ^ (-(B / 8 - 5)) + Real.log N ^ (-(B / 8))) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) ht0
  have hC2 : |C| * (Real.log N ^ (-(B / 8 - 5)) + Real.log N ^ (-(B / 8))) ≤ |C| * (2 * ε) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  have hC3 : |C| * (2 * ε) ≤ δ := by
    have : |C| * (2 * ε) = δ * (|C| / (|C| + 1)) := by simp only [ε]; field_simp
    rw [this]
    have : |C| / (|C| + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  linarith

end ArcsAlgo.Core
