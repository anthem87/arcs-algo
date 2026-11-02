module

public import ArcsAlgo.LemmaW
public import ArcsAlgo.Classical.SiegelWalfisz
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false

/-!
# Lemma W(2): the size of `ν_{a/q}` (paper §3.5)

* `tan_alw_mod`, `sum_tan_zero`, `abs_tan_le`: `tan(πra/q)` depends on `r mod q`, sums to `0` over
  `(r, q) = 1` (pair `r` with `q − r`), and is `≤ q` in modulus off `𝒱`.
* `nu_bound_det`: grouping the primes by class, `|ν| ≤ ½(φ(q)qD + (q + 1)q²)` when
  `|S_r − S_1| ≤ D` for all `(r, q) = 1`, `S_r = Σ_{p≤N, p≡r} p`.
* `abel_count`, `abs_abel_le`, `primeSum_diff_le`: summation by parts,
  `|S_r − S_1| ≤ 2N max_{m≤N} |π(m;q,r) − π(m;q,1)|`.
* `classdiff_SW`: with Siegel–Walfisz (for `(log x)^{2B}`), `|π(m;q,r) − π(m;q,1)| ≤
  √N + 1 + 2C N e^{−c√(log N/2)}` for `m ≤ N`, `q ≤ (log N)^B`.
* `S2_lower`, `liK_diff_ge`: `S₂ ≥ ⌊N/2⌋²(π(N) − π(N/2))` and `li(y) − li(x) ≥ (y − x)/log y`.
* `ev_poly_exp`: `K L^k ≤ e^{γ√L}` for `L` large.
* `lemmaW2`: for `N ≥ N₀`, `3 ≤ q ≤ (log N)^B`, `(a, q) = 1`: `|ν| ≤ N² e^{−c√log N}`, `S₂ > 0`,
  `4|ν|/S₂ < π/(qN)` (so `peak` applies) and `|t*| ≤ 4|ν|/S₂ ≤ N^{−1}e^{−c√log N}`.

The only hypothesis is `SiegelWalfisz` (cited, ineffective constants).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-! ### `ν` grouped by residue classes -/

/-- `tan(πra/q)`, a function of `r mod q`. -/
theorem tan_alw_mod (q a w : ℕ) (hq : 0 < q) : tan (alw q a w) = tan (alw q a (w % q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : alw q a w = alw q a (w % q) + ((w / q * a : ℕ) : ℝ) * π := by
    unfold alw
    have h := Nat.div_add_mod w q
    have : (w : ℝ) = q * (w / q : ℕ) + (w % q : ℕ) := by exact_mod_cast h.symm
    rw [this]; push_cast; field_simp; ring
  rw [e]; exact Real.tan_periodic.nat_mul _ _

theorem abs_tan_le {q a w : ℕ} (hq : 1 ≤ q) (hv : ¬ vanish q a w) : |tan (alw q a w)| ≤ q := by
  have hc := cos_lower hq hv
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hcalw : alw q a w = π * (w * ((a : ℝ) / q)) := by unfold alw; ring
  rw [hcalw]
  set c := cos (π * (w * ((a : ℝ) / q)))
  have hc0 : 0 < |c| := lt_of_lt_of_le (by positivity) hc
  rw [Real.tan_eq_sin_div_cos, abs_div, div_le_iff₀ hc0]
  have h1 := abs_sin_le_one (π * (w * ((a : ℝ) / q)))
  have : 1 ≤ q * |c| := by rwa [div_le_iff₀ hq', mul_comm] at hc
  linarith

/-- A prime coprime to `q ≥ 3` never vanishes. -/
theorem not_vanish_coprime {q a w : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hw : w.Coprime q) :
    ¬ vanish q a w := by
  rintro ⟨c, hc⟩
  have hdz : (q : ℤ) ∣ 2 * w * a := ⟨2 * c + 1, by linarith⟩
  have hd : q ∣ 2 * w * a := by exact_mod_cast hdz
  have h2w : q ∣ 2 * w := Nat.Coprime.dvd_of_dvd_mul_right ha.symm hd
  have h2 : q ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hw.symm h2w
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- `S_r = Σ_{p ≤ N, p ≡ r (mod q)} p`. -/
noncomputable def primeSum (N q r : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), if n.Prime ∧ n % q = r then (n : ℝ) else 0

/-- `Σ_{(r,q)=1} tan(πra/q) = 0` (pair `r` with `q − r`). -/
theorem sum_tan_zero {q a : ℕ} (hq : 3 ≤ q) :
    ∑ r ∈ (range q).filter (fun r => r.Coprime q), tan (alw q a r) = 0 := by
  set s := (range q).filter (fun r => r.Coprime q)
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hle : ∀ r ∈ s, r ≤ q := fun r hr => (mem_range.mp (mem_filter.mp hr).1).le
  have hmem : ∀ r ∈ s, q - r ∈ s := by
    intro r hr
    have hr' := mem_filter.mp hr
    have hr0 : r ≠ 0 := by
      rintro rfl; have := hr'.2; rw [Nat.coprime_zero_left] at this; omega
    simp only [s, mem_filter, mem_range]
    exact ⟨by omega, (Nat.coprime_self_sub_left (hle r hr)).mpr hr'.2⟩
  have hneg : ∀ r ∈ s, tan (alw q a (q - r)) = -tan (alw q a r) := by
    intro r hr
    have e : alw q a (q - r) = -alw q a r + (a : ℝ) * π := by
      unfold alw; rw [Nat.cast_sub (hle r hr)]; field_simp; ring
    rw [e, Real.tan_periodic.nat_mul a, Real.tan_neg]
  have hsw : ∑ r ∈ s, tan (alw q a r) = ∑ r ∈ s, tan (alw q a (q - r)) := by
    refine Finset.sum_nbij' (fun r => q - r) (fun r => q - r) hmem hmem
      (fun r hr => by have := hle r hr; omega) (fun r hr => by have := hle r hr; omega) fun r hr => ?_
    have := hle r hr
    rw [show q - (q - r) = r by omega]
  rw [sum_congr rfl hneg, sum_neg_distrib] at hsw
  linarith

/-- **`ν` by classes**: for `q ≥ 3`, `(a, q) = 1`, if `|S_r − S_1| ≤ D` for every `(r, q) = 1`, then
`|ν_{a/q}| ≤ ½(φ(q)qD + (q + 1)q²)` (the weight `1` and the primes dividing `q` give the second
term). -/
theorem nu_bound_det {q a N : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ r < q, r.Coprime q → |primeSum N q r - primeSum N q 1| ≤ D) :
    |nuW (WN N) q a| ≤ (1 / 2) * (q.totient * q * D + (q + 1) * q ^ 2) := by
  have hq1 : 1 ≤ q := by omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set W' := (WN N).filter (fun w => ¬ vanish q a w)
  set s := (range q).filter (fun r => r.Coprime q)
  set good : ℕ → Prop := fun w => w.Prime ∧ w.Coprime q
  have hT : ∀ r ∈ s, |tan (alw q a r)| ≤ q := fun r hr =>
    abs_tan_le hq1 (not_vanish_coprime hq ha (mem_filter.mp hr).2)
  -- the main part, by classes
  have hgood : W'.filter good = (range (N + 1)).filter good := by
    ext w
    simp only [W', good, WN, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨⟨h, _⟩, _⟩, hp, hc⟩; exact ⟨h, hp, hc⟩
    · rintro ⟨h, hp, hc⟩; exact ⟨⟨⟨h, Or.inr hp⟩, not_vanish_coprime hq ha hc⟩, hp, hc⟩
  have hcopmod : ∀ n, (n % q).Coprime q ↔ n.Coprime q := by
    intro n
    rw [Nat.Coprime, Nat.Coprime, ← Nat.gcd_rec q n, Nat.gcd_comm q n]
  have hmain : ∑ w ∈ W'.filter good, (w : ℝ) * tan (alw q a w) =
      ∑ r ∈ s, tan (alw q a r) * primeSum N q r := by
    rw [hgood]
    simp only [primeSum, mul_sum]
    rw [sum_comm]
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · by_cases hc : n.Coprime q
      · rw [if_pos ⟨hp, hc⟩, tan_alw_mod q a n (by omega)]
        have hmem : n % q ∈ s := by
          simp only [s, mem_filter, mem_range]; exact ⟨Nat.mod_lt _ (by omega), (hcopmod n).mpr hc⟩
        rw [← sum_erase_add _ _ hmem, sum_eq_zero, zero_add]
        · simp [hp]; ring
        · intro r hr
          rw [if_neg]; · ring
          rintro ⟨-, h⟩; exact (mem_erase.mp hr).1 h.symm
      · rw [if_neg (fun h => hc h.2)]
        refine (sum_eq_zero fun r hr => ?_).symm
        rw [if_neg]; · ring
        rintro ⟨-, h⟩
        apply hc; rw [← hcopmod n, h]; exact (mem_filter.mp hr).2
    · rw [if_neg (fun h => hp h.1)]
      exact (sum_eq_zero fun r _ => by rw [if_neg (fun h => hp h.1)]; ring).symm
  have hshift : ∑ r ∈ s, tan (alw q a r) * primeSum N q r =
      ∑ r ∈ s, tan (alw q a r) * (primeSum N q r - primeSum N q 1) := by
    have h0 : ∑ i ∈ s, tan (alw q a i) = 0 := sum_tan_zero hq
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [h0]; ring
  have hcard : (s.card : ℝ) = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 2; ext r; simp [s, Nat.coprime_comm]
  have hM : |∑ w ∈ W'.filter good, (w : ℝ) * tan (alw q a w)| ≤ q.totient * q * D := by
    rw [hmain, hshift]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ s, |tan (alw q a r) * (primeSum N q r - primeSum N q 1)| ≤ ∑ _r ∈ s, (q : ℝ) * D := by
          refine sum_le_sum fun r hr => ?_
          rw [abs_mul]
          have hr' := mem_filter.mp hr
          exact mul_le_mul (hT r hr) (hD r (mem_range.mp hr'.1) hr'.2) (abs_nonneg _) hq'.le
      _ = q.totient * q * D := by rw [sum_const, nsmul_eq_mul, hcard]; ring
  -- the rest: `1` and the primes dividing `q`
  have hrest_sub : W'.filter (fun w => ¬ good w) ⊆ range (q + 1) := by
    intro w hw
    simp only [W', good, WN, mem_filter, mem_range] at hw ⊢
    obtain ⟨⟨⟨_, h1 | hp⟩, _⟩, hng⟩ := hw
    · omega
    · have : ¬ w.Coprime q := fun hc => hng ⟨hp, hc⟩
      have hd : w ∣ q := (Nat.Prime.dvd_iff_not_coprime hp).mpr this
      have := Nat.le_of_dvd (by omega) hd; omega
  have hR : |∑ w ∈ W'.filter (fun w => ¬ good w), (w : ℝ) * tan (alw q a w)| ≤ (q + 1) * q ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w ∈ W'.filter (fun w => ¬ good w), |(w : ℝ) * tan (alw q a w)|
        ≤ ∑ _w ∈ W'.filter (fun w => ¬ good w), (q : ℝ) * q := by
          refine sum_le_sum fun w hw => ?_
          rw [abs_mul, Nat.abs_cast]
          have hwq : (w : ℝ) ≤ q := by
            have := mem_range.mp (hrest_sub hw); exact_mod_cast (by omega : w ≤ q)
          have hv := (mem_filter.mp (mem_filter.mp hw).1).2
          exact mul_le_mul hwq (abs_tan_le hq1 hv) (abs_nonneg _) hq'.le
      _ ≤ (q + 1) * q ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
          have : ((W'.filter (fun w => ¬ good w)).card : ℝ) ≤ q + 1 := by
            have := card_le_card hrest_sub; rw [card_range] at this; exact_mod_cast this
          nlinarith
  unfold nuW
  rw [← sum_filter_add_sum_filter_not W' good, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hM hR)) (by norm_num)

/-! ### Summation by parts -/

theorem abel_count (d : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), (n : ℝ) * d n =
      ∑ k ∈ range N, (∑ n ∈ range (N + 1), d n - ∑ n ∈ range (k + 1), d n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k => ∑ n ∈ range (N + 1 + 1), d n - ∑ n ∈ range (k + 1), d n)]
    have e : ∀ k ∈ range N, ∑ n ∈ range (N + 1 + 1), d n - ∑ n ∈ range (k + 1), d n =
        (∑ n ∈ range (N + 1), d n - ∑ n ∈ range (k + 1), d n) + d (N + 1) := by
      intro k _; rw [sum_range_succ _ (N + 1)]; ring
    rw [sum_congr rfl e, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_range_succ _ (N + 1)]
    push_cast; ring

theorem abs_abel_le (d : ℕ → ℝ) (N : ℕ) {M : ℝ} (hM : ∀ m ≤ N, |∑ n ∈ range (m + 1), d n| ≤ M) :
    |∑ n ∈ range (N + 1), (n : ℝ) * d n| ≤ 2 * N * M := by
  rw [abel_count]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range N, |∑ n ∈ range (N + 1), d n - ∑ n ∈ range (k + 1), d n|
      ≤ ∑ _k ∈ range N, 2 * M := sum_le_sum fun k hk => by
        have h1 := hM N le_rfl
        have h2 := hM k (mem_range.mp hk).le
        calc |∑ n ∈ range (N + 1), d n - ∑ n ∈ range (k + 1), d n|
            ≤ |∑ n ∈ range (N + 1), d n| + |∑ n ∈ range (k + 1), d n| := abs_sub _ _
          _ ≤ 2 * M := by linarith
    _ = 2 * N * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- `S_r − S_1 = Σ_{n≤N} n (1[n ∈ class r] − 1[n ∈ class 1])`, with partial sums `π(m;q,r) − π(m;q,1)`. -/
theorem primeSum_diff_le {N q r : ℕ} (hq : 2 ≤ q) (hr : r < q) {M : ℝ}
    (hM : ∀ m ≤ N, |(cntQ m q r : ℝ) - cntQ m q 1| ≤ M) :
    |primeSum N q r - primeSum N q 1| ≤ 2 * N * M := by
  set d : ℕ → ℝ := fun n => (if n.Prime ∧ n % q = r then 1 else 0) - (if n.Prime ∧ n % q = 1 then 1 else 0)
  have hS : primeSum N q r - primeSum N q 1 = ∑ n ∈ range (N + 1), (n : ℝ) * d n := by
    unfold primeSum; rw [← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [d]; split_ifs <;> ring
  have hD : ∀ m, ∑ n ∈ range (m + 1), d n = (cntQ m q r : ℝ) - cntQ m q 1 := by
    intro m
    simp only [d, sum_sub_distrib, cntQ, card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_one]
    rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : 1 < q)]
    push_cast; rfl
  rw [hS]
  exact abs_abel_le d N fun m hm => (hD m).symm ▸ hM m hm


/-! ### Asymptotics -/

theorem ev_poly_exp (k : ℝ) {γ : ℝ} (hγ : 0 < γ) (K : ℝ) :
    ∃ L₀ ≥ (1 : ℝ), ∀ L ≥ L₀, K * L ^ k ≤ Real.exp (γ * √L) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * k) γ hγ).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (|K| + 1) by positivity))
  obtain ⟨u₀, hu₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max 1 (max u₀ 0 ^ 2), le_max_left _ _, fun L hL => ?_⟩
  have hL0 : 0 ≤ L := le_trans zero_le_one (le_trans (le_max_left _ _) hL)
  set u := √L with hudef
  have hu0 : 0 ≤ u := Real.sqrt_nonneg L
  have hu : u₀ ≤ u := by
    have h2 : max u₀ 0 ^ 2 ≤ L := le_trans (le_max_right _ _) hL
    have := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq (le_max_right _ _)] at this
    exact le_trans (le_max_left _ _) this
  have h1 := hu₀ u hu
  have hLk : L ^ k = u ^ (2 * k) := by
    rw [Real.rpow_mul hu0, show u ^ (2 : ℝ) = L by rw [Real.rpow_two, hudef, Real.sq_sqrt hL0]]
  have he : 0 < Real.exp (γ * u) := Real.exp_pos _
  have h2 : u ^ (2 * k) ≤ Real.exp (γ * u) / (|K| + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have e : Real.exp (-γ * u) * Real.exp (γ * u) = 1 := by rw [← Real.exp_add]; simp
    have : u ^ (2 * k) * Real.exp (-γ * u) * Real.exp (γ * u) ≤ 1 / (|K| + 1) * Real.exp (γ * u) :=
      mul_le_mul_of_nonneg_right h1.le he.le
    rw [mul_assoc, e, mul_one] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at this
    linarith
  have hpos : 0 ≤ u ^ (2 * k) := Real.rpow_nonneg hu0 _
  rw [hLk]
  calc K * u ^ (2 * k) ≤ |K| * u ^ (2 * k) := mul_le_mul_of_nonneg_right (le_abs_self K) hpos
    _ ≤ |K| * (Real.exp (γ * u) / (|K| + 1)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    _ ≤ Real.exp (γ * u) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg K]

theorem cnt_one (m : ℕ) : cntQ m 1 0 = ((range (m + 1)).filter Nat.Prime).card := by
  unfold cntQ; congr 1; ext n; simp [Nat.mod_one]

/-- `S₂ ≥ N′²(π(N) − π(N′))` with `N′ = ⌊N/2⌋ ≥ q`: the primes of `(N′, N]` are coprime to `q`. -/
theorem S2_lower {N q a : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hqN : q ≤ N / 2) :
    ((N / 2 : ℕ) : ℝ) ^ 2 * ((cntQ N 1 0 : ℝ) - cntQ (N / 2) 1 0) ≤ S2W (WN N) q a := by
  set N' := N / 2
  set T := (range (N + 1)).filter (fun n => n.Prime ∧ N' < n)
  have hT : T ⊆ (WN N).filter (fun w => ¬ vanish q a w) := by
    intro n hn
    obtain ⟨hr, hp, hlt⟩ := by simpa [T] using hn
    simp only [WN, mem_filter, mem_range]
    refine ⟨⟨by omega, Or.inr hp⟩, not_vanish_coprime hq ha ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega
  have hcard : ((cntQ N 1 0 : ℝ) - cntQ N' 1 0) = T.card := by
    rw [cnt_one, cnt_one]
    have hsub : (range (N' + 1)).filter Nat.Prime ⊆ (range (N + 1)).filter Nat.Prime := by
      intro n hn; simp only [mem_filter, mem_range] at hn ⊢; exact ⟨by omega, hn.2⟩
    have e : T = (range (N + 1)).filter Nat.Prime \ (range (N' + 1)).filter Nat.Prime := by
      ext n; simp only [T, mem_filter, mem_range, mem_sdiff]; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun h => by omega⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by by_contra h; exact h3 ⟨by omega, h2⟩⟩
    rw [e, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  rw [hcard]
  unfold S2W
  calc ((N' : ℕ) : ℝ) ^ 2 * T.card = ∑ _n ∈ T, ((N' : ℕ) : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ T, (n : ℝ) ^ 2 := sum_le_sum fun n hn => by
        have : N' < n := (mem_filter.mp hn).2.2
        have : ((N' : ℕ) : ℝ) ≤ n := by exact_mod_cast this.le
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => sq_nonneg _

theorem liK_diff_ge {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : (y - x) / Real.log y ≤ liK 0 y - liK 0 x := by
  have hy : 2 ≤ y := le_trans hx hxy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have e : liK 0 y - liK 0 x = ∫ t in x..y, liIntegrand 0 t := by
    unfold liK
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_liIntegrand 0 0 x)
      (intervalIntegrable_liIntegrand 0 x y)]; ring
  rw [e]
  have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume) hxy
    (intervalIntegrable_const (c := 1 / Real.log y)) (intervalIntegrable_liIntegrand 0 x y) fun t ht => by
      have ht2 : 2 < t := by linarith [ht.1]
      unfold liIntegrand; rw [if_pos ht2, pow_zero]
      exact one_div_le_one_div_of_le (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) ht.2.le)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  rw [div_eq_mul_one_div]; exact this

theorem classdiff_SW {c₀ C₀ B : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hB : 0 < B)
    (hsw : ∀ m : ℕ, 2 ≤ m → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log m ^ (2 * B) → a.Coprime q →
      |(cntQ m q a : ℝ) - liK 0 m / q.totient| ≤ C₀ * m * Real.exp (-c₀ * √(Real.log m)))
    {N q r : ℕ} (hN : 4 ≤ N) (hL4 : 4 ≤ Real.log N) (hq1 : 1 ≤ q) (hqL : (q : ℝ) ≤ Real.log N ^ B)
    (hr : r.Coprime q) (m : ℕ) (hm : m ≤ N) :
    |(cntQ m q r : ℝ) - cntQ m q 1| ≤ √N + 1 + 2 * C₀ * N * Real.exp (-c₀ * √(Real.log N / 2)) := by
  set L := Real.log N
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hext : 0 ≤ 2 * C₀ * N * Real.exp (-c₀ * √(L / 2)) := by positivity
  by_cases hsm : (m : ℝ) < √N
  · have h1 := cntQ_le m q r
    have h2 := cntQ_le m q 1
    have h0 : (0 : ℝ) ≤ cntQ m q r := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ cntQ m q 1 := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  · push Not at hsm
    have hs2 : (2 : ℝ) ≤ √N := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hN'
    have hm2 : 2 ≤ m := by have : (2 : ℝ) ≤ m := le_trans hs2 hsm; exact_mod_cast this
    have hlogm : L / 2 ≤ Real.log m := by
      have := Real.log_le_log (by positivity) hsm
      rwa [Real.log_sqrt (by positivity)] at this
    have hL0 : 0 ≤ L := by linarith
    have hqm : (q : ℝ) ≤ Real.log m ^ (2 * B) := by
      refine hqL.trans ?_
      have h1 : L ^ B ≤ ((L / 2) ^ 2) ^ B := Real.rpow_le_rpow hL0 (by nlinarith) hB.le
      have h2 : ((L / 2) ^ 2) ^ B = (L / 2) ^ (2 * B) := by
        rw [Real.rpow_mul (by linarith), Real.rpow_two]
      have h3 : (L / 2) ^ (2 * B) ≤ Real.log m ^ (2 * B) := Real.rpow_le_rpow (by linarith) hlogm (by positivity)
      linarith
    have hA := hsw m hm2 q r hq1 hqm hr
    have hB1 := hsw m hm2 q 1 hq1 hqm (Nat.coprime_one_left q)
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
    have hexp : Real.exp (-c₀ * √(Real.log m)) ≤ Real.exp (-c₀ * √(L / 2)) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_le_sqrt hlogm
      nlinarith
    have h4 : |(cntQ m q r : ℝ) - cntQ m q 1| ≤ 2 * (C₀ * m * Real.exp (-c₀ * √(Real.log m))) := by
      calc |(cntQ m q r : ℝ) - cntQ m q 1|
          = |((cntQ m q r : ℝ) - liK 0 m / q.totient) - ((cntQ m q 1 : ℝ) - liK 0 m / q.totient)| := by
            congr 1; ring
        _ ≤ |(cntQ m q r : ℝ) - liK 0 m / q.totient| + |(cntQ m q 1 : ℝ) - liK 0 m / q.totient| := abs_sub _ _
        _ ≤ _ := by linarith
    have h5 : C₀ * m * Real.exp (-c₀ * √(Real.log m)) ≤ C₀ * N * Real.exp (-c₀ * √(L / 2)) := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have he0 : 0 ≤ Real.exp (-c₀ * √(Real.log m)) := (Real.exp_pos _).le
      calc C₀ * m * Real.exp (-c₀ * √(Real.log m)) ≤ C₀ * N * Real.exp (-c₀ * √(Real.log m)) := by gcongr
        _ ≤ C₀ * N * Real.exp (-c₀ * √(L / 2)) := by gcongr
    have : (0 : ℝ) ≤ √N := Real.sqrt_nonneg _
    linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma W(2) with Siegel–Walfisz** (paper §3.5): fix `B > 0`. There are `c > 0` and `N₀` such
that for `N ≥ N₀`, `3 ≤ q ≤ (log N)^B` and `(a, q) = 1` (weights `W_N = {1} ∪ {p ≤ N}`):
`|ν_{a/q}| ≤ N² e^{−c√log N}`, `S₂ > 0`, `4|ν|/S₂ < π/(qN)` (so `peak` applies: the maximum `t*` lies
inside the window), `|t*| ≤ 4|ν|/S₂ ≤ N^{−1} e^{−c√log N}`, and `S₂ ≥ N³/(64 log N)`. The only hypothesis is
Siegel–Walfisz. -/
theorem lemmaW2 (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) :
    ∃ c > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ Real.log N ^ B → a.Coprime q →
      |nuW (WN N) q a| ≤ (N : ℝ) ^ 2 * Real.exp (-c * √(Real.log N)) ∧ 0 < S2W (WN N) q a ∧
      4 * |nuW (WN N) q a| / S2W (WN N) q a < π / (q * N) ∧
      4 * |nuW (WN N) q a| / S2W (WN N) q a ≤ Real.exp (-c * √(Real.log N)) / N ∧
      (N : ℝ) ^ 3 / (64 * Real.log N) ≤ S2W (WN N) q a := by
  obtain ⟨c₀, hc₀, C₀, hC₀, h2⟩ := hSW (2 * B) (by positivity)
  obtain ⟨c₁, hc₁, C₁, hC₁, h1⟩ := hSW 1 one_pos
  set c := c₀ / 4 with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨E1, hE1, hE1'⟩ := ev_poly_exp (2 * B) one_pos 4
  obtain ⟨E2, hE2, hE2'⟩ := ev_poly_exp (2 * B) (by positivity : 0 < c₀ / 4) (8 * C₀)
  obtain ⟨E3, hE3, hE3'⟩ := ev_poly_exp (3 * B) one_pos 4
  obtain ⟨E4, hE4, hE4'⟩ := ev_poly_exp 1 (by positivity : 0 < c₁ / 2) (8 * C₁)
  obtain ⟨E5, hE5, hE5'⟩ := ev_poly_exp B one_pos 1
  obtain ⟨E6, hE6, hE6'⟩ := ev_poly_exp (B + 1) (by positivity : 0 < c / 2) 256
  set L₁ := max (max (max E1 E2) (max E3 E4)) (max (max E5 E6) (max (4 * (c + 1) ^ 2) 16))
  refine ⟨c / 2, by positivity, ⌈Real.exp L₁⌉₊ + 16, fun N hN q a hq hqL ha => ?_⟩
  set Nr : ℝ := (N : ℝ) with hNr
  set L := Real.log Nr
  have hN16 : (16 : ℝ) ≤ Nr := by
    have : 16 ≤ N := by omega
    rw [hNr]; exact_mod_cast this
  have hNpos : 0 < Nr := by linarith
  have hLL : L₁ ≤ L := by
    have : Real.exp L₁ ≤ Nr := le_trans (Nat.le_ceil _) (by
      rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp L₁⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL16 : 16 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hLL)
  have hLc : 4 * (c + 1) ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hLL)
  have hL1 : E1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hLL
  have hL2 : E2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hLL
  have hL3 : E3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hLL
  have hL4' : E4 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hLL
  have hL5 : E5 ≤ L := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hLL
  have hL6 : E6 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hLL
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : 0 ≤ √L := Real.sqrt_nonneg L
  have hsqLsq : √L * √L = L := Real.mul_self_sqrt hL0.le
  have hq1 : 1 ≤ q := by omega
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  set Q := L ^ B with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow (by linarith) hB.le
  have hqQ : (q : ℝ) ≤ Q := hqL
  have hQ2 : Q ^ 2 = L ^ (2 * B) := by rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have hQ3 : Q ^ 3 = L ^ (3 * B) := by rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have hsqrtN : √Nr = Real.exp (L / 2) := by
    rw [← hexpL, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hsqN1 : 1 ≤ √Nr := by rw [hsqrtN]; exact Real.one_le_exp (by linarith)
  have hsqN2 : √Nr * √Nr = Nr := Real.mul_self_sqrt hNpos.le
  -- `√(L/2) ≥ √L/2`
  have hhalf : √L / 2 ≤ √(L / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, sq_sqrt hL0.le]; linarith
  -- the class differences
  have hM := fun (r : ℕ) (hr : r.Coprime q) (m : ℕ) (hm : m ≤ N) =>
    classdiff_SW hc₀ hC₀ hB (fun m hm q a h1 h2' h3 => h2 m hm q a h1 h2' h3)
      (by omega : 4 ≤ N) (by linarith : (4 : ℝ) ≤ L) hq1 hqL hr m hm
  set M := √Nr + 1 + 2 * C₀ * Nr * Real.exp (-c₀ * √(L / 2))
  have hM0 : 0 ≤ M := by positivity
  have hD : ∀ r < q, r.Coprime q → |primeSum N q r - primeSum N q 1| ≤ 2 * N * M :=
    fun r hr hrc => primeSum_diff_le (by omega) hr (hM r hrc)
  have hν := nu_bound_det hq ha (by positivity) hD
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  -- `|ν| ≤ N² e^{−c√L}`
  have he1 : 4 * L ^ (2 * B) ≤ Real.exp (1 * √L) := hE1' L hL1
  have he2 : 8 * C₀ * L ^ (2 * B) ≤ Real.exp (c₀ / 4 * √L) := hE2' L hL2
  have he3 : 4 * L ^ (3 * B) ≤ Real.exp (1 * √L) := hE3' L hL3
  have hcs : (1 + c) * √L ≤ L / 2 := by
    have : 2 * (c + 1) ≤ √L := by
      rw [Real.le_sqrt (by positivity) hL0.le]; nlinarith
    nlinarith
  have hA : Q ^ 2 * Nr * √Nr ≤ Nr ^ 2 * Real.exp (-c * √L) / 4 := by
    have h : 4 * Q ^ 2 * Real.exp (c * √L) ≤ √Nr := by
      rw [hQ2, hsqrtN]
      calc 4 * L ^ (2 * B) * Real.exp (c * √L) ≤ Real.exp (1 * √L) * Real.exp (c * √L) := by gcongr
        _ = Real.exp ((1 + c) * √L) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hcs
    have hexpc : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp (c * √L) := Real.exp_pos _
    rw [le_div_iff₀ (by norm_num)]
    calc Q ^ 2 * Nr * √Nr * 4 = 4 * Q ^ 2 * (Nr * √Nr) * (Real.exp (-c * √L) * Real.exp (c * √L)) := by
          rw [hexpc]; ring
      _ = (4 * Q ^ 2 * Real.exp (c * √L)) * (Nr * √Nr) * Real.exp (-c * √L) := by ring
      _ ≤ √Nr * (Nr * √Nr) * Real.exp (-c * √L) := by gcongr
      _ = Nr ^ 2 * Real.exp (-c * √L) := by rw [show √Nr * (Nr * √Nr) = Nr * (√Nr * √Nr) by ring, hsqN2]; ring
  have hB' : Q ^ 2 * Nr ≤ Q ^ 2 * Nr * √Nr := le_mul_of_one_le_right (by positivity) hsqN1
  have hC : 2 * C₀ * Q ^ 2 * Nr ^ 2 * Real.exp (-c₀ * √(L / 2)) ≤ Nr ^ 2 * Real.exp (-c * √L) / 4 := by
    have hx : Real.exp (-c₀ * √(L / 2)) ≤ Real.exp (-(c₀ / 2) * √L) := Real.exp_le_exp.mpr (by nlinarith)
    have h8 : 8 * C₀ * Q ^ 2 ≤ Real.exp (c₀ / 4 * √L) := by rw [hQ2]; linarith
    have hexp : Real.exp (c₀ / 4 * √L) * Real.exp (-(c₀ / 2) * √L) = Real.exp (-c * √L) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    have hpos : 0 ≤ Nr ^ 2 := sq_nonneg _
    calc 2 * C₀ * Q ^ 2 * Nr ^ 2 * Real.exp (-c₀ * √(L / 2))
        ≤ 2 * C₀ * Q ^ 2 * Nr ^ 2 * Real.exp (-(c₀ / 2) * √L) := by gcongr
      _ = (8 * C₀ * Q ^ 2) * Real.exp (-(c₀ / 2) * √L) * Nr ^ 2 / 4 := by ring
      _ ≤ Real.exp (c₀ / 4 * √L) * Real.exp (-(c₀ / 2) * √L) * Nr ^ 2 / 4 := by gcongr
      _ = _ := by rw [hexp]; ring
  have hD3 : Q ^ 3 ≤ Nr ^ 2 * Real.exp (-c * √L) / 4 := by
    have h : 4 * Q ^ 3 * Real.exp (c * √L) ≤ Nr ^ 2 := by
      rw [hQ3]
      calc 4 * L ^ (3 * B) * Real.exp (c * √L) ≤ Real.exp (1 * √L) * Real.exp (c * √L) := by gcongr
        _ = Real.exp ((1 + c) * √L) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
        _ = Nr ^ 2 := by rw [show 2 * L = L + L by ring, Real.exp_add, hexpL]; ring
    have hexpc : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
    rw [le_div_iff₀ (by norm_num)]
    have hpos : 0 < Real.exp (-c * √L) := Real.exp_pos _
    nlinarith
  have hνb : |nuW (WN N) q a| ≤ Nr ^ 2 * Real.exp (-c * √L) := by
    refine hν.trans ?_
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have h1' : (q.totient : ℝ) * q * (2 * N * M) ≤ Q ^ 2 * (2 * Nr * M) := by
      have : (q.totient : ℝ) * q ≤ Q ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) q.totient]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h2' : ((q : ℝ) + 1) * q ^ 2 ≤ 2 * Q ^ 3 := by
      have h3 : (q : ℝ) ^ 3 ≤ Q ^ 3 := pow_le_pow_left₀ (by linarith) hqQ 3
      nlinarith
    have hexp0 : 0 ≤ 2 * C₀ * Nr * Real.exp (-c₀ * √(L / 2)) := by positivity
    have : Q ^ 2 * (2 * Nr * M) = 2 * (Q ^ 2 * Nr * √Nr + Q ^ 2 * Nr +
        2 * C₀ * Q ^ 2 * Nr ^ 2 * Real.exp (-c₀ * √(L / 2))) := by simp only [M]; ring
    nlinarith
  -- `S₂ ≥ N³/(64 L)`
  have hNh : q ≤ N / 2 := by
    have h5 : 1 * L ^ B ≤ Real.exp (1 * √L) := hE5' L hL5
    have hs : 1 * √L + Real.log 4 ≤ L := by
      have : √L ≤ L / 4 := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      have : Real.log 4 < 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      linarith
    have : (q : ℝ) * 4 ≤ Nr := by
      have h6 : Real.exp (1 * √L) * 4 ≤ Nr := by
        rw [← hexpL, show (4 : ℝ) = Real.exp (Real.log 4) by rw [Real.exp_log (by norm_num)], ← Real.exp_add]
        exact Real.exp_le_exp.mpr hs
      nlinarith
    rw [hNr] at this
    have : q * 4 ≤ N := by exact_mod_cast this
    omega
  set N' := N / 2
  have hN'r : Nr / 4 ≤ (N' : ℝ) := by
    have : (N : ℝ) / 2 - 1 ≤ (N' : ℝ) := by
      have h := Nat.div_add_mod N 2
      have : ((N % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : N % 2 ≤ 1)
      have e : (N : ℝ) = 2 * N' + (N % 2 : ℕ) := by exact_mod_cast h.symm
      linarith
    linarith
  have hN'2 : 3 ≤ N' := by have : (3 : ℝ) ≤ N' := by linarith
                           exact_mod_cast this
  have hNN' : (N' : ℝ) ≤ Nr / 2 := by
    have := Nat.div_mul_le_self N 2
    have : ((N' * 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at this; linarith
  have hS2 := S2_lower hq ha hNh
  -- counts via Siegel–Walfisz at `q = 1`
  have hlog1 : ∀ m : ℕ, 3 ≤ m → ((1 : ℕ) : ℝ) ≤ Real.log m ^ (1 : ℝ) := by
    intro m hm
    rw [Real.rpow_one]; push_cast
    have : (Real.exp 1 : ℝ) ≤ m := by
      have := Real.exp_one_lt_d9; have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [Real.le_log_iff_exp_le (by positivity)]; exact this
  have hSWN := h1 N (by omega) 1 0 le_rfl (hlog1 N (by omega)) (Nat.coprime_zero_left 1 |>.mpr rfl)
  have hSWN' := h1 N' (by omega) 1 0 le_rfl (hlog1 N' hN'2) (Nat.coprime_zero_left 1 |>.mpr rfl)
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hSWN hSWN'
  have hli := liK_diff_ge (show (2 : ℝ) ≤ N' by linarith) (show (N' : ℝ) ≤ Nr by linarith)
  have hlogN' : L / 2 ≤ Real.log N' := by
    have : √Nr ≤ N' := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_sqrt hNpos.le] at this
  have herr : C₁ * Nr * Real.exp (-c₁ * √L) + C₁ * N' * Real.exp (-c₁ * √(Real.log N')) ≤
      2 * C₁ * Nr * Real.exp (-(c₁ / 2) * √L) := by
    have e1 : Real.exp (-c₁ * √L) ≤ Real.exp (-(c₁ / 2) * √L) := Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (-c₁ * √(Real.log N')) ≤ Real.exp (-(c₁ / 2) * √L) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_le_sqrt hlogN'
      nlinarith
    have : (N' : ℝ) ≤ Nr := by linarith
    have hp : 0 ≤ Real.exp (-(c₁ / 2) * √L) := (Real.exp_pos _).le
    calc C₁ * Nr * Real.exp (-c₁ * √L) + C₁ * N' * Real.exp (-c₁ * √(Real.log N'))
        ≤ C₁ * Nr * Real.exp (-(c₁ / 2) * √L) + C₁ * Nr * Real.exp (-(c₁ / 2) * √L) := by
          gcongr
      _ = _ := by ring
  have he4 : 8 * C₁ * L ^ (1 : ℝ) ≤ Real.exp (c₁ / 2 * √L) := hE4' L hL4'
  rw [Real.rpow_one] at he4
  have hcnt : Nr / (4 * L) ≤ (cntQ N 1 0 : ℝ) - cntQ N' 1 0 := by
    have hli' : Nr / (2 * L) ≤ liK 0 Nr - liK 0 N' := by
      refine le_trans ?_ hli
      rw [div_le_div_iff₀ (by positivity) hL0]; nlinarith
    have hsmall : 2 * C₁ * Nr * Real.exp (-(c₁ / 2) * √L) ≤ Nr / (4 * L) := by
      have hexp : Real.exp (c₁ / 2 * √L) * Real.exp (-(c₁ / 2) * √L) = 1 := by rw [← Real.exp_add]; simp
      rw [le_div_iff₀ (by positivity)]
      have hp : 0 < Real.exp (-(c₁ / 2) * √L) := Real.exp_pos _
      have h8 : 8 * C₁ * L * Real.exp (-(c₁ / 2) * √L) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right he4 hp.le; rwa [hexp] at this
      calc 2 * C₁ * Nr * Real.exp (-(c₁ / 2) * √L) * (4 * L) = Nr * (8 * C₁ * L * Real.exp (-(c₁ / 2) * √L)) := by
            ring
        _ ≤ Nr * 1 := mul_le_mul_of_nonneg_left h8 hNpos.le
        _ = Nr := mul_one _
    rw [abs_le] at hSWN hSWN'
    have e2 : Nr / (2 * L) = 2 * (Nr / (4 * L)) := by field_simp; ring
    linarith [hSWN.1, hSWN'.2]
  have hS2lo : Nr ^ 3 / (64 * L) ≤ S2W (WN N) q a := by
    refine le_trans ?_ hS2
    have h1' : (Nr / 4) ^ 2 ≤ (N' : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN'r 2
    have : Nr ^ 3 / (64 * L) = (Nr / 4) ^ 2 * (Nr / (4 * L)) := by field_simp; ring
    rw [this]
    exact mul_le_mul h1' hcnt (by positivity) (by positivity)
  have hS2pos : 0 < S2W (WN N) q a := lt_of_lt_of_le (by positivity) hS2lo
  -- the window
  have hratio : 4 * |nuW (WN N) q a| / S2W (WN N) q a ≤ 256 * L * Real.exp (-c * √L) / Nr := by
    rw [div_le_div_iff₀ hS2pos hNpos]
    have h4 : 4 * |nuW (WN N) q a| * Nr ≤ 4 * (Nr ^ 2 * Real.exp (-c * √L)) * Nr := by gcongr
    have h5 : 4 * (Nr ^ 2 * Real.exp (-c * √L)) * Nr = 256 * L * Real.exp (-c * √L) * (Nr ^ 3 / (64 * L)) := by
      field_simp; ring
    rw [h5] at h4
    have : 0 ≤ 256 * L * Real.exp (-c * √L) := by positivity
    nlinarith
  have he6 : 256 * L ^ (B + 1) ≤ Real.exp (c / 2 * √L) := hE6' L hL6
  have hLB : L * q ≤ L ^ (B + 1) := by
    rw [Real.rpow_add hL0, Real.rpow_one]
    calc L * q ≤ L * L ^ B := mul_le_mul_of_nonneg_left hqQ hL0.le
      _ = L ^ B * L := by ring
  have hLle : L ≤ L ^ (B + 1) := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L) (by linarith : (1 : ℝ) ≤ B + 1)
    rwa [Real.rpow_one] at this
  have hexpc : Real.exp (c / 2 * √L) * Real.exp (-c * √L) = Real.exp (-(c / 2) * √L) := by
    rw [← Real.exp_add]; ring_nf
  have hkey : 256 * L * Real.exp (-c * √L) ≤ Real.exp (-(c / 2) * √L) := by
    rw [← hexpc]
    exact mul_le_mul_of_nonneg_right (by linarith [he6, hLle]) (Real.exp_pos _).le
  refine ⟨hνb.trans ?_, hS2pos, ?_, ?_, hS2lo⟩
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg _)
  · refine lt_of_le_of_lt hratio ?_
    rw [div_lt_div_iff₀ hNpos (by positivity)]
    have hq0 : (0 : ℝ) < q := by linarith
    have : 256 * L * q * Real.exp (-c * √L) ≤ Real.exp (-(c / 2) * √L) := by
      rw [← hexpc]
      exact mul_le_mul_of_nonneg_right (by linarith [he6, hLB]) (Real.exp_pos _).le
    have hlt : Real.exp (-(c / 2) * √L) < π := by
      have : Real.exp (-(c / 2) * √L) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ c / 2) hsqL; linarith)
      linarith [Real.two_le_pi]
    calc 256 * L * Real.exp (-c * √L) * (q * Nr) = (256 * L * q * Real.exp (-c * √L)) * Nr := by ring
      _ ≤ Real.exp (-(c / 2) * √L) * Nr := mul_le_mul_of_nonneg_right this hNpos.le
      _ < π * Nr := mul_lt_mul_of_pos_right hlt hNpos
  · exact hratio.trans (div_le_div_of_nonneg_right hkey hNpos.le)

end ArcsAlgo.Core
