module

public import ArcsAlgo.EdgeE2
public import ArcsAlgo.EdgeShoulder
set_option autoImplicit false

/-!
# Remark (the lobe exponent) (paper §3.5)

* `cq q = Λ(q/2)/φ(q)` (`q` even), `0` (`q` odd): the core level.
* `log_Gw_centre`: `|log|G(a/q)| − li(N)c_q| ≤ φ(q)E log q + (q + 1) log q` when every class count is within
  `E` of `li(N)/φ(q)` (Lemma 1, two-sided).
* `firstLocalMin`, `anti_first_min`, `remark_lobe_max`: for a first local minimum `X_q` of `A_q`, `X_q ≥ 1/(2q)`,
  `A_q` is non-increasing on `(0, X_q]`, and `ℓ*_q = max(A_q(1/(2q))/φ(q), ℓ_q)`.
* `remark_lobe_lt`: for `q ∈ 𝔈`, `ℓ*_q < c_q` (Lemma P).
* `remark_lobe_height`: `|G(θ*)| = 2^n exp(π(N)(−log 2 + c_q) + o(π(N)))`, uniformly in `q ≤ 𝔓` (Lemma W(3),
  Siegel–Walfisz).
* `remark_lobe_gap`: for each fixed `q ∈ 𝔈` the lobe error of (2) is `≤ e^{−γπ(N)}|G(θ*)|`,
  `γ = (c_q − ℓ*_q)/4 > 0`.
* `remark_lobe_other`: for `q ∉ 𝔈`, `c_q = 0 ≤ ℓ_q`.

The numerical gaps (about 0.016, 0.009, 0.006 for q = 6, 10, 14) are not formalized. The only hypothesis is
`SiegelWalfisz`.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Edge ArcsAlgo.Classical

/-- The core level `c_q = Λ(q/2)/φ(q)` for `q` even, `0` for `q` odd (`q ≥ 3`). -/
noncomputable def cq (q : ℕ) : ℝ := (if Even q then Λ (q / 2) else 0) / q.totient

/-- **The centre of an arc, two-sided**: if every class count is within `E` of `li(N)/φ(q)`, then
`|log|G(a/q)| − li(N)c_q| ≤ φ(q)E log q + (q + 1) log q` (`G = F_N` without the vanishing factor). -/
theorem log_Gw_centre {q a : ℕ} (h3 : 3 ≤ q) (ha : a.Coprime q) (N : ℕ) {E : ℝ}
    (hE : ∀ r ∈ resQ q, |(cntQ N q r : ℝ) - liK 0 N / q.totient| ≤ E) :
    |Real.log ‖Gw (WN N) q a ((a : ℝ) / q)‖ - liK 0 N * cq q| ≤
      q.totient * E * Real.log q + (q + 1) * Real.log q := by
  have hq0 : 0 < q := by omega
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast h3
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set V := (WN N).filter (fun w => ¬ vanish q a w)
  set f : ℕ → ℝ := fun w => Real.log (2 * |cos (π * (w * ((a : ℝ) / q)))|)
  -- each factor of `G` at `a/q`: `2/q ≤ 2|cos| ≤ 2`
  have hfb : ∀ w, ¬ vanish q a w → |f w| ≤ Real.log q := by
    intro w hw
    have hl := cos_lower (by omega : 1 ≤ q) hw (a := a)
    have hc1 := abs_cos_le_one (π * (w * ((a : ℝ) / q)))
    have hpos : 0 < 2 * |cos (π * (w * ((a : ℝ) / q)))| := by
      have : 0 < 1 / (q : ℝ) := by positivity
      linarith
    rw [abs_le]; constructor
    · have := Real.log_le_log (by positivity) (show 2 / (q : ℝ) ≤ 2 * |cos (π * (w * ((a : ℝ) / q)))| by
        rw [div_le_iff₀ (by positivity)]; have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2 * q)
        rw [show 2 * (q : ℝ) * (1 / q) = 2 by field_simp] at this; linarith)
      rw [Real.log_div (by norm_num) (by positivity)] at this
      simp only [f]; linarith
    · have := Real.log_le_log hpos (show 2 * |cos (π * (w * ((a : ℝ) / q)))| ≤ 2 by linarith)
      simp only [f]; linarith
  have hlogG : Real.log ‖Gw (WN N) q a ((a : ℝ) / q)‖ = ∑ w ∈ V, f w := by
    unfold Gw
    rw [norm_prod, Real.log_prod]
    · exact sum_congr rfl fun w _ => by rw [norm_one_add_ee]
    · intro w hw
      rw [norm_one_add_ee]
      have h1 := cos_lower (by omega : 1 ≤ q) (mem_filter.mp hw).2 (a := a)
      have h2 : 0 < 1 / (q : ℝ) := by positivity
      exact ne_of_gt (by linarith)
  -- the primes coprime to `q` and the rest
  set P := (range (N + 1)).filter (fun n => n.Prime ∧ n.Coprime q)
  have hPV : P ⊆ V := by
    intro n hn
    simp only [P, mem_filter] at hn
    simp only [V, WN, mem_filter]
    exact ⟨⟨hn.1, Or.inr hn.2.1⟩, not_vanish_coprime h3 ha hn.2.2⟩
  have hrest : V \ P ⊆ insert 1 (range (q + 1) |>.filter (· ∣ q)) := by
    intro n hn
    simp only [V, P, WN, mem_sdiff, mem_filter, mem_range, not_and] at hn
    obtain ⟨⟨⟨hnN, h1p⟩, -⟩, hnP⟩ := hn
    rcases h1p with rfl | hp
    · exact mem_insert_self _ _
    · have hnc : ¬ n.Coprime q := hnP hnN hp
      have hd : n ∣ q := by
        rcases (Nat.coprime_or_dvd_of_prime hp q) with h | h
        · exact absurd h hnc
        · exact h
      exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hq0 hd)), hd⟩)
  have hcard : ((V \ P).card : ℝ) ≤ q + 1 := by
    have h1 := card_le_card hrest
    have h2 := card_insert_le 1 ((range (q + 1)).filter (· ∣ q))
    have h3' := card_filter_le (range (q + 1)) (· ∣ q)
    rw [card_range] at h3'
    have : (V \ P).card ≤ q + 2 := by omega
    -- `1 ∣ q`, so the insert is not new
    have hin : 1 ∈ (range (q + 1)).filter (· ∣ q) := mem_filter.mpr ⟨mem_range.mpr (by omega), one_dvd q⟩
    rw [insert_eq_of_mem hin] at h1
    exact_mod_cast h1.trans h3'
  have hsplitV : ∑ w ∈ V, f w = ∑ w ∈ P, f w + ∑ w ∈ V \ P, f w := by
    rw [← sum_sdiff hPV, add_comm]
  have hRest : |∑ w ∈ V \ P, f w| ≤ (q + 1) * Real.log q := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w ∈ V \ P, |f w| ≤ ∑ _w ∈ V \ P, Real.log q :=
          sum_le_sum fun w hw => hfb w (mem_filter.mp (mem_sdiff.mp hw).1).2
      _ = (V \ P).card * Real.log q := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (q + 1) * Real.log q := mul_le_mul_of_nonneg_right hcard (by linarith)
  -- regroup `P` by classes
  set g : ℕ → ℝ := fun r => Real.log (2 * |cos (π * r * a / q)|)
  have hcopmod : ∀ n, (n % q).Coprime q ↔ n.Coprime q := by
    intro n; rw [Nat.Coprime, Nat.Coprime, ← Nat.gcd_rec q n, Nat.gcd_comm q n]
  have hfp : ∀ p, f p = g (p % q) := by
    intro p
    simp only [f, g]
    have := cos_class (a := a) (p := p) hq0 0
    rw [add_zero, mul_zero, add_zero] at this
    rw [this]; push_cast; ring_nf
  have hPclass : ∑ w ∈ P, f w = ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r := by
    rw [← sum_fiberwise_of_maps_to (g := fun n => n % q) (t := resQ q) (s := P) (fun n hn => by
      simp only [P, mem_filter] at hn
      simp only [resQ, mem_filter, mem_range]; exact ⟨Nat.mod_lt _ hq0, (hcopmod n).mpr hn.2.2⟩)]
    refine sum_congr rfl fun r hr => ?_
    have hrq : r % q = r := Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr).1)
    rw [sum_congr rfl fun p hp => by rw [hfp, (mem_filter.mp hp).2], sum_const, nsmul_eq_mul]
    congr 1
    unfold cntQ; rw [hrq]; norm_cast; congr 1; ext n
    simp only [P, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2, ?_⟩, h3⟩
      rw [← hcopmod n, h3]; exact (mem_filter.mp hr).2
  -- the main term: `Σ_r g(r) = φ(q) c_q` (Lemma 1)
  have hsum : ∑ r ∈ resQ q, g r = (if Even q then Λ (q / 2) else 0) := by
    have h1 := ArcsAlgo.lemma_one q a h3 ha
    have e : resQ q = (range q).filter (q.Coprime ·) := by
      unfold resQ; congr 1; ext r; exact Nat.coprime_comm
    have hne : ∀ r ∈ resQ q, 0 < |cos (π * r * a / q)| := by
      intro r hr
      have := cos_lower (by omega : 1 ≤ q) (not_vanish_coprime h3 ha (mem_filter.mp hr).2) (a := a) (w := r)
      rw [show π * (r * ((a : ℝ) / q)) = π * r * a / q by ring] at this
      have : 0 < 1 / (q : ℝ) := by positivity
      linarith
    have : ∑ r ∈ resQ q, g r = (resQ q).card * Real.log 2 + ∑ r ∈ resQ q, Real.log |cos (π * r * a / q)| := by
      rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
      exact sum_congr rfl fun r hr => Real.log_mul (by norm_num) (hne r hr).ne'
    rw [this, card_resQ, e, h1]; ring
  have hgb : ∀ r ∈ resQ q, |g r| ≤ Real.log q := by
    intro r hr
    have := hfb r (not_vanish_coprime h3 ha (mem_filter.mp hr).2)
    simp only [f] at this; simp only [g]
    rwa [show π * (r * ((a : ℝ) / q)) = π * r * a / q by ring] at this
  have hmain : |∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r - liK 0 N * cq q| ≤ q.totient * E * Real.log q := by
    have e : ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r - liK 0 N * cq q =
        ∑ r ∈ resQ q, ((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r := by
      rw [show ∑ r ∈ resQ q, ((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r =
          ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r - liK 0 N / q.totient * ∑ r ∈ resQ q, g r by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun r _ => by ring, hsum]
      unfold cq; field_simp
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ resQ q, |((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r| ≤ ∑ _r ∈ resQ q, E * Real.log q :=
          sum_le_sum fun r hr => by
            rw [abs_mul]; exact mul_le_mul (hE r hr) (hgb r hr) (abs_nonneg _) (le_trans (abs_nonneg _) (hE r hr))
      _ = q.totient * E * Real.log q := by rw [sum_const, card_resQ, nsmul_eq_mul]; ring
  rw [hlogG, hsplitV, hPclass]
  have := abs_add_le (∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r - liK 0 N * cq q) (∑ w ∈ V \ P, f w)
  rw [show ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r - liK 0 N * cq q + ∑ w ∈ V \ P, f w =
    ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r + ∑ w ∈ V \ P, f w - liK 0 N * cq q by ring] at this
  linarith


theorem card_WN (N : ℕ) (hN : 1 ≤ N) : ((WN N).card : ℝ) = Nat.primeCounting N + 1 := by
  have e : WN N = insert 1 ((range (N + 1)).filter Nat.Prime) := by
    ext w; simp only [WN, mem_filter, mem_insert, mem_range]
    constructor
    · rintro ⟨h1, rfl | h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, Or.inl rfl⟩
      · exact ⟨h1, Or.inr h2⟩
  rw [e, card_insert_of_notMem (by simp [Nat.not_prime_one]), card_primes_eq]; push_cast; ring

/-! ### The Remark (the lobe exponent) -/

/-- For `q ∈ 𝔈`, `q ≥ 3`: `ℓ*_q < c_q` (Lemma P). -/
theorem remark_lobe_lt {q : ℕ} (h3 : 3 ≤ q) (he : emerging q) : ellq q (1 / (2 * q)) < cq q := by
  rcases he with h1 | ⟨hev, hpp⟩
  · omega
  have h4 : 4 ≤ q := by obtain ⟨k, hk⟩ := hev; omega
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨c, hc, hle⟩ := (lemmaP hev h4 hpp).2.2.2.2 (1 / (2 * q)) (by positivity)
  have hs : ellq q (1 / (2 * q)) ≤ c / q.totient := by
    refine csSup_le (Set.Nonempty.image _ ⟨1 / (2 * q), Set.mem_Ici.mpr le_rfl⟩) ?_
    rintro _ ⟨X, hX, rfl⟩
    exact div_le_div_of_nonneg_right (hle X hX) hφ.le
  unfold cq; rw [if_pos hev]
  exact lt_of_le_of_lt hs (div_lt_div_of_pos_right hc hφ)

/-- For `q ∉ 𝔈`, `q ≥ 3`: `c_q = 0 ≤ ℓ_q`. -/
theorem remark_lobe_other {q : ℕ} (h3 : 3 ≤ q) (hne : ¬ emerging q) {X₀ : ℝ} (hX₀ : 0 < X₀) :
    cq q = 0 ∧ 0 ≤ ellq q X₀ := by
  refine ⟨?_, ellq_nonneg (by omega) hX₀⟩
  unfold cq
  split_ifs with hev
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun h => hne (Or.inr ⟨hev, h⟩), zero_div]
  · rw [zero_div]

/-- `X_q` is a first local minimum of `A_q`: a local minimum with none in `(0, X_q)`. -/
def firstLocalMin (q : ℕ) (X : ℝ) : Prop :=
  0 < X ∧ IsLocalMin (Aq q) X ∧ ∀ y ∈ Set.Ioo 0 X, ¬ IsLocalMin (Aq q) y

/-- `A_q` is non-increasing on `(0, X_q]` (it decreases strictly on `(0, 1/(2q))`, Lemma Q(1)), and
`X_q ≥ 1/(2q)`. -/
theorem anti_first_min {q : ℕ} (h3 : 3 ≤ q) {Xq : ℝ} (hX : firstLocalMin q Xq) :
    1 / (2 * q) ≤ Xq ∧ ∀ x y, 0 < x → x ≤ y → y ≤ Xq → Aq q y ≤ Aq q x := by
  obtain ⟨hX0, hmin, hfirst⟩ := hX
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdec := (lemmaQ1_avg h3).2
  have hc := Aq_cont (q := q) (by omega)
  set h := 1 / (2 * (q : ℝ))
  have hh : 0 < h := by positivity
  -- no local minimum in `(0, h)`
  have hnomin : ∀ y ∈ Set.Ioo 0 h, ¬ IsLocalMin (Aq q) y := by
    intro y hy hloc
    obtain ⟨U, hU, hUm⟩ := Filter.eventually_iff_exists_mem.mp hloc
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    set z := min (y + ε / 2) ((y + h) / 2)
    have hyz : y < z := lt_min (by linarith) (by linarith [hy.2])
    have hzh : z < h := lt_of_le_of_lt (min_le_right _ _) (by linarith [hy.2])
    have hzU : z ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (y + ε / 2) ((y + h) / 2); linarith)
    have := hUm z hzU
    have := hdec ⟨hy.1, hy.2⟩ ⟨by linarith [hy.1], hzh⟩ hyz
    linarith
  have hXh : h ≤ Xq := by
    by_contra hlt; push_neg at hlt
    exact hnomin Xq ⟨hX0, hlt⟩ hmin
  refine ⟨hXh, fun x y hx hxy hyX => ?_⟩
  by_contra hgt; push_neg at hgt
  set x0 := min x h / 2
  have hx0 : 0 < x0 := by positivity
  have hx0x : x0 < x := by have := min_le_left x h; simp only [x0]; linarith
  have hx0h : x0 < h := by have := min_le_right x h; simp only [x0]; linarith
  have hx0y : x0 < y := lt_of_lt_of_le hx0x hxy
  have hcont : ContinuousOn (Aq q) (Set.Icc x0 y) := hc.mono fun t ht => lt_of_lt_of_le hx0 ht.1
  obtain ⟨m, hm, hmin'⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hx0y.le) hcont
  -- `m ≠ x0`: `A_q` decreases right after `x0`
  have hm0 : m ≠ x0 := by
    intro hmx
    set x1 := min x h * (3 / 4)
    have hx1 : x0 < x1 := by simp only [x0, x1]; have : 0 < min x h := lt_min hx hh; linarith
    have hx1x : x1 ≤ x := by simp only [x1]; have := min_le_left x h; have : 0 < min x h := lt_min hx hh; linarith
    have hx1h : x1 < h := by simp only [x1]; have := min_le_right x h; have : 0 < min x h := lt_min hx hh; linarith
    have h1 := hdec ⟨hx0, hx0h⟩ ⟨by linarith, hx1h⟩ hx1
    have h2 := hmin' ⟨hx1.le, hx1x.trans hxy⟩
    rw [hmx] at h2
    exact absurd h2 (not_le.mpr h1)
  have hmy : m ≠ y := by
    intro hmy
    have h1 : Aq q m ≤ Aq q x := hmin' ⟨hx0x.le, hxy⟩
    rw [hmy] at h1; linarith
  have hmI : m ∈ Set.Ioo x0 y := ⟨lt_of_le_of_ne hm.1 (Ne.symm hm0), lt_of_le_of_ne hm.2 hmy⟩
  have hloc : IsLocalMin (Aq q) m := hmin'.isLocalMin (Icc_mem_nhds hmI.1 hmI.2)
  exact hfirst m ⟨lt_trans hx0 hmI.1, lt_of_lt_of_le hmI.2 hyX⟩ hloc

/-- **The Remark, first sentence**: `ℓ*_q = max(A_q(1/(2q))/φ(q), ℓ_q)`, `ℓ_q = sup_{X≥X_q} A_q(X)/φ(q)`, for a first
local minimum `X_q` of `A_q`. -/
theorem remark_lobe_max {q : ℕ} (h3 : 3 ≤ q) {Xq : ℝ} (hX : firstLocalMin q Xq) :
    ellq q (1 / (2 * q)) = max (Aq q (1 / (2 * q)) / q.totient) (ellq q Xq) := by
  obtain ⟨hXh, hanti⟩ := anti_first_min h3 hX
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hh : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hq0 : q ≠ 0 := by omega
  apply le_antisymm
  · refine csSup_le (Set.Nonempty.image _ ⟨_, Set.mem_Ici.mpr le_rfl⟩) ?_
    rintro _ ⟨X, hX', rfl⟩
    rcases le_or_gt X Xq with h | h
    · exact le_max_of_le_left (div_le_div_of_nonneg_right (hanti _ _ hh hX' h) hφ.le)
    · exact le_max_of_le_right (le_ellq hq0 (lt_of_lt_of_le hh hXh) h.le)
  · refine max_le (le_ellq hq0 hh le_rfl) ?_
    refine csSup_le (Set.Nonempty.image _ ⟨Xq, Set.mem_Ici.mpr le_rfl⟩) ?_
    rintro _ ⟨X, hX', rfl⟩
    exact le_ellq hq0 hh (hXh.trans hX')


set_option maxHeartbeats 4000000 in
/-- **The Remark, the height of the peak**: `|G(θ*)| = 2^n exp(π(N)(−log 2 + c_q) + o(π(N)))`, uniformly for
`3 ≤ q ≤ 𝔓`, `(a, q) = 1` (Lemma W(3) and Siegel–Walfisz). -/
theorem remark_lobe_height (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 →
        |Real.log ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ -
            ((WN N).card * Real.log 2 + Nat.primeCounting N * (-Real.log 2 + cq q))| ≤
          δ * Nat.primeCounting N := by
  obtain ⟨c, hc, N₁, hW2⟩ := lemmaW2 hSW hB
  obtain ⟨c₀, hc₀, C₀, hC₀, hsw⟩ := hSW B hB
  obtain ⟨N₂, hlow⟩ := pi_lower hSW
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp 2 (by positivity : 0 < 2 * c) (2048 / δ)
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp (2 * B + 1) hc₀ (32 * C₀ / δ)
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp (2 * B + 1) one_pos (64 / δ)
  set Kmax := max (max K₁ K₂) K₃
  refine ⟨N₁ + N₂ + ⌈Real.exp Kmax⌉₊ + 16, fun N hN q a hq hqP ha ts hts hF => ?_⟩
  obtain ⟨hnu, hS2pos, hwin, -, hS2lo⟩ := hW2 N (by omega) q a hq hqP ha
  set Nr : ℝ := (N : ℝ) with hNr
  have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
  have hNpos : 0 < Nr := by linarith
  set L := Real.log Nr with hLdef
  have hKL : Kmax ≤ L := by
    have : Real.exp Kmax ≤ Nr := le_trans (Nat.le_ceil _)
      (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp Kmax⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL1 : K₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKL
  have hL2 : K₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKL
  have hL3 : K₃ ≤ L := le_trans (le_max_right _ _) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqL : (q : ℝ) ≤ L ^ B := hqP
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
  set P := (Nat.primeCounting N : ℝ) with hPdef
  have hPlow : Nr / (2 * L) ≤ P := hlow N (by omega)
  -- the peak: `F(0) ≤ F(t*) ≤ F(0) + 4ν²/S₂`
  have hWN : ∀ w ∈ WN N, w ≤ N := fun w hw => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hw).1)
  obtain ⟨ts', hts'b, -, hmax', hlo', hhi'⟩ :=
    peak (W := WN N) (q := q) (a := a) (by omega) (by omega) hWN hS2pos hwin
  have htsw : |ts| < π / (q * Nr) := lt_of_le_of_lt hts hwin
  have hts'w : |ts'| < π / (q * Nr) := lt_of_le_of_lt hts'b hwin
  have heq : ts = ts' := by
    by_contra hne
    have h1 := hmax' ts htsw hne
    have h2 := Fw_quad (W := WN N) (q := q) (a := a) (by omega) (by omega) hWN htsw hF hts'w
    have : 0 ≤ S2W (WN N) q a / 8 * (ts' - ts) ^ 2 := by positivity
    linarith
  rw [← heq] at hlo' hhi'
  have hlog : ∀ t, |t| < π / (q * Nr) →
      Real.log ‖Gw (WN N) q a ((a : ℝ) / q + t / (2 * π))‖ = Fw (WN N) q a t :=
    fun t ht => log_Gw (W := WN N) (by omega) (by omega) hWN ht
  have h0 : Real.log ‖Gw (WN N) q a ((a : ℝ) / q)‖ = Fw (WN N) q a 0 := by
    have := hlog 0 (by rw [abs_zero]; positivity); simpa using this
  rw [hlog ts htsw]
  -- the centre
  set E := C₀ * Nr * Real.exp (-c₀ * √L) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hEr : ∀ r ∈ resQ q, |(cntQ N q r : ℝ) - liK 0 N / q.totient| ≤ E := fun r hr =>
    hsw N (by omega) q r (by omega) hqP (mem_filter.mp hr).2
  have hc := log_Gw_centre hq ha N hEr
  rw [h0] at hc
  have hli : |P - liK 0 N| ≤ E := by
    have := hsw N (by omega) 1 0 le_rfl
      (by rw [← hNr]; push_cast; exact Real.one_le_rpow hLone hB.le) (Nat.coprime_zero_left 1 |>.mpr rfl)
    rw [cnt_one, card_primes_eq, Nat.totient_one, Nat.cast_one, div_one] at this
    exact this
  have hn := card_WN N (by omega)
  -- sizes
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hlq : Real.log q ≤ L ^ B := le_trans (Real.log_le_sub_one_of_pos hq0) (by linarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcq : |cq q| ≤ L ^ B := by
    have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    unfold cq
    split_ifs
    · rw [abs_div, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_pos (by linarith)]
      have h1 : Λ (q / 2) ≤ Real.log q := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
        · have : 1 ≤ q / 2 := by omega
          exact_mod_cast (by omega : 0 < q / 2)
        · exact_mod_cast Nat.div_le_self q 2
      rw [div_le_iff₀ (by linarith)]; nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := q / 2)]
    · simp; positivity
  have hsplit : |Fw (WN N) q a ts - ((WN N).card * Real.log 2 + P * (-Real.log 2 + cq q))| ≤
      4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a + (q.totient * E * Real.log q + (q + 1) * Real.log q) +
        E * L ^ B + Real.log 2 := by
    rw [hn]
    have e : Fw (WN N) q a ts - ((P + 1) * Real.log 2 + P * (-Real.log 2 + cq q)) =
        (Fw (WN N) q a ts - Fw (WN N) q a 0) + (Fw (WN N) q a 0 - liK 0 N * cq q) +
          (liK 0 N - P) * cq q - Real.log 2 := by ring
    rw [e]
    have a1 : |Fw (WN N) q a ts - Fw (WN N) q a 0| ≤ 4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a := by
      rw [abs_le]; constructor <;> linarith
    have a3 : |(liK 0 N - P) * cq q| ≤ E * L ^ B := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul hli hcq (abs_nonneg _) hE0
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc _ ≤ |Fw (WN N) q a ts - Fw (WN N) q a 0| + |Fw (WN N) q a 0 - liK 0 N * cq q| +
          |(liK 0 N - P) * cq q| + |Real.log 2| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ _ := by rw [abs_of_pos hl2]; linarith
  refine hsplit.trans ?_
  -- each term is `≤ δπ(N)/4`, via `π(N) ≥ N/(2L)`
  have hu : δ * Nr / (8 * L) ≤ δ / 4 * P := by
    have : Nr / (2 * L) * (δ / 4) = δ * Nr / (8 * L) := by field_simp; ring
    nlinarith
  have he := Real.exp_pos (-c₀ * √L)
  have he' : Real.exp (c₀ * √L) * Real.exp (-c₀ * √L) = 1 := by rw [← Real.exp_add]; simp
  have hpow : L ^ (2 * B + 1) = L ^ B * L ^ B * L := by
    rw [Real.rpow_add_one hL0.ne', two_mul, Real.rpow_add hL0]
  have t1 : 4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a ≤ δ * Nr / (8 * L) := by
    have hnu2 : nuW (WN N) q a ^ 2 ≤ (Nr ^ 2 * Real.exp (-c * √L)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hnu 2
    have hS : Nr ^ 3 / (64 * L) ≤ S2W (WN N) q a := hS2lo
    rw [div_le_iff₀ hS2pos]
    have h1 := hk1 L hL1
    have hL2' : L ^ (2 : ℝ) = L ^ 2 := by norm_cast
    rw [hL2'] at h1
    have hx : Real.exp (-c * √L) ^ 2 * Real.exp (2 * c * √L) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; simp
    have hx0 : 0 ≤ Real.exp (-c * √L) ^ 2 := by positivity
    -- `4ν² ≤ 4N⁴e^{−2c√L} ≤ δN/(8L)·N³/(64L)`
    have key : 4 * (Nr ^ 2 * Real.exp (-c * √L)) ^ 2 ≤ δ * Nr / (8 * L) * (Nr ^ 3 / (64 * L)) := by
      have : 2048 / δ * L ^ 2 * Real.exp (-c * √L) ^ 2 ≤ 1 := by
        calc 2048 / δ * L ^ 2 * Real.exp (-c * √L) ^ 2 ≤ Real.exp (2 * c * √L) * Real.exp (-c * √L) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 hx0
          _ = 1 := by rw [mul_comm]; exact hx
      have e1 : δ * Nr / (8 * L) * (Nr ^ 3 / (64 * L)) = δ * Nr ^ 4 / (512 * L ^ 2) := by field_simp; ring
      rw [e1, le_div_iff₀ (by positivity)]
      have e2 : 4 * (Nr ^ 2 * Real.exp (-c * √L)) ^ 2 * (512 * L ^ 2) =
          δ * Nr ^ 4 * (2048 / δ * L ^ 2 * Real.exp (-c * √L) ^ 2) := by field_simp; ring
      rw [e2]
      have : 0 ≤ δ * Nr ^ 4 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ δ * Nr / (8 * L))
    nlinarith
  have t2 : q.totient * E * Real.log q + E * L ^ B ≤ δ * Nr / (8 * L) := by
    have hφl : (q.totient : ℝ) * Real.log q ≤ L ^ B * L ^ B :=
      mul_le_mul (le_trans hφq hqL) hlq hlq0 (by positivity)
    have hs : (q.totient : ℝ) * E * Real.log q + E * L ^ B ≤ 2 * E * (L ^ B * L ^ B) := by
      have e : (q.totient : ℝ) * E * Real.log q = E * ((q.totient : ℝ) * Real.log q) := by ring
      rw [e]; nlinarith [mul_le_mul_of_nonneg_left hφl hE0, mul_le_mul_of_nonneg_left hLB1 hE0]
    refine hs.trans ?_
    have h2 := hk2 L hL2; rw [hpow] at h2
    rw [hEdef, le_div_iff₀ (by positivity)]
    have e : 2 * (C₀ * Nr * Real.exp (-c₀ * √L)) * (L ^ B * L ^ B) * (8 * L) =
        δ * Nr * Real.exp (-c₀ * √L) * (16 * C₀ / δ * (L ^ B * L ^ B * L)) := by field_simp; ring
    rw [e]
    have : δ * Nr * Real.exp (-c₀ * √L) * (16 * C₀ / δ * (L ^ B * L ^ B * L)) ≤
        δ * Nr * Real.exp (-c₀ * √L) * Real.exp (c₀ * √L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 16 * C₀ / δ * (L ^ B * L ^ B * L) ≤ 32 * C₀ / δ * (L ^ B * L ^ B * L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ hδ.le; linarith
      linarith
    have e2 : δ * Nr * Real.exp (-c₀ * √L) * Real.exp (c₀ * √L) = δ * Nr := by
      rw [mul_assoc, mul_comm (Real.exp (-c₀ * √L)), he', mul_one]
    linarith
  have t3 : (q + 1) * Real.log q + Real.log 2 ≤ δ * Nr / (8 * L) := by
    have hl2 : Real.log 2 ≤ L ^ B := le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by linarith)
    have hs : (q + 1) * Real.log q + Real.log 2 ≤ 4 * (L ^ B * L ^ B) := by nlinarith
    refine hs.trans ?_
    have h3 := hk3 L hL3; rw [hpow] at h3
    have hN : Real.exp (1 * √L) ≤ Nr := by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith)
    rw [le_div_iff₀ (by positivity)]
    have : 64 / δ * (L ^ B * L ^ B * L) ≤ Nr := h3.trans hN
    have e : 4 * (L ^ B * L ^ B) * (8 * L) = δ / 2 * (64 / δ * (L ^ B * L ^ B * L)) := by field_simp; ring
    rw [e]; nlinarith
  linarith


/-- **The Remark, the conclusion**: for each fixed `q ∈ 𝔈`, with `γ = (c_q − ℓ*_q)/4 > 0` (Lemma P), the lobe
error of Theorem E(2) taken with `δ = γ` is `≤ e^{−γπ(N)}|G(θ*)|` for `N ≥ N₀`: exponentially smaller than the
peak. (`γ` depends on `q`; Lemma P gives no lower bound for `c_q − ℓ*_q` uniform in `q`.) -/
theorem remark_lobe_gap (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {q : ℕ} (h3 : 3 ≤ q) (he : emerging q) :
    0 < (cq q - ellq q (1 / (2 * q))) / 4 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (q : ℝ) ≤ PP B N → ∀ a : ℕ, a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 →
        2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) +
            (cq q - ellq q (1 / (2 * q))) / 4) * Nat.primeCounting N)) ≤
          Real.exp (-((cq q - ellq q (1 / (2 * q))) / 4) * Nat.primeCounting N) *
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ := by
  set γ := (cq q - ellq q (1 / (2 * q))) / 4 with hγ
  have hγ0 : 0 < γ := by have := remark_lobe_lt h3 he; rw [hγ]; linarith
  refine ⟨hγ0, ?_⟩
  obtain ⟨N₁, hH⟩ := remark_lobe_height hSW hB hγ0
  obtain ⟨c, hc, N₂, hW2⟩ := lemmaW2 hSW hB
  obtain ⟨N₃, hlow⟩ := pi_lower hSW
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp 1 one_pos (2 * Real.log 2 / γ)
  refine ⟨N₁ + N₂ + N₃ + ⌈Real.exp K₁⌉₊ + 16, fun N hN hqP a ha ts hts hF => ?_⟩
  have hh := hH N (by omega) q a h3 hqP ha ts hts hF
  obtain ⟨-, -, hwin, -, -⟩ := hW2 N (by omega) q a h3 hqP ha
  have hG := Gw_pos (q := q) (a := a) (N := N) (by omega) (by omega) (lt_of_le_of_lt hts hwin)
  set G := ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖
  set P := (Nat.primeCounting N : ℝ)
  set n := ((WN N).card : ℝ)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `γπ(N) ≥ log 2`
  have hP : Real.log 2 ≤ γ * P := by
    set Nr : ℝ := (N : ℝ) with hNr
    have hN16 : (16 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 16 ≤ N)
    have hNpos : 0 < Nr := by linarith
    set L := Real.log Nr with hLdef
    have hKL : K₁ ≤ L := by
      have : Real.exp K₁ ≤ Nr := le_trans (Nat.le_ceil _)
        (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp K₁⌉₊ ≤ N))
      rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
    have hL0 : 0 < L := by linarith
    have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h1 := hk1 L hKL; rw [Real.rpow_one, one_mul] at h1
    have h2 : 2 * Real.log 2 / γ * L ≤ Nr := h1.trans (by
      rw [← Real.exp_log hNpos]; exact Real.exp_le_exp.mpr (by linarith))
    have hlowN : Nr / (2 * L) ≤ P := hlow N (by omega)
    have h3' : Real.log 2 / γ ≤ Nr / (2 * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * Real.log 2 / γ * L = Real.log 2 / γ * (2 * L) := by ring
      linarith
    have := le_trans h3' hlowN
    rw [div_le_iff₀ hγ0] at this; linarith
  have hlo : n * Real.log 2 + P * (-Real.log 2 + cq q) - γ * P ≤ Real.log G := by
    have := (abs_le.mp hh).1; linarith
  have hGe : Real.exp (n * Real.log 2 + P * (-Real.log 2 + cq q) - γ * P) ≤ G := by
    rw [← Real.exp_log hG]; exact Real.exp_le_exp.mpr hlo
  have h2n : (2 : ℝ) ^ (WN N).card = Real.exp (n * Real.log 2) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; simp [n]
  rw [h2n]
  have hc : cq q = ellq q (1 / (2 * q)) + 4 * γ := by rw [hγ]; ring
  calc 2 * (Real.exp (n * Real.log 2) * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + γ) * P))
      = Real.exp (Real.log 2 + n * Real.log 2 + (-Real.log 2 + ellq q (1 / (2 * q)) + γ) * P) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]; ring
    _ ≤ Real.exp (-γ * P) * Real.exp (n * Real.log 2 + P * (-Real.log 2 + cq q) - γ * P) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [hc]; nlinarith
    _ ≤ Real.exp (-γ * P) * G := mul_le_mul_of_nonneg_left hGe (Real.exp_pos _).le

/-- **Theorem E (3): `ℓ*_q = ℓ_q` off the emerging moduli.** For `q ≥ 3`, `q ∉ 𝔈` and a first local
minimum `X_q` of `A_q`, the lobe exponent of Theorem E(3), `ℓ*_q = sup_{X ≥ 1/(2q)} A_q(X)/φ(q)`,
equals `ℓ_q = sup_{X ≥ X_q} A_q(X)/φ(q)`: here `A_q(1/(2q)) ≤ h_q(0) = 0` and `ℓ_q ≥ 0`. -/
theorem ellE_eq_ellq {q : ℕ} (h3 : 3 ≤ q) (hne : ¬ emerging q) {Xq : ℝ} (hX : firstLocalMin q Xq) :
    ellq q (1 / (2 * q)) = ellq q Xq := by
  have hq0 : 0 < q := by omega
  rw [← ellE_eq hq0]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hpos : 0 ≤ ellq q Xq := ellq_nonneg hq0 hX.1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hh : (0 : ℝ) < 1 / (2 * q) := by positivity
  -- `A_q(1/(2q)) ≤ 0`, by continuity from `A_q < h_q(0) = 0` on `(0, 1/(2q))`
  have hA : Aq q (1 / (2 * q)) ≤ 0 := by
    have hlt := (lemmaQ1_avg h3).1
    rw [hq_zero h3 hne] at hlt
    have hc : ContinuousWithinAt (Aq q) (Set.Ioo 0 (1 / (2 * q))) (1 / (2 * q)) :=
      ((Aq_cont hq0).continuousAt (Ioi_mem_nhds hh)).continuousWithinAt
    have hcl : (1 / (2 * (q : ℝ))) ∈ closure (Set.Ioo 0 (1 / (2 * (q : ℝ)))) := by
      rw [closure_Ioo hh.ne]; exact ⟨hh.le, le_rfl⟩
    exact ContinuousWithinAt.closure_le hcl hc continuousWithinAt_const fun y hy => (hlt y hy).le
  have hA' : Aq q (1 / (2 * q)) / q.totient ≤ ellq q Xq :=
    (div_nonpos_of_nonpos_of_nonneg hA hφ.le).trans hpos
  unfold ellE
  rw [remark_lobe_max h3 hX, max_eq_right hA', max_eq_right hpos]

end ArcsAlgo.Core
