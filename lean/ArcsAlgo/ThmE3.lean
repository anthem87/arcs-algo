module

public import ArcsAlgo.LemmaL
public import ArcsAlgo.CorQprime
public import ArcsAlgo.ArcLevels
public import ArcsAlgo.PrimeCount
set_option autoImplicit false

/-!
# Theorem E(3): the arcs of non-emerging moduli (paper §3.5)

* `PP`, `Rarc`: `𝔓 = (log N)^B` and `R_{a/q}(T) = ∫_{|θ − a/q| ≤ 𝔓/(qN)} F_N(e(θ)) e(−Tθ) dθ`.
* `ellE q = max(0, sup_{X ≥ 1/(2q)} A_q(X)/φ(q))`: the lobe exponent. Since `X_q ≥ 1/(2q)`
  (Lemma Q(1)) and `A_q` is non-increasing on `[0, X_q]`, this is the paper's `ℓ_q`
  (`ℓ_q ≥ 0 = c_q`); the supremum from `1/(2q)` is also the quantity certified in Corollary Q′.
* `hq_le`, `Aq_le_log2`, `ellq_le_log2`: `A_q(X)/φ(q) ≤ log 2`.
* `hq_zero`, `Aq_le_ellE`: for `q ∉ 𝔈`, `h_q(0) = 0` and `A_q(X)/φ(q) ≤ ellE q` for `X > 0`.
* `not_vanish_ne`, `Fstar_eq`: for `q ∉ 𝔈` no weight vanishes at `a/q`.
* `FW_centre_le`: `|F_N(e(a/q))| ≤ 2^n exp(−li(N) log 2 + φ(q) E log q)` when every class count is
  within `E` of `li(N)/φ(q)` (Lemma 1 for the main term).
* `thmE3`: for every `δ > 0` and `N ≥ N₀`, uniformly for `3 ≤ q ≤ 𝔓`, `(a, q) = 1`, `q ∉ 𝔈` and all
  `T`: `|R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ_q + δ)π(N))`. Core `|X| < N^{−1/2}` by Lemma L₀ and
  Siegel–Walfisz, lobes by Lemma L.

Proved for every `B > 0` (in particular for the paper's `B > 40`). The only hypothesis is
`SiegelWalfisz`.
-/

open Finset Real Polynomial

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-- `𝔓 = (log N)^B`. -/
noncomputable def PP (B : ℝ) (N : ℕ) : ℝ := Real.log N ^ B

/-- `R_{a/q}(T) = ∫_{𝔐(a/q)} F_N(e(θ)) e(−Tθ) dθ`, `𝔐(a/q) = {|θ − a/q| ≤ 𝔓/(qN)}`. -/
noncomputable def Rarc (B : ℝ) (N q a : ℕ) (T : ℝ) : ℂ :=
  ∫ θ in ((a : ℝ) / q - PP B N / (q * N))..((a : ℝ) / q + PP B N / (q * N)), FW (WN N) θ * ee (-(T * θ))

/-- The lobe exponent `max(0, sup_{X ≥ 1/(2q)} A_q(X)/φ(q))`. -/
noncomputable def ellE (q : ℕ) : ℝ := max 0 (ellq q (1 / (2 * q)))

/-- `h_q ≤ φ(q) log 2`: each factor `|e(x) + ν|` is `≤ 2`. -/
theorem hq_le {q : ℕ} (hq0 : q ≠ 0) (x : ℝ) : hq q x ≤ q.totient * Real.log 2 := by
  unfold hq
  rw [norm_cyc_neg_prod q hq0]
  have hb : ∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν‖ ≤ 2 ^ q.totient := by
    calc ∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν‖ ≤ ∏ _ν ∈ primitiveRoots q ℂ, (2 : ℝ) :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun ν hν => by
            have h1 : ‖ν‖ = 1 := ((mem_primitiveRoots (Nat.pos_of_ne_zero hq0)).mp hν).norm'_eq_one hq0
            calc ‖ee x + ν‖ ≤ ‖ee x‖ + ‖ν‖ := norm_add_le _ _
              _ = 2 := by rw [norm_ee, h1]; norm_num
      _ = 2 ^ q.totient := by rw [prod_const, Complex.card_primitiveRoots]
  rcases eq_or_lt_of_le (prod_nonneg fun ν _ => norm_nonneg (ee x + ν) :
      (0 : ℝ) ≤ ∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν‖) with h | h
  · rw [← h, Real.log_zero]; positivity
  · calc Real.log (∏ ν ∈ primitiveRoots q ℂ, ‖ee x + ν‖) ≤ Real.log (2 ^ q.totient) := Real.log_le_log h hb
      _ = q.totient * Real.log 2 := by rw [Real.log_pow]

theorem Aq_le_log2 {q : ℕ} (hq0 : q ≠ 0) {X : ℝ} (hX : 0 < X) : Aq q X ≤ q.totient * Real.log 2 := by
  unfold Aq
  rw [div_le_iff₀ hX]
  by_cases hi : IntervalIntegrable (hq q) MeasureTheory.volume 0 X
  · have := intervalIntegral.integral_mono_on hX.le hi
      (intervalIntegrable_const (c := (q.totient : ℝ) * Real.log 2)) fun x _ => hq_le hq0 x
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this; linarith
  · rw [intervalIntegral.integral_undef hi]; have := log_two_pos'; positivity

theorem ellq_bdd {q : ℕ} (hq0 : q ≠ 0) {X₀ : ℝ} (hX₀ : 0 < X₀) :
    BddAbove ((fun X => Aq q X / q.totient) '' Set.Ici X₀) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  refine ⟨Real.log 2, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  rw [div_le_iff₀ hφ]
  have := Aq_le_log2 hq0 (lt_of_lt_of_le hX₀ hX); linarith

theorem le_ellq {q : ℕ} (hq0 : q ≠ 0) {X₀ X : ℝ} (hX₀ : 0 < X₀) (hX : X₀ ≤ X) :
    Aq q X / q.totient ≤ ellq q X₀ :=
  le_csSup (ellq_bdd hq0 hX₀) ⟨X, Set.mem_Ici.mpr hX, rfl⟩

theorem ellq_le_log2 {q : ℕ} (hq0 : q ≠ 0) {X₀ : ℝ} (hX₀ : 0 < X₀) : ellq q X₀ ≤ Real.log 2 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  refine csSup_le (Set.Nonempty.image _ ⟨X₀, Set.mem_Ici.mpr le_rfl⟩) ?_
  rintro _ ⟨X, hX, rfl⟩
  rw [div_le_iff₀ hφ]
  have := Aq_le_log2 hq0 (lt_of_lt_of_le hX₀ hX); linarith

theorem ellE_le_log2 {q : ℕ} (hq0 : q ≠ 0) : ellE q ≤ Real.log 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  exact max_le log_two_pos'.le (ellq_le_log2 hq0 (by positivity))

/-- For `q ∉ 𝔈`, `q ≥ 3`: `h_q(0) = log|Φ_q(−1)| = 0`. -/
theorem hq_zero {q : ℕ} (h3 : 3 ≤ q) (hne : ¬ emerging q) : hq q 0 = 0 := by
  unfold hq
  rw [norm_cyc_neg_prod q (by omega)]
  have e1 : ee 0 = 1 := by unfold ee; simp
  rw [e1, ← norm_prod, ArcsAlgo.prod_one_add_primitiveRoots q h3]
  split_ifs with he
  · have : ¬ IsPrimePow (q / 2) := fun h => hne (Or.inr ⟨he, h⟩)
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr this, Real.exp_zero, Real.log_one]
  · simp

/-- For `q ∉ 𝔈`, `q ≥ 3` and `X > 0`: `A_q(X)/φ(q) ≤ max(0, sup_{X ≥ 1/(2q)} A_q/φ(q))`. -/
theorem Aq_le_ellE {q : ℕ} (h3 : 3 ≤ q) (hne : ¬ emerging q) {X : ℝ} (hX : 0 < X) :
    Aq q X / q.totient ≤ ellE q := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rcases lt_or_ge X (1 / (2 * q)) with h | h
  · have := (lemmaQ1_avg h3).1 X ⟨hX, h⟩
    rw [hq_zero h3 hne] at this
    exact le_trans (div_nonpos_of_nonpos_of_nonneg this.le hφ.le) (le_max_left _ _)
  · exact le_trans (le_ellq (by omega) (by positivity) h) (le_max_right _ _)

/-- For `q ∉ 𝔈`, `q ≥ 3`, `(a, q) = 1`: no weight of `W_N` vanishes at `a/q`. -/
theorem not_vanish_ne {q a : ℕ} (h3 : 3 ≤ q) (ha : a.Coprime q) (hne : ¬ emerging q) {N w : ℕ}
    (hw : w ∈ WN N) : ¬ vanish q a w := by
  intro hv
  have hw' : w = 1 ∨ w.Prime := (mem_filter.mp hw).2
  have h2 := vanish_eq h3 ha hw' hv
  rcases hw' with rfl | hp
  · omega
  · apply hne; right
    refine ⟨⟨w, by omega⟩, ?_⟩
    rw [show q / 2 = w by omega]; exact hp.isPrimePow

theorem Fstar_eq {q a : ℕ} (h3 : 3 ≤ q) (ha : a.Coprime q) (hne : ¬ emerging q) (N : ℕ) :
    Fstar (WN N) q a = FW (WN N) ((a : ℝ) / q) := by
  unfold Fstar FW
  rw [filter_true_of_mem fun w hw => not_vanish_ne h3 ha hne hw]

/-- **The centre of a non-emerging arc**: if `|π(N;q,r) − li(N)/φ(q)| ≤ E` for every `(r, q) = 1`, then
`|F_N(e(a/q))| ≤ 2^n exp(−li(N) log 2 + φ(q) E log q)`. -/
theorem FW_centre_le {q a : ℕ} (h3 : 3 ≤ q) (ha : a.Coprime q) (hne : ¬ emerging q) (N : ℕ) {E : ℝ}
    (hE : ∀ r ∈ resQ q, |(cntQ N q r : ℝ) - liK 0 N / q.totient| ≤ E) :
    ‖FW (WN N) ((a : ℝ) / q)‖ ≤
      2 ^ (WN N).card * Real.exp (-(liK 0 N) * Real.log 2 + q.totient * E * Real.log q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hR := FN_reduce (a := a) h3 0 N 0 (ε := 1 / q) (by positivity)
  rw [add_zero] at hR
  refine hR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  set g : ℕ → ℝ := fun r => Real.log |cos (π * r * a / q)|
  have hl : ∀ r ∈ resQ q, 1 / (q : ℝ) ≤ |cos (π * r * a / q)| := by
    intro r hr
    have := cos_lower (by omega : 1 ≤ q) (not_vanish_coprime h3 ha (mem_filter.mp hr).2) (a := a) (w := r)
    rwa [show π * (r * ((a : ℝ) / q)) = π * r * a / q by ring] at this
  have hG : ∀ r ∈ resQ q, ∀ p : ℕ, Gq q a r 0 (1 / q) p = g r := by
    intro r hr p
    unfold Gq
    rw [show π * (((r * a : ℕ) : ℝ) / q + p * 0) = π * r * a / q by push_cast; ring, max_eq_left (hl r hr)]
  have hcard : ∀ r ∈ resQ q, ((Ioc 0 N).filter (fun n => n.Prime ∧ n % q = r)).card = cntQ N q r := by
    intro r hr
    have hrq : r % q = r := Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr).1)
    unfold cntQ; rw [hrq]; congr 1; ext n
    simp only [mem_filter, mem_Ioc, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, hp, h3⟩; exact ⟨by omega, hp, h3⟩
    · rintro ⟨h1, hp, h3⟩; exact ⟨⟨hp.pos, by omega⟩, hp, h3⟩
  rw [sum_congr rfl fun r hr => by
    rw [sum_congr rfl fun p _ => hG r hr p, sum_const, hcard r hr, nsmul_eq_mul]]
  have hsum : ∑ r ∈ resQ q, g r = -(q.totient : ℝ) * Real.log 2 := by
    have h1 := ArcsAlgo.lemma_one q a h3 ha
    have hΛ : (if Even q then ArithmeticFunction.vonMangoldt (q / 2) else 0) = 0 := by
      split_ifs with he
      · exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun h => hne (Or.inr ⟨he, h⟩)
      · rfl
    rw [hΛ, add_zero] at h1
    have e : resQ q = (range q).filter (q.Coprime ·) := by
      unfold resQ; congr 1; ext r; exact Nat.coprime_comm
    rw [e]; exact h1
  have hg0 : ∀ r ∈ resQ q, g r ≤ 0 := fun r _ => Real.log_nonpos (abs_nonneg _) (abs_cos_le_one _)
  have hg1 : ∀ r ∈ resQ q, -Real.log q ≤ g r := by
    intro r hr
    have := Real.log_le_log (by positivity) (hl r hr)
    rwa [one_div, Real.log_inv] at this
  have hterm : ∀ r ∈ resQ q, (cntQ N q r : ℝ) * g r ≤ liK 0 N / q.totient * g r + E * Real.log q := by
    intro r hr
    have h1 := hE r hr
    have h2 : |g r| ≤ Real.log q := by rw [abs_le]; constructor <;> linarith [hg0 r hr, hg1 r hr]
    have h3 : ((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r ≤ E * Real.log q := by
      calc ((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r
          ≤ |((cntQ N q r : ℝ) - liK 0 N / q.totient) * g r| := le_abs_self _
        _ = |(cntQ N q r : ℝ) - liK 0 N / q.totient| * |g r| := abs_mul _ _
        _ ≤ E * Real.log q := mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
    linarith
  calc ∑ r ∈ resQ q, (cntQ N q r : ℝ) * g r
      ≤ ∑ r ∈ resQ q, (liK 0 N / q.totient * g r + E * Real.log q) := sum_le_sum hterm
    _ = liK 0 N / q.totient * ∑ r ∈ resQ q, g r + q.totient * E * Real.log q := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_resQ, nsmul_eq_mul]; ring
    _ = -(liK 0 N) * Real.log 2 + q.totient * E * Real.log q := by
        rw [hsum]; field_simp

set_option maxHeartbeats 8000000 in
/-- **Theorem E(3) (other arcs)** (paper §3.5): fix `B > 0` and `δ > 0`. For `N ≥ N₀`, `3 ≤ q ≤ 𝔓`,
`(a, q) = 1`, `q ∉ 𝔈` and every `T`: `|R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ_q + δ)π(N))`, `n = |W_N|`,
with `ℓ_q = ellE q`. This is the paper's `o(1)`, uniform in `q`, `a`, `T`. The only hypothesis is
Siegel–Walfisz. -/
theorem thmE3 (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q → ¬ emerging q →
      ∀ T : ℝ, ‖Rarc B N q a T‖ ≤
        2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellE q + δ) * Nat.primeCounting N) := by
  have hl2 := log_two_pos'
  obtain ⟨N₁, hLL⟩ := lemmaL hSW hB
  obtain ⟨c, hc, C, hC, hsw⟩ := hSW B hB
  obtain ⟨N₂, hlow⟩ := pi_lower hSW
  obtain ⟨N₃, hup⟩ := pi_upper hSW (δ := δ / (8 * Real.log 2)) (by positivity)
  obtain ⟨K₁, hK₁, hk1⟩ := ev_poly_exp (2 * B + 1) hc (16 * C / δ)
  obtain ⟨K₂, hK₂, hk2⟩ := ev_poly_exp 1 one_pos (8 * Real.log 2 / δ)
  obtain ⟨K₃, hK₃, hk3⟩ := ev_poly_exp B (by norm_num : (0 : ℝ) < 1 / 2) (4 * π / δ)
  obtain ⟨K₄, hK₄, hk4⟩ := ev_poly_exp B one_pos 1
  set K := max (max K₁ K₂) (max (max K₃ K₄) (24 / δ))
  refine ⟨N₁ + N₂ + N₃ + ⌈Real.exp K⌉₊ + 16, fun N hN q a hq hqP ha hne T => ?_⟩
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
  have hL3 : K₃ ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL4 : K₄ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hKL
  have hL5 : 24 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKL
  have hLone : 1 ≤ L := le_trans hK₁ hL1
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hsqL : √L ≤ L := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set P := (Nat.primeCounting N : ℝ) with hPdef
  have hPlow : Nr / (2 * L) ≤ P := hlow N (by omega)
  have hPup : P ≤ (1 + δ / (8 * Real.log 2)) * Nr / L := hup N (by omega)
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPlow
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set ℓ := ellE q with hℓdef
  have hℓ0 : 0 ≤ ℓ := le_max_left _ _
  have hℓ2 : ℓ ≤ Real.log 2 := ellE_le_log2 (by omega)
  set n := (WN N).card
  have hLB : (q : ℝ) ≤ L ^ B := hqP
  have hPN : L ^ B ≤ Nr := by
    have := hk4 L hL4; rw [one_mul] at this
    exact this.trans (by rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
  set u := Nr / L with hu
  have hu2 : u ≤ 2 * P := by
    have : Nr / (2 * L) = u / 2 := by rw [hu]; field_simp
    linarith
  have hu0 : 0 ≤ u := by positivity
  -- the pointwise bound
  have hpt : ∀ θ : ℝ, |θ - a / q| ≤ PP B N / (q * N) →
      ‖FW (WN N) θ‖ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓ + δ) * P) := by
    intro θ hθ
    set X := Nr * (θ - a / q) with hX
    have hθX : θ = a / q + X / Nr := by rw [hX]; field_simp; ring
    have hXle : |X| ≤ L ^ B / q := by
      rw [hX, abs_mul, abs_of_pos hNpos]
      have := mul_le_mul_of_nonneg_left hθ hNpos.le
      have e : Nr * (PP B N / (q * N)) = L ^ B / q := by unfold PP; rw [← hNr, ← hLdef]; field_simp
      linarith
    rcases le_or_gt (Nr ^ (-(1 / 2 : ℝ))) |X| with hXlo | hXlo
    · -- lobes: Lemma L
      have h1 := hLL N (by omega) q a hq hqP ha X hXlo hXle
      rw [hθX]
      refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
      have hX0 : 0 < |X| := lt_of_lt_of_le (by positivity) hXlo
      have hA := Aq_le_ellE hq hne hX0
      have s1 : Nr / L * (Aq q |X| / q.totient - Real.log 2) ≤ u * (ℓ - Real.log 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hu0
      set D := Real.log 2 - ℓ
      have hD0 : 0 ≤ D := by linarith
      have hPup' : P ≤ u + δ / (8 * Real.log 2) * u := by
        have : (1 + δ / (8 * Real.log 2)) * Nr / L = u + δ / (8 * Real.log 2) * u := by rw [hu]; ring
        linarith
      have s2 : D * P ≤ D * u + D * (δ / (8 * Real.log 2) * u) := by
        have := mul_le_mul_of_nonneg_left hPup' hD0; linarith
      have s3 : D * (δ / (8 * Real.log 2) * u) ≤ δ / 4 * P := by
        have h1 : D * (δ / (8 * Real.log 2) * u) ≤ Real.log 2 * (δ / (8 * Real.log 2) * u) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h2 : Real.log 2 * (δ / (8 * Real.log 2) * u) = δ / 8 * u := by field_simp
        nlinarith
      have s4 : 3 * Nr / L ^ 2 ≤ δ / 4 * P := by
        have e : 3 * Nr / L ^ 2 = 3 / L * u := by rw [hu]; field_simp
        have h6 : 3 / L ≤ δ / 8 := by
          rw [div_le_iff₀ hL0]; rw [div_le_iff₀ hδ] at hL5; nlinarith
        rw [e]
        have := mul_le_mul_of_nonneg_right h6 hu0
        nlinarith
      have e : u * (ℓ - Real.log 2) = -(D * u) := by simp only [D]; ring
      nlinarith
    · -- core: Lemma L₀ and the centre
      have hβ : |X / Nr| ≤ Nr ^ (-(3 / 2 : ℝ)) := by
        rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
        have e : Nr ^ (-(3 / 2 : ℝ)) * Nr = Nr ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add_one hNpos.ne']; norm_num
        rw [e]; exact hXlo.le
      have h0 := lemmaL0 hq ha (by omega : 3 ≤ N) hβ
      rw [Fstar_eq hq ha hne] at h0
      set E := C * Nr * Real.exp (-c * √L) with hEdef
      have hE0 : 0 ≤ E := by positivity
      have hEr : ∀ r ∈ resQ q, |(cntQ N q r : ℝ) - liK 0 N / q.totient| ≤ E := fun r hr =>
        hsw N (by omega) q r (by omega) hqP (mem_filter.mp hr).2
      have hc0 := FW_centre_le hq ha hne N hEr
      have hli : P - E ≤ liK 0 N := by
        have := hsw N (by omega) 1 0 le_rfl
          (by rw [← hNr]; push_cast; exact Real.one_le_rpow hLone hB.le) (Nat.coprime_zero_left 1 |>.mpr rfl)
        rw [cnt_one, card_primes_eq, Nat.totient_one, Nat.cast_one, div_one] at this
        rw [← hNr, ← hLdef, ← hPdef] at this
        have h' : P - E ≤ liK 0 Nr := by rw [hEdef]; linarith [(abs_le.mp this).2]
        exact h'
      rw [hθX]
      refine h0.trans ?_
      have hexp2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      calc 2 * ‖FW (WN N) ((a : ℝ) / q)‖ * Real.exp (π * q * P * Nr ^ (-(1 / 2 : ℝ)))
          ≤ 2 * (2 ^ n * Real.exp (-(liK 0 N) * Real.log 2 + q.totient * E * Real.log q)) *
              Real.exp (π * q * P * Nr ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = 2 ^ n * Real.exp (Real.log 2 + (-(liK 0 N) * Real.log 2 + q.totient * E * Real.log q) +
              π * q * P * Nr ^ (-(1 / 2 : ℝ))) := by
            simp only [Real.exp_add]; rw [← hexp2]; ring
        _ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓ + δ) * P) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            -- `log 2 ≤ δP/4`
            have t1 : Real.log 2 ≤ δ / 4 * P := by
              have h1 := hk2 L hL2
              rw [Real.rpow_one] at h1
              have h2 : 8 * Real.log 2 / δ * L ≤ Nr := h1.trans (by
                rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith))
              have h3 : 4 * Real.log 2 / δ ≤ Nr / (2 * L) := by
                rw [le_div_iff₀ (by positivity)]; field_simp at h2 ⊢; nlinarith
              have h4 : 4 * Real.log 2 / δ ≤ P := le_trans h3 hPlow
              rw [div_le_iff₀ hδ] at h4
              nlinarith
            -- the Siegel–Walfisz errors
            have t2 : E * Real.log 2 + q.totient * E * Real.log q ≤ δ / 4 * P := by
              have hlq : Real.log q ≤ L ^ B := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
              have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
              have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hLone hB.le
              have hφl : (q.totient : ℝ) * Real.log q ≤ L ^ B * L ^ B :=
                mul_le_mul (le_trans hφq hLB) hlq hlq0 (by positivity)
              have hsum : E * Real.log 2 + q.totient * E * Real.log q ≤ 2 * E * (L ^ B * L ^ B) := by
                have : Real.log 2 ≤ L ^ B * L ^ B := by
                  have : Real.log 2 < 1 := by
                    have := Real.log_two_lt_d9; linarith
                  nlinarith
                have e : (q.totient : ℝ) * E * Real.log q = E * ((q.totient : ℝ) * Real.log q) := by ring
                rw [e]
                nlinarith [mul_le_mul_of_nonneg_left hφl hE0, mul_le_mul_of_nonneg_left this hE0]
              have h1 := hk1 L hL1
              have hpow : L ^ (2 * B + 1) = L ^ B * L ^ B * L := by
                rw [Real.rpow_add_one hL0.ne', two_mul, Real.rpow_add hL0]
              rw [hpow] at h1
              have he : Real.exp (-c * √L) * Real.exp (c * √L) = 1 := by rw [← Real.exp_add]; simp
              -- `2E L^{2B} ≤ δ u/8 ≤ δP/4`
              have h2 : 2 * E * (L ^ B * L ^ B) ≤ δ / 8 * u := by
                have hp : 0 ≤ Nr * Real.exp (-c * √L) := by positivity
                have h3 : Nr * Real.exp (-c * √L) * (16 * C / δ * (L ^ B * L ^ B * L)) ≤ Nr :=
                  calc Nr * Real.exp (-c * √L) * (16 * C / δ * (L ^ B * L ^ B * L))
                      ≤ Nr * Real.exp (-c * √L) * Real.exp (c * √L) := mul_le_mul_of_nonneg_left h1 hp
                    _ = Nr := by rw [mul_assoc, he, mul_one]
                rw [hu, hEdef]
                rw [show δ / 8 * (Nr / L) = Nr / (8 * L / δ) by field_simp]
                rw [le_div_iff₀ (by positivity)]
                have e : 2 * (C * Nr * Real.exp (-c * √L)) * (L ^ B * L ^ B) * (8 * L / δ) =
                    Nr * Real.exp (-c * √L) * (16 * C / δ * (L ^ B * L ^ B * L)) := by field_simp; ring
                rw [e]; exact h3
              nlinarith
            -- `πqπ(N)N^{−1/2} ≤ δP/4`
            have t3 : π * q * P * Nr ^ (-(1 / 2 : ℝ)) ≤ δ / 4 * P := by
              have hr : Nr ^ (-(1 / 2 : ℝ)) = Real.exp (-(L / 2)) := by
                rw [Real.rpow_def_of_pos hNpos, ← hLdef]; ring_nf
              have h1 := hk3 L hL3
              have h2 : 4 * π / δ * q ≤ Real.exp (L / 2) := by
                refine le_trans ?_ (h1.trans (Real.exp_le_exp.mpr (by linarith)))
                exact mul_le_mul_of_nonneg_left hLB (by positivity)
              have h3 : π * q * Real.exp (-(L / 2)) ≤ δ / 4 := by
                have he : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by rw [← Real.exp_add]; simp
                have hp : 0 < Real.exp (-(L / 2)) := Real.exp_pos _
                have : 4 * π / δ * q * Real.exp (-(L / 2)) ≤ 1 := by
                  calc 4 * π / δ * q * Real.exp (-(L / 2)) ≤ Real.exp (L / 2) * Real.exp (-(L / 2)) :=
                        mul_le_mul_of_nonneg_right h2 hp.le
                    _ = 1 := by rw [mul_comm]; exact he
                have e : π * q * Real.exp (-(L / 2)) = δ / 4 * (4 * π / δ * q * Real.exp (-(L / 2))) := by
                  field_simp
                rw [e]; nlinarith
              rw [hr]
              have := mul_le_mul_of_nonneg_right h3 hP0.le
              nlinarith
            nlinarith
  -- integrate over the arc
  have hh : 0 ≤ PP B N / (q * N) := by unfold PP; rw [← hNr]; positivity
  have hlen : |((a : ℝ) / q + PP B N / (q * N)) - ((a : ℝ) / q - PP B N / (q * N))| ≤ 1 := by
    rw [show ((a : ℝ) / q + PP B N / (q * N)) - ((a : ℝ) / q - PP B N / (q * N)) = 2 * (PP B N / (q * N)) by ring,
      abs_of_nonneg (by positivity)]
    unfold PP; rw [← hNr, ← hLdef]
    rw [show 2 * (L ^ B / (q * Nr)) = 2 * L ^ B / (q * Nr) by ring, div_le_one (by positivity)]
    nlinarith
  unfold Rarc
  have hb : ∀ θ ∈ Set.uIoc ((a : ℝ) / q - PP B N / (q * N)) ((a : ℝ) / q + PP B N / (q * N)),
      ‖FW (WN N) θ * ee (-(T * θ))‖ ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓ + δ) * P) := by
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith)] at hθ
    rw [norm_mul, norm_ee, mul_one]
    exact hpt θ (abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  calc 2 ^ n * Real.exp ((-Real.log 2 + ℓ + δ) * P) *
        |((a : ℝ) / q + PP B N / (q * N)) - ((a : ℝ) / q - PP B N / (q * N))|
      ≤ 2 ^ n * Real.exp ((-Real.log 2 + ℓ + δ) * P) * 1 := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = _ := mul_one _

end ArcsAlgo.Core
