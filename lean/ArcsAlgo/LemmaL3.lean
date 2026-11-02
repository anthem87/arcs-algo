module

public import ArcsAlgo.LemmaL2
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# Lemma L, part 3: variation and integrals (paper §3.5)

`h_ε(y) = log max(|cos πy|, ε)` (`hEps`).

* `hEps_anti`, `hEps_mono`, `var_hEps`: `h_ε` is monotone on each half-period, so
  `Var(h_ε, [Y, Y + ℓ]) ≤ (4ℓ + 2) log(1/ε)`; `seqVar_G`: the same for `t ↦ h_ε(c + tβ)` on `[M, N]`.
* `int_Dε_le`, `int_D_le`: `∫_c^{c+X} (h_ε − log|cos π·|) ≤ (X + 2)ε` (one zero of `cos` per period,
  `|cos| ≥ 2 dist`).
* `int_G_le`: `∫_M^N h_ε(c + tβ) dt/log t ≤ (β log N)⁻¹(∫_c^{c+Nβ} log|cos πy| dy + (Nβ + 2)ε + Mβ log(1/ε))`.
* `sum_logcos`: `Σ_{(r,q)=1} ∫_{ra/q}^{ra/q+X} log|cos πy| dy = X(A_q(X) − φ(q) log 2)`, from
  `norm_cyc_prod_cos`, almost everywhere.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-- `h_ε(y) = log max(|cos πy|, ε)`. -/
noncomputable def hEps (ε y : ℝ) : ℝ := Real.log (max |cos (π * y)| ε)

theorem hEps_le (ε y : ℝ) (hε1 : ε ≤ 1) : hEps ε y ≤ 0 := by
  unfold hEps
  rcases (le_max_right |cos (π * y)| ε).eq_or_lt' with h | h
  · exact Real.log_nonpos (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le (abs_cos_le_one _) hε1)
  · exact Real.log_nonpos (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le (abs_cos_le_one _) hε1)

theorem hEps_ge {ε : ℝ} (hε : 0 < ε) (y : ℝ) : Real.log ε ≤ hEps ε y :=
  Real.log_le_log hε (le_max_right _ _)

theorem abs_hEps_sub {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : ℝ) :
    |hEps ε x - hEps ε y| ≤ -Real.log ε := by
  have := hEps_le ε x hε1; have := hEps_le ε y hε1
  have := hEps_ge hε x; have := hEps_ge hε y
  rw [abs_le]; constructor <;> linarith

/-- `|cos πy|` is antitone on `[k, k + 1/2]` and monotone on `[k + 1/2, k + 1]`. -/
theorem abs_cos_anti (k : ℤ) : AntitoneOn (fun y => |cos (π * y)|) (Set.Icc (k : ℝ) (k + 1 / 2)) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  have e : ∀ z : ℝ, |cos (π * z)| = |cos (π * (z - k))| := by
    intro z
    rw [show π * z = π * (z - k) + k * π by ring, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg,
      abs_one, one_zpow, one_mul]
  simp only
  rw [e x, e y]
  have h0 : ∀ z ∈ Set.Icc (k : ℝ) (k + 1 / 2), 0 ≤ cos (π * (z - k)) := fun z hz =>
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hz.1], by nlinarith [hz.2]⟩
  rw [abs_of_nonneg (h0 x hx), abs_of_nonneg (h0 y hy)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by nlinarith [hy.2]) (by nlinarith)

theorem abs_cos_mono (k : ℤ) : MonotoneOn (fun y => |cos (π * y)|) (Set.Icc ((k : ℝ) + 1 / 2) (k + 1)) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  have e : ∀ z : ℝ, |cos (π * z)| = |cos (π * (z - k))| := by
    intro z
    rw [show π * z = π * (z - k) + k * π by ring, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg,
      abs_one, one_zpow, one_mul]
  simp only
  rw [e x, e y]
  have h0 : ∀ z ∈ Set.Icc ((k : ℝ) + 1 / 2) (k + 1), cos (π * (z - k)) ≤ 0 := fun z hz =>
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [hz.1]) (by nlinarith [hz.2])
  rw [abs_of_nonpos (h0 x hx), abs_of_nonpos (h0 y hy), neg_le_neg_iff]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by nlinarith [hy.2]) (by nlinarith)

theorem hEps_anti {ε : ℝ} (hε : 0 < ε) (k : ℤ) : AntitoneOn (hEps ε) (Set.Icc (k : ℝ) (k + 1 / 2)) :=
  fun x hx y hy hxy => Real.log_le_log (lt_of_lt_of_le hε (le_max_right _ _))
    (max_le_max_right _ (abs_cos_anti k hx hy hxy))

theorem hEps_mono {ε : ℝ} (hε : 0 < ε) (k : ℤ) : MonotoneOn (hEps ε) (Set.Icc ((k : ℝ) + 1 / 2) (k + 1)) :=
  fun x hx y hy hxy => Real.log_le_log (lt_of_lt_of_le hε (le_max_right _ _))
    (max_le_max_right _ (abs_cos_mono k hx hy hxy))

/-! ### The variation of `h_ε` -/

theorem var_mono_piece {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    eVariationOn f (Set.Icc a b) = ENNReal.ofReal (f b - f a) := by
  have := hf.eVariationOn_eq (a := a) (b := b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [Set.inter_self] at this

theorem var_anti_piece {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) :
    eVariationOn f (Set.Icc a b) = ENNReal.ofReal (f a - f b) := by
  have hφ : AntitoneOn (fun y : ℝ => -y) (Set.Icc (-b) (-a)) := fun x _ y _ h => neg_le_neg h
  have h1 := eVariationOn.comp_eq_of_antitoneOn f (fun y : ℝ => -y) hφ
  rw [Set.image_neg_Icc, neg_neg, neg_neg] at h1
  rw [← h1]
  have hmono : MonotoneOn (f ∘ fun y : ℝ => -y) (Set.Icc (-b) (-a)) := by
    intro x hx y hy hxy
    exact hf ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
  rw [var_mono_piece (by linarith) hmono]
  simp

/-- On an interval inside one half-period block `[j/2, (j+1)/2]`, the variation is `≤ log(1/ε)`. -/
theorem var_block {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℤ) {x y : ℝ} (hxy : x ≤ y)
    (hx : (j : ℝ) / 2 ≤ x) (hy : y ≤ ((j : ℝ) + 1) / 2) :
    eVariationOn (hEps ε) (Set.Icc x y) ≤ ENNReal.ofReal (-Real.log ε) := by
  rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
  · have hsub : Set.Icc x y ⊆ Set.Icc (k : ℝ) (k + 1 / 2) := Set.Icc_subset_Icc (by push_cast at hx; linarith)
      (by push_cast at hy; linarith)
    rw [var_anti_piece hxy ((hEps_anti hε k).mono hsub)]
    exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (abs_hEps_sub hε hε1 x y))
  · have hsub : Set.Icc x y ⊆ Set.Icc ((k : ℝ) + 1 / 2) (k + 1) := Set.Icc_subset_Icc
      (by push_cast at hx; linarith) (by push_cast at hy; linarith)
    rw [var_mono_piece hxy ((hEps_mono hε k).mono hsub)]
    exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (abs_hEps_sub hε hε1 y x))

theorem var_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a : ℝ) :
    eVariationOn (hEps ε) (Set.Icc a (a + 1 / 2)) ≤ ENNReal.ofReal (2 * -Real.log ε) := by
  set j : ℤ := ⌈2 * a⌉
  set b : ℝ := (j : ℝ) / 2 with hb
  have hj1 : 2 * a ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < 2 * a + 1 := Int.ceil_lt_add_one _
  have hab : a ≤ b := by simp only [b]; linarith
  have hbc : b ≤ a + 1 / 2 := by simp only [b]; linarith
  have hsplit := eVariationOn.Icc_add_Icc (hEps ε) (s := Set.univ) hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at hsplit
  rw [← hsplit]
  have hK : 0 ≤ -Real.log ε := by have := Real.log_nonpos hε.le hε1; linarith
  calc eVariationOn (hEps ε) (Set.Icc a b) + eVariationOn (hEps ε) (Set.Icc b (a + 1 / 2))
      ≤ ENNReal.ofReal (-Real.log ε) + ENNReal.ofReal (-Real.log ε) := by
        gcongr
        · exact var_block hε hε1 (j - 1) hab (by push_cast; linarith) (by push_cast; linarith)
        · exact var_block hε hε1 j hbc (le_of_eq hb.symm) (by linarith)
    _ = ENNReal.ofReal (2 * -Real.log ε) := by rw [← ENNReal.ofReal_add hK hK]; ring_nf

theorem var_n_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a : ℝ) (n : ℕ) :
    eVariationOn (hEps ε) (Set.Icc a (a + n / 2)) ≤ ENNReal.ofReal (n * (2 * -Real.log ε)) := by
  have hK : 0 ≤ -Real.log ε := by have := Real.log_nonpos hε.le hε1; linarith
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_div, add_zero, zero_mul, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
    exact (eVariationOn.eq_zero_iff _).mpr fun x hx y hy => by
      rw [Set.Icc_self] at hx hy; rw [hx, hy, edist_self]
  | succ n ih =>
    have h1 : a ≤ a + n / 2 := by have : (0 : ℝ) ≤ n / 2 := by positivity
                                  linarith
    have h2 : a + n / 2 ≤ a + (n + 1 : ℕ) / 2 := by push_cast; linarith
    have hsplit := eVariationOn.Icc_add_Icc (hEps ε) (s := Set.univ) h1 h2 (Set.mem_univ _)
    simp only [Set.univ_inter] at hsplit
    rw [← hsplit]
    have hh := var_half hε hε1 (a + n / 2)
    rw [show a + (n : ℝ) / 2 + 1 / 2 = a + ((n + 1 : ℕ) : ℝ) / 2 by push_cast; ring] at hh
    calc eVariationOn (hEps ε) (Set.Icc a (a + n / 2)) + eVariationOn (hEps ε) (Set.Icc (a + n / 2) (a + (n + 1 : ℕ) / 2))
        ≤ ENNReal.ofReal (n * (2 * -Real.log ε)) + ENNReal.ofReal (2 * -Real.log ε) := add_le_add ih hh
      _ = ENNReal.ofReal ((n + 1 : ℕ) * (2 * -Real.log ε)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; push_cast; ring_nf

/-- **Step C**: `Var(h_ε, [Y, Y + ℓ]) ≤ (4ℓ + 2) log(1/ε)`. -/
theorem var_hEps {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (Y : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    eVariationOn (hEps ε) (Set.Icc Y (Y + ℓ)) ≤ ENNReal.ofReal ((4 * ℓ + 2) * -Real.log ε) := by
  have hK : 0 ≤ -Real.log ε := by have := Real.log_nonpos hε.le hε1; linarith
  set n := ⌈2 * ℓ⌉₊
  have hn1 : 2 * ℓ ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < 2 * ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
  calc eVariationOn (hEps ε) (Set.Icc Y (Y + ℓ)) ≤ eVariationOn (hEps ε) (Set.Icc Y (Y + n / 2)) :=
        eVariationOn.mono _ (Set.Icc_subset_Icc le_rfl (by linarith))
    _ ≤ ENNReal.ofReal (n * (2 * -Real.log ε)) := var_n_half hε hε1 Y n
    _ ≤ ENNReal.ofReal ((4 * ℓ + 2) * -Real.log ε) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- `SeqVar` for `G_r(t) = h_ε(c + tβ)` on `[M, N]`, `β ≥ 0`. -/
theorem seqVar_G {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) {M N : ℝ} (hMN : M ≤ N) :
    SeqVar (fun t => hEps ε (c + t * β)) M N ((4 * ((N - M) * β) + 2) * -Real.log ε) := by
  intro k u hu hus
  have hK : 0 ≤ -Real.log ε := by have := Real.log_nonpos hε.le hε1; linarith
  set v : ℕ → ℝ := fun i => c + u i * β
  have hv : Monotone v := fun i j hij => by
    simp only [v]; have := hu hij; nlinarith
  have hvs : ∀ i, v i ∈ Set.Icc (c + M * β) (c + M * β + (N - M) * β) := by
    intro i; simp only [v]
    have := hus i
    constructor <;> nlinarith [this.1, this.2]
  have h1 := eVariationOn.sum_le (f := hEps ε) (n := k) hv hvs
  have h2 := var_hEps hε hε1 (c + M * β) (show 0 ≤ (N - M) * β by nlinarith)
  have h3 := h1.trans h2
  simp only [edist_dist, Real.dist_eq] at h3
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  exact h3

/-! ### Step D: the integrals -/

theorem logcos_int (a b : ℝ) : IntervalIntegrable (fun y => Real.log (cos (π * y))) MeasureTheory.volume a b := by
  have h1 := (logsin_int (a + 1 / 2) (b + 1 / 2)).comp_add_right (1 / 2)
  simp only [add_sub_cancel_right] at h1
  refine h1.congr fun y _ => ?_
  rw [show π * (y + 1 / 2) = π * y + π / 2 by ring, Real.sin_add_pi_div_two]

theorem hEps_cont (ε : ℝ) (hε : 0 < ε) : Continuous (hEps ε) := by
  unfold hEps
  refine Continuous.log (by fun_prop) fun y => ?_
  exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'

/-- `D(s) = h_ε(s + 1/2) − log|cos π(s + 1/2)| = log max(|sin πs|, ε) − log|sin πs|`. -/
noncomputable def Dε (ε s : ℝ) : ℝ := hEps ε (s + 1 / 2) - Real.log (cos (π * (s + 1 / 2)))

theorem Dε_eq (ε s : ℝ) : Dε ε s = Real.log (max |sin (π * s)| ε) - Real.log (sin (π * s)) := by
  unfold Dε hEps
  rw [show π * (s + 1 / 2) = π * s + π / 2 by ring, Real.cos_add_pi_div_two, abs_neg, Real.log_neg_eq_log]

theorem Dε_periodic (ε : ℝ) : Function.Periodic (Dε ε) 1 := by
  intro s; rw [Dε_eq, Dε_eq, show π * (s + 1) = π * s + π by ring, Real.sin_add_pi, abs_neg, Real.log_neg_eq_log]

theorem Dε_even (ε s : ℝ) : Dε ε (-s) = Dε ε s := by
  rw [Dε_eq, Dε_eq, show π * -s = -(π * s) by ring, Real.sin_neg, abs_neg, Real.log_neg_eq_log]

theorem Dε_int (ε : ℝ) (hε : 0 < ε) (a b : ℝ) : IntervalIntegrable (Dε ε) MeasureTheory.volume a b := by
  unfold Dε
  refine ((hEps_cont ε hε).comp (by fun_prop : Continuous fun s : ℝ => s + 1 / 2)).intervalIntegrable a b |>.sub ?_
  have := (logcos_int (a + 1 / 2) (b + 1 / 2)).comp_add_right (1 / 2)
  simp only [add_sub_cancel_right] at this
  exact this

/-- `D ≤ max(0, log(ε/(2s)))` on `(0, 1/2]`. -/
theorem Dε_le {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    Dε ε s ≤ max 0 (Real.log ε - Real.log (2 * s)) := by
  rw [Dε_eq]
  have hpi := Real.pi_pos
  have hs : 2 * s ≤ sin (π * s) := by
    have := Real.mul_le_sin (x := π * s) (by positivity) (by nlinarith)
    have e : 2 / π * (π * s) = 2 * s := by field_simp
    linarith
  have hsp : 0 < sin (π * s) := by linarith
  rw [abs_of_pos hsp]
  rcases le_total (sin (π * s)) ε with h | h
  · rw [max_eq_right h]
    have := Real.log_le_log (by positivity) hs
    exact le_trans (by linarith) (le_max_right _ _)
  · rw [max_eq_left h]; simp

/-- `∫_{−1/2}^{1/2} D ≤ ε` for `0 < ε ≤ 1`. -/
theorem int_Dε_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : ∫ s in (-1 / 2 : ℝ)..(1 / 2), Dε ε s ≤ ε := by
  have hsym : ∫ s in (-1 / 2 : ℝ)..(1 / 2), Dε ε s = 2 * ∫ s in (0 : ℝ)..(1 / 2), Dε ε s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (Dε_int ε hε (-1 / 2) 0) (Dε_int ε hε 0 (1 / 2))]
    have : ∫ s in (-1 / 2 : ℝ)..0, Dε ε s = ∫ s in (0 : ℝ)..(1 / 2), Dε ε s := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := 1 / 2) (Dε ε)
      rw [neg_zero, show -(1 / 2 : ℝ) = -1 / 2 by ring] at this
      rw [← this]; exact intervalIntegral.integral_congr fun s _ => Dε_even ε s
    rw [this]; ring
  rw [hsym]
  have hε2 : ε / 2 ≤ 1 / 2 := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (Dε_int ε hε 0 (ε / 2)) (Dε_int ε hε (ε / 2) (1 / 2))
  have hlogint : IntervalIntegrable (fun s => Real.log ε - Real.log 2 - Real.log s) MeasureTheory.volume 0 (ε / 2) :=
    (intervalIntegrable_const.sub intervalIntegrable_const).sub intervalIntegral.intervalIntegrable_log'
  have h1 : ∫ s in (0 : ℝ)..(ε / 2), Dε ε s ≤ ∫ s in (0 : ℝ)..(ε / 2), (Real.log ε - Real.log 2 - Real.log s) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) (Dε_int ε hε _ _) hlogint fun s hs => ?_
    have h := Dε_le hε hs.1 (by linarith [hs.2])
    have hge : 0 ≤ Real.log ε - Real.log (2 * s) := by
      have := Real.log_le_log (by linarith [hs.1]) (show 2 * s ≤ ε by linarith [hs.2]); linarith
    rw [max_eq_right hge, Real.log_mul (by norm_num) hs.1.ne'] at h; linarith
  have h2 : ∫ s in (ε / 2)..(1 / 2), Dε ε s ≤ ∫ s in (ε / 2)..(1 / 2), (0 : ℝ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hε2 (Dε_int ε hε _ _) intervalIntegrable_const fun s hs => ?_
    have h := Dε_le hε (by linarith [hs.1]) hs.2.le
    have hle : Real.log ε - Real.log (2 * s) ≤ 0 := by
      have := Real.log_le_log hε (show ε ≤ 2 * s by linarith [hs.1]); linarith
    rwa [max_eq_left hle] at h
  have h3 : ∫ s in (0 : ℝ)..(ε / 2), (Real.log ε - Real.log 2 - Real.log s) = ε / 2 := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub intervalIntegrable_const)
      intervalIntegral.intervalIntegrable_log', integral_log, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, mul_zero, Real.log_zero]
    rw [Real.log_div hε.ne' (by norm_num)]; ring
  simp only [intervalIntegral.integral_zero] at h2
  linarith

theorem cos_zero_countable : MeasureTheory.volume {y : ℝ | cos (π * y) = 0} = 0 := by
  apply Set.Countable.measure_zero
  refine (Set.countable_range (fun k : ℤ => ((2 * k + 1 : ℤ) : ℝ) / 2)).mono fun y hy => ?_
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hy
  refine ⟨k, ?_⟩
  have := Real.pi_pos
  push_cast
  field_simp at hk ⊢; linarith

/-- `D(y) = h_ε(y) − log|cos πy| ≥ 0` off the zeros of `cos πy`. -/
theorem D_nonneg_ae (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ y ∂MeasureTheory.volume, 0 ≤ hEps ε y - Real.log (cos (π * y)) := by
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp cos_zero_countable] with y hy
  have hc : cos (π * y) ≠ 0 := hy
  unfold hEps
  rw [← Real.log_abs (cos (π * y))]
  have := Real.log_le_log (abs_pos.mpr hc) (le_max_left |cos (π * y)| ε)
  linarith

theorem D_int (ε : ℝ) (hε : 0 < ε) (a b : ℝ) :
    IntervalIntegrable (fun y => hEps ε y - Real.log (cos (π * y))) MeasureTheory.volume a b :=
  ((hEps_cont ε hε).intervalIntegrable a b).sub (logcos_int a b)

theorem D_periodic (ε : ℝ) : Function.Periodic (fun y => hEps ε y - Real.log (cos (π * y))) 1 := by
  intro y
  have := Dε_periodic ε (y - 1 / 2)
  simp only [Dε] at this
  rwa [show y - 1 / 2 + 1 + 1 / 2 = y + 1 by ring, show y - 1 / 2 + 1 / 2 = y by ring] at this

theorem int_D_nat (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∫ y in (0 : ℝ)..n, (hEps ε y - Real.log (cos (π * y))) =
      n * ∫ y in (0 : ℝ)..1, (hEps ε y - Real.log (cos (π * y))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := (D_periodic ε).intervalIntegral_add_eq (n : ℝ) 0
    rw [zero_add] at this
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals (D_int ε hε 0 n) (D_int ε hε n (n + 1)), ih, this]
    ring

/-- `∫_c^{c+X} (h_ε − log|cos π·|) ≤ (X + 2)ε`. -/
theorem int_D_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    ∫ y in c..c + X, (hEps ε y - Real.log (cos (π * y))) ≤ (X + 2) * ε := by
  set D : ℝ → ℝ := fun y => hEps ε y - Real.log (cos (π * y))
  set k : ℤ := ⌊c⌋
  set n : ℕ := ⌈X⌉₊ + 1
  have hk1 : (k : ℝ) ≤ c := Int.floor_le c
  have hk2 : c < k + 1 := Int.lt_floor_add_one c
  have hn : X ≤ ⌈X⌉₊ := Nat.le_ceil X
  have hn2 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX
  have hnr : (n : ℝ) = ⌈X⌉₊ + 1 := by simp only [n]; push_cast; ring
  have hcover : ∫ y in c..c + X, D y ≤ ∫ y in (k : ℝ)..k + n, D y := by
    refine intervalIntegral.integral_mono_interval hk1 (by linarith) (by linarith) ?_ (D_int ε hε _ _)
    exact MeasureTheory.ae_restrict_of_ae (D_nonneg_ae ε hε)
  have hshift : ∫ y in (k : ℝ)..k + n, D y = ∫ y in (0 : ℝ)..n, D y := by
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := n) D (k : ℝ)
    rw [zero_add, add_comm (n : ℝ)] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun y _ => by
      have := (D_periodic ε).int_mul k y
      simp only [mul_one] at this
      exact this
  have hone : ∫ y in (0 : ℝ)..1, D y = ∫ s in (-1 / 2 : ℝ)..(1 / 2), Dε ε s := by
    have := intervalIntegral.integral_comp_add_right (a := -1 / 2) (b := 1 / 2) D (1 / 2)
    rw [show (-1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at this
    rw [← this]; rfl
  have hper := int_Dε_le hε hε1
  rw [hshift, int_D_nat ε hε n, hone] at hcover
  have : (n : ℝ) ≤ X + 2 := by linarith
  calc ∫ y in c..c + X, D y ≤ n * ∫ s in (-1 / 2 : ℝ)..(1 / 2), Dε ε s := hcover
    _ ≤ n * ε := mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg _)
    _ ≤ (X + 2) * ε := mul_le_mul_of_nonneg_right this hε.le

/-- **Step D, one class**: `∫_M^N h_ε(c + tβ) dt/log t ≤ (β log N)⁻¹ (∫_c^{c+Nβ} log|cos πy| dy
+ (Nβ + 2)ε + Mβ log(1/ε))`. -/
theorem int_G_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) {β : ℝ} (hβ : 0 < β) {M N : ℕ} (hM : 3 ≤ M)
    (hMN : M ≤ N) :
    ∫ t in (M : ℝ)..N, hEps ε (c + t * β) * liIntegrand 0 t ≤
      1 / (β * Real.log N) * ((∫ y in c..c + N * β, Real.log (cos (π * y))) + (N * β + 2) * ε +
        M * β * -Real.log ε) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set f : ℝ → ℝ := fun t => hEps ε (c + t * β)
  have hfc : Continuous f := (hEps_cont ε hε).comp (by fun_prop)
  -- `1/log t ≥ 1/log N` and `f ≤ 0`
  have h1 : ∫ t in (M : ℝ)..N, f t * liIntegrand 0 t ≤ ∫ t in (M : ℝ)..N, f t * (1 / Real.log N) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hMN'
      ((intervalIntegrable_liIntegrand 0 _ _).continuousOn_mul hfc.continuousOn)
      (hfc.intervalIntegrable _ _ |>.mul_const _) fun t ht => ?_
    have ht2 : 2 < t := by linarith [ht.1]
    have hli : 1 / Real.log N ≤ liIntegrand 0 t := by
      unfold liIntegrand; rw [if_pos ht2, pow_zero]
      exact one_div_le_one_div_of_le (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) ht.2.le)
    exact mul_le_mul_of_nonpos_left hli (hEps_le ε _ hε1)
  have h2 : ∫ t in (M : ℝ)..N, f t * (1 / Real.log N) =
      1 / (β * Real.log N) * ∫ y in c + M * β..c + N * β, hEps ε y := by
    rw [intervalIntegral.integral_mul_const]
    have := intervalIntegral.integral_comp_mul_add (a := (M : ℝ)) (b := N) (hEps ε) hβ.ne' c
    rw [show β * (M : ℝ) + c = c + M * β by ring, show β * (N : ℝ) + c = c + N * β by ring, smul_eq_mul] at this
    rw [show (∫ t in (M : ℝ)..N, f t) = ∫ t in (M : ℝ)..N, hEps ε (β * t + c) from
      intervalIntegral.integral_congr fun t _ => by simp only [f]; ring_nf, this]
    field_simp
  have hi : ∀ a b : ℝ, IntervalIntegrable (hEps ε) MeasureTheory.volume a b :=
    fun a b => (hEps_cont ε hε).intervalIntegrable a b
  have h3 : ∫ y in c + M * β..c + N * β, hEps ε y ≤
      (∫ y in c..c + N * β, hEps ε y) + M * β * -Real.log ε := by
    have e := intervalIntegral.integral_add_adjacent_intervals (hi c (c + M * β)) (hi (c + M * β) (c + N * β))
    have hcM : c ≤ c + M * β := by
      have : (0 : ℝ) ≤ M * β := by positivity
      linarith
    have hlow : M * β * Real.log ε ≤ ∫ y in c..c + M * β, hEps ε y := by
      have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hcM
        intervalIntegrable_const (hi _ _) fun y _ => hEps_ge hε y
      simpa [intervalIntegral.integral_const, mul_comm] using this
    linarith
  have h4 : ∫ y in c..c + N * β, hEps ε y ≤ (∫ y in c..c + N * β, Real.log (cos (π * y))) + (N * β + 2) * ε := by
    have hD := int_D_le hε hε1 c (show 0 ≤ (N : ℝ) * β by positivity)
    rw [intervalIntegral.integral_sub (hi _ _) (logcos_int _ _)] at hD
    linarith
  have hpos : 0 ≤ 1 / (β * Real.log N) := by positivity
  calc ∫ t in (M : ℝ)..N, hEps ε (c + t * β) * liIntegrand 0 t ≤ ∫ t in (M : ℝ)..N, f t * (1 / Real.log N) := h1
    _ = 1 / (β * Real.log N) * ∫ y in c + M * β..c + N * β, hEps ε y := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hpos

theorem shift_zero_countable (c : ℝ) : MeasureTheory.volume {x : ℝ | cos (π * (c + x)) = 0} = 0 := by
  apply Set.Countable.measure_zero
  refine (Set.countable_range (fun k : ℤ => ((2 * k + 1 : ℤ) : ℝ) / 2 - c)).mono fun x hx => ?_
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hx
  refine ⟨k, ?_⟩
  have := Real.pi_pos
  push_cast
  field_simp at hk ⊢; linarith

/-- **Step D, all classes**: `Σ_{(r,q)=1} ∫_{ra/q}^{ra/q + X} log|cos πy| dy = X(A_q(X) − φ(q) log 2)`. -/
theorem sum_logcos {q a : ℕ} (h3 : 3 ≤ q) (ha : a.Coprime q) {X : ℝ} (hX : 0 < X) :
    ∑ r ∈ resQ q, ∫ y in ((r * a : ℕ) : ℝ) / q..((r * a : ℕ) : ℝ) / q + X, Real.log (cos (π * y)) =
      X * Aq q X - X * q.totient * Real.log 2 := by
  have hshift : ∀ r ∈ resQ q, ∫ y in ((r * a : ℕ) : ℝ) / q..((r * a : ℕ) : ℝ) / q + X, Real.log (cos (π * y)) =
      ∫ x in (0 : ℝ)..X, Real.log (cos (π * (((r * a : ℕ) : ℝ) / q + x))) := by
    intro r _
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := X) (fun y => Real.log (cos (π * y)))
      (((r * a : ℕ) : ℝ) / q)
    rw [zero_add, add_comm X] at this
    rw [← this]; exact intervalIntegral.integral_congr fun x _ => by ring_nf
  have hint : ∀ r ∈ resQ q, IntervalIntegrable (fun x => Real.log (cos (π * (((r * a : ℕ) : ℝ) / q + x))))
      MeasureTheory.volume 0 X := by
    intro r _
    have := (logcos_int (((r * a : ℕ) : ℝ) / q) (((r * a : ℕ) : ℝ) / q + X)).comp_add_right (((r * a : ℕ) : ℝ) / q)
    simp only [add_sub_cancel_left, sub_self] at this
    refine this.congr fun x _ => ?_
    ring_nf
  rw [sum_congr rfl hshift, ← intervalIntegral.integral_finsetSum hint]
  -- a.e. identity with `h_q`
  have hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc 0 X →
      ∑ r ∈ resQ q, Real.log (cos (π * (((r * a : ℕ) : ℝ) / q + x))) = hq q x - q.totient * Real.log 2 := by
    have hnull : MeasureTheory.volume (⋃ r ∈ resQ q, {x : ℝ | cos (π * (((r * a : ℕ) : ℝ) / q + x)) = 0}) = 0 :=
      (MeasureTheory.measure_biUnion_null_iff (resQ q).countable_toSet).mpr fun r _ => shift_zero_countable _
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with x hx _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hx
    unfold hq
    rw [norm_cyc_prod_cos h3 ha x, Real.log_prod (fun r hr => by
      have := hx r hr; positivity)]
    rw [← card_resQ, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    refine sum_congr rfl fun r hr => ?_
    rw [Real.log_mul (by norm_num) (abs_ne_zero.mpr (hx r hr)), Real.log_abs]; ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hqint : IntervalIntegrable (hq q) MeasureTheory.volume 0 X := by
    have hsum1 : IntervalIntegrable (fun x => ∑ r ∈ resQ q, Real.log (cos (π * (((r * a : ℕ) : ℝ) / q + x))))
        MeasureTheory.volume 0 X := by
      have := IntervalIntegrable.sum (resQ q) hint
      convert this using 1; ext x; simp [Finset.sum_apply]
    have hs : IntervalIntegrable (fun x => ∑ r ∈ resQ q, Real.log (cos (π * (((r * a : ℕ) : ℝ) / q + x))) +
        q.totient * Real.log 2) MeasureTheory.volume 0 X := hsum1.add intervalIntegrable_const
    refine hs.congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with x hx hxm
    have := hx hxm; linarith
  rw [intervalIntegral.integral_sub hqint intervalIntegrable_const, intervalIntegral.integral_const]
  unfold Aq
  rw [sub_zero, smul_eq_mul]
  field_simp

end ArcsAlgo.Core
