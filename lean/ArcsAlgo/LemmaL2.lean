module

public import ArcsAlgo.LemmaL1
set_option autoImplicit false

/-!
# Lemma L, part 2: one class of primes (paper §3.5)

* `SeqVar`: variation `≤ V` along monotone sequences; `seq_consec`, `seq_shift`.
* `sum_Ioc_by_parts`, `cntQ_sub`: summation by parts against `π(n; q, r)`.
* `class_sum_le`: for `f` continuous on `[M, N]`, `|f| ≤ S`, variation `≤ V`, and
  `|π(n; q, r) − li(n)/φ(q)| ≤ E`: `Σ_{M<p≤N, p≡r} f(p) ≤ φ(q)⁻¹∫_M^N f(t) dt/log t + V/φ(q) + E(2S + V)`
  (the Stieltjes estimate of the paper, `|∫f dE| ≤ (2 sup|f| + Var f) sup|E|`, in discrete form).
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

/-- Variation of `f` on `[a, b]` at most `V`, in the form used: along every monotone sequence. -/
def SeqVar (f : ℝ → ℝ) (a b V : ℝ) : Prop :=
  ∀ (k : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Set.Icc a b) →
    ∑ i ∈ range k, |f (u (i + 1)) - f (u i)| ≤ V

/-- Summation by parts on `(M, N]`. -/
theorem sum_Ioc_by_parts (e g : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Ioc M N, (e n - e (n - 1)) * g n =
      e N * g N - e M * g M - ∑ n ∈ Ico M N, e n * (g (n + 1) - g n) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [Finset.sum_Ioc_succ_top hMN, Finset.sum_Ico_succ_top hMN, ih, Nat.add_sub_cancel]
    ring

theorem cntQ_sub (n q r : ℕ) (hn : 1 ≤ n) :
    (cntQ n q r : ℝ) - cntQ (n - 1) q r = if n.Prime ∧ n % q = r % q then 1 else 0 := by
  unfold cntQ
  rw [Nat.sub_add_cancel hn, range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]; push_cast; ring
  · simp

theorem sum_two_mul (t : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ range (2 * K), t i = ∑ j ∈ range K, (t (2 * j) + t (2 * j + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]; ring

theorem seq_consec {f : ℝ → ℝ} {V : ℝ} {M N : ℕ} (hMN : M ≤ N) (hV : SeqVar f M N V) :
    ∑ n ∈ Ico M N, |f (n + 1) - f n| ≤ V := by
  set u : ℕ → ℝ := fun i => min ((M : ℝ) + i) N
  have hu : Monotone u := fun i j hij => min_le_min_right _ (by exact_mod_cast Nat.add_le_add_left hij M)
  have hus : ∀ i, u i ∈ Set.Icc (M : ℝ) N := fun i =>
    ⟨le_min (by simp) (by exact_mod_cast hMN), min_le_right _ _⟩
  have h := hV (N - M) u hu hus
  rw [sum_Ico_eq_sum_range]
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have h1 : u i = ((M + i : ℕ) : ℝ) := by
    simp only [u]; rw [min_eq_left]; · push_cast; ring
    exact_mod_cast (by omega : M + i ≤ N)
  have h2 : u (i + 1) = ((M + i : ℕ) : ℝ) + 1 := by
    simp only [u]; rw [min_eq_left]; · push_cast; ring
    exact_mod_cast (by omega : M + (i + 1) ≤ N)
  rw [h1, h2]

theorem seq_shift {f : ℝ → ℝ} {V : ℝ} {M N : ℕ} (hMN : M ≤ N) (hV : SeqVar f M N V) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ n ∈ Ioc M N, |f n - f ((n : ℝ) - 1 + s)| ≤ V := by
  set u : ℕ → ℝ := fun i => min ((M : ℝ) + (i / 2 : ℕ) + (if i % 2 = 0 then s else 1)) N
  have hstep : ∀ i, (M : ℝ) + (i / 2 : ℕ) + (if i % 2 = 0 then s else 1) ≤
      (M : ℝ) + ((i + 1) / 2 : ℕ) + (if (i + 1) % 2 = 0 then s else 1) := by
    intro i
    rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have e1 : (k + k) / 2 = k := by omega
      have e2 : (k + k + 1) / 2 = k := by omega
      rw [e1, e2, if_pos (by omega), if_neg (by omega)]; linarith
    · have e1 : (2 * k + 1) / 2 = k := by omega
      have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [e1, e2, if_neg (by omega), if_pos (by omega)]; push_cast; linarith
  have hu : Monotone u := monotone_nat_of_le_succ fun i => min_le_min_right _ (hstep i)
  have hus : ∀ i, u i ∈ Set.Icc (M : ℝ) N := by
    intro i
    refine ⟨le_min ?_ (by exact_mod_cast hMN), min_le_right _ _⟩
    have : (0 : ℝ) ≤ (if i % 2 = 0 then s else 1) := by split_ifs <;> linarith
    have : (0 : ℝ) ≤ ((i / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h := hV (2 * (N - M)) u hu hus
  rw [sum_two_mul] at h
  have hodd : ∀ j ∈ range (N - M), u (2 * j + 1) = ((M + j + 1 : ℕ) : ℝ) ∧ u (2 * j) = ((M + j : ℕ) : ℝ) + s := by
    intro j hj
    have hj' := mem_range.mp hj
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : (2 * j) / 2 = j := by omega
    constructor
    · simp only [u]; rw [e1, if_neg (by omega), min_eq_left]; · push_cast; ring
      have : M + j + 1 ≤ N := by omega
      have : ((M + j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this ⊢; linarith
    · simp only [u]; rw [e2, if_pos (by omega), min_eq_left]; · push_cast; ring
      have : M + j + 1 ≤ N := by omega
      have : ((M + j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this ⊢; linarith
  have hsum : ∑ n ∈ Ioc M N, |f n - f ((n : ℝ) - 1 + s)| =
      ∑ j ∈ range (N - M), |f (u (2 * j + 1)) - f (u (2 * j))| := by
    rw [show Ioc M N = Ico (M + 1) (N + 1) by ext n; simp only [mem_Ioc, mem_Ico]; omega, sum_Ico_eq_sum_range,
      show N + 1 - (M + 1) = N - M by omega]
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨h1, h2⟩ := hodd j hj
    rw [h1, h2]; push_cast; ring_nf
  rw [hsum]
  refine le_trans (sum_le_sum fun j _ => ?_) h
  have := abs_nonneg (f (u (2 * j + 1 + 1)) - f (u (2 * j + 1)))
  rw [show 2 * j + 1 + 1 = 2 * j + 1 + 1 from rfl]
  linarith

theorem liIntegrand_le_one {t : ℝ} (ht : 3 ≤ t) : liIntegrand 0 t ≤ 1 := by
  unfold liIntegrand; rw [if_pos (by linarith), pow_zero]
  have : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; have := Real.exp_one_lt_d9; linarith
  rw [div_le_one (by linarith)]; linarith

theorem liK_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    liK 0 n - liK 0 ((n - 1 : ℕ) : ℝ) = ∫ t in ((n - 1 : ℕ) : ℝ)..n, liIntegrand 0 t := by
  unfold liK
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_liIntegrand 0 0 ((n - 1 : ℕ) : ℝ))
    (intervalIntegrable_liIntegrand 0 ((n - 1 : ℕ) : ℝ) n)]; ring

theorem sum_integral_Ioc (g : ℝ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (hg : ∀ n ∈ Ioc M N, IntervalIntegrable g MeasureTheory.volume ((n - 1 : ℕ) : ℝ) n) :
    ∑ n ∈ Ioc M N, ∫ t in ((n - 1 : ℕ) : ℝ)..n, g t = ∫ t in (M : ℝ)..N, g t := by
  have hI : Ioc M N = Ico (M + 1) (N + 1) := by ext n; simp only [mem_Ioc, mem_Ico]; omega
  rw [hI, sum_Ico_eq_sum_range, show N + 1 - (M + 1) = N - M by omega]
  have := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := g)
    (a := fun k : ℕ => ((M + k : ℕ) : ℝ)) (n := N - M) fun k hk => by
      have h := hg (M + k + 1) (by rw [hI]; simp only [mem_Ico]; omega)
      rw [show M + k + 1 - 1 = M + k by omega] at h
      simpa [add_assoc] using h
  simp only [Nat.add_zero, show M + (N - M) = N by omega] at this
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  rw [show M + 1 + k - 1 = M + k by omega, show M + 1 + k = M + (k + 1) by omega]

set_option maxHeartbeats 1000000 in
/-- **Step B, one class**: for `f` continuous on `[M, N]` (`M ≥ 3`), `|f| ≤ S`, of variation `≤ V`, and
`|π(n; q, r) − li(n)/φ(q)| ≤ E` on `[M, N]`:
`Σ_{M<p≤N, p≡r} f(p) ≤ φ(q)⁻¹ ∫_M^N f(t) dt/log t + V/φ(q) + E(2S + V)`. -/
theorem class_sum_le {f : ℝ → ℝ} {q r M N : ℕ} (hq : 1 ≤ q) (hM : 3 ≤ M) (hMN : M ≤ N) {E S V : ℝ}
    (hf : ContinuousOn f (Set.Icc (M : ℝ) N))
    (hE : ∀ n : ℕ, M ≤ n → n ≤ N → |(cntQ n q r : ℝ) - liK 0 n / q.totient| ≤ E)
    (hS : ∀ t ∈ Set.Icc (M : ℝ) N, |f t| ≤ S) (hV : SeqVar f M N V) (hE0 : 0 ≤ E) :
    ∑ n ∈ (Ioc M N).filter (fun n => n.Prime ∧ n % q = r % q), f n ≤
      (1 / q.totient) * (∫ t in (M : ℝ)..N, f t * liIntegrand 0 t) + V / q.totient + E * (2 * S + V) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set A : ℕ → ℝ := fun n => (cntQ n q r : ℝ)
  set Lf : ℕ → ℝ := fun n => liK 0 n / q.totient
  set Er : ℕ → ℝ := fun n => A n - Lf n
  set g : ℕ → ℝ := fun n => f n
  have hV0 : 0 ≤ V := by
    have := hV 0 (fun _ => M) monotone_const (fun _ => ⟨le_rfl, by exact_mod_cast hMN⟩); simpa using this
  have hind : ∑ n ∈ (Ioc M N).filter (fun n => n.Prime ∧ n % q = r % q), f n =
      ∑ n ∈ Ioc M N, (A n - A (n - 1)) * g n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    simp only [A, g]; rw [cntQ_sub n q r hn1]; split_ifs <;> ring
  rw [hind]
  have hsplit : ∑ n ∈ Ioc M N, (A n - A (n - 1)) * g n =
      ∑ n ∈ Ioc M N, (Lf n - Lf (n - 1)) * g n + ∑ n ∈ Ioc M N, (Er n - Er (n - 1)) * g n := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_; simp only [Er]; ring
  rw [hsplit]
  -- the error part
  have herr : ∑ n ∈ Ioc M N, (Er n - Er (n - 1)) * g n ≤ E * (2 * S + V) := by
    rw [sum_Ioc_by_parts Er g M N hMN]
    have hEN : |Er N| ≤ E := hE N hMN le_rfl
    have hEM : |Er M| ≤ E := hE M le_rfl hMN
    have hgN : |g N| ≤ S := hS N ⟨by exact_mod_cast hMN, le_rfl⟩
    have hgM : |g M| ≤ S := hS M ⟨le_rfl, by exact_mod_cast hMN⟩
    have hsum : |∑ n ∈ Ico M N, Er n * (g (n + 1) - g n)| ≤ E * V := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Ico M N, |Er n * (g (n + 1) - g n)| ≤ ∑ n ∈ Ico M N, E * |f (n + 1) - f n| := by
            refine sum_le_sum fun n hn => ?_
            have hn' := mem_Ico.mp hn
            rw [abs_mul]
            simp only [g]; push_cast
            exact mul_le_mul_of_nonneg_right (hE n hn'.1 hn'.2.le) (abs_nonneg _)
        _ = E * ∑ n ∈ Ico M N, |f (n + 1) - f n| := by rw [mul_sum]
        _ ≤ E * V := mul_le_mul_of_nonneg_left (seq_consec hMN hV) hE0
    have h1 : Er N * g N ≤ E * S := by
      calc Er N * g N ≤ |Er N * g N| := le_abs_self _
        _ = |Er N| * |g N| := abs_mul _ _
        _ ≤ E * S := mul_le_mul hEN hgN (abs_nonneg _) hE0
    have h2 : -(Er M * g M) ≤ E * S := by
      calc -(Er M * g M) ≤ |Er M * g M| := neg_le_abs _
        _ = |Er M| * |g M| := abs_mul _ _
        _ ≤ E * S := mul_le_mul hEM hgM (abs_nonneg _) hE0
    have h3 := neg_abs_le (∑ n ∈ Ico M N, Er n * (g (n + 1) - g n))
    linarith
  -- the main part
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => liIntegrand 0 t) MeasureTheory.volume a b :=
    fun a b => intervalIntegrable_liIntegrand 0 a b
  have hmain : ∑ n ∈ Ioc M N, (Lf n - Lf (n - 1)) * g n ≤
      (1 / q.totient) * (∫ t in (M : ℝ)..N, f t * liIntegrand 0 t) + V / q.totient := by
    have e1 : ∀ n ∈ Ioc M N, (Lf n - Lf (n - 1)) * g n =
        (1 / q.totient) * ∫ t in ((n - 1 : ℕ) : ℝ)..n, liIntegrand 0 t * f n := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      simp only [Lf, g]
      rw [intervalIntegral.integral_mul_const, ← liK_sub_eq n hn1]
      field_simp
    rw [sum_congr rfl e1, ← mul_sum]
    -- `liInt·f(n) = liInt·f(t) + liInt·(f(n) − f(t))`
    have hcomp : ∀ n ∈ Ioc M N, ∫ t in ((n - 1 : ℕ) : ℝ)..n, liIntegrand 0 t * f n ≤
        (∫ t in ((n - 1 : ℕ) : ℝ)..n, f t * liIntegrand 0 t) + ∫ t in ((n - 1 : ℕ) : ℝ)..n, |f n - f t| := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hlo : (M : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ n - 1)
      have hhi : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
      have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      have hfc : ContinuousOn f (Set.Icc ((n - 1 : ℕ) : ℝ) n) := hf.mono (Set.Icc_subset_Icc hlo hhi)
      have i1 : IntervalIntegrable (fun t => f t * liIntegrand 0 t) MeasureTheory.volume ((n - 1 : ℕ) : ℝ) n :=
        (hint _ _).continuousOn_mul (by rw [Set.uIcc_of_le hle]; exact hfc)
      have i2 : IntervalIntegrable (fun t => |f n - f t|) MeasureTheory.volume ((n - 1 : ℕ) : ℝ) n :=
        ((continuousOn_const.sub hfc).abs).intervalIntegrable_of_Icc hle
      rw [← intervalIntegral.integral_add i1 i2]
      refine intervalIntegral.integral_mono_on hle ((hint _ _).mul_const _) (i1.add i2) fun t ht => ?_
      have ht3 : (3 : ℝ) ≤ t := by
        have : (3 : ℝ) ≤ M := by exact_mod_cast hM
        linarith [ht.1]
      have h0 := liIntegrand_nonneg 0 t
      have h1 := liIntegrand_le_one ht3
      have : liIntegrand 0 t * (f n - f t) ≤ |f n - f t| := by
        calc liIntegrand 0 t * (f n - f t) ≤ liIntegrand 0 t * |f n - f t| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) h0
          _ ≤ 1 * |f n - f t| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |f n - f t| := one_mul _
      nlinarith
    have hsumc := sum_le_sum hcomp
    rw [sum_add_distrib] at hsumc
    have hfi : ∀ n ∈ Ioc M N, IntervalIntegrable (fun t => f t * liIntegrand 0 t) MeasureTheory.volume
        ((n - 1 : ℕ) : ℝ) n := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      have hlo : (M : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ n - 1)
      have hhi : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
      have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      exact (hint _ _).continuousOn_mul (by rw [Set.uIcc_of_le hle]; exact hf.mono (Set.Icc_subset_Icc hlo hhi))
    rw [sum_integral_Ioc (fun t => f t * liIntegrand 0 t) M N hMN hfi] at hsumc
    -- `Σ_n ∫_{n−1}^n |f(n) − f(t)| ≤ V`
    have hshift : ∀ n ∈ Ioc M N, ∫ t in ((n - 1 : ℕ) : ℝ)..n, |f n - f t| =
        ∫ s in (0 : ℝ)..1, |f n - f ((n : ℝ) - 1 + s)| := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have := intervalIntegral.integral_comp_add_right (a := 0) (b := 1) (fun t => |f n - f t|) ((n : ℝ) - 1)
      rw [zero_add, show (1 : ℝ) + ((n : ℝ) - 1) = n by ring] at this
      rw [Nat.cast_sub hn1, Nat.cast_one, ← this]
      exact intervalIntegral.integral_congr fun s _ => by ring_nf
    have hcont : ∀ n ∈ Ioc M N, ContinuousOn (fun s => |f n - f ((n : ℝ) - 1 + s)|) (Set.Icc 0 1) := by
      intro n hn
      have hn' := mem_Ioc.mp hn
      refine (continuousOn_const.sub (hf.comp (by fun_prop) fun s hs => ?_)).abs
      have : ((M : ℝ) + 1) ≤ n := by exact_mod_cast (by omega : M + 1 ≤ n)
      have : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hV' : ∑ n ∈ Ioc M N, ∫ t in ((n - 1 : ℕ) : ℝ)..n, |f n - f t| ≤ V := by
      rw [sum_congr rfl hshift, ← intervalIntegral.integral_finsetSum fun n hn =>
        (hcont n hn).intervalIntegrable_of_Icc zero_le_one]
      have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
        (IntervalIntegrable.sum _ fun n hn => (hcont n hn).intervalIntegrable_of_Icc zero_le_one)
        intervalIntegrable_const fun s hs => by rw [Finset.sum_apply]; exact seq_shift hMN hV hs.1 hs.2
      simpa using this
    have h1φ : 0 ≤ 1 / (q.totient : ℝ) := by positivity
    calc 1 / (q.totient : ℝ) * ∑ n ∈ Ioc M N, ∫ t in ((n - 1 : ℕ) : ℝ)..n, liIntegrand 0 t * f n
        ≤ 1 / (q.totient : ℝ) * ((∫ t in (M : ℝ)..N, f t * liIntegrand 0 t) + V) :=
          mul_le_mul_of_nonneg_left (hsumc.trans (by linarith)) h1φ
      _ = _ := by ring
  linarith

end ArcsAlgo.Core
