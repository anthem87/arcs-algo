module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# Riemann sums of unimodal functions

`sum_unimodal`: if `0 ≤ f ≤ F` is continuous, increasing up to `c` and decreasing after, and
`a ≤ c ≤ a + N`, then `|Σ_{i=0}^N f(a + i) − ∫_a^{a+N} f| ≤ 2F`.
-/

open Finset MeasureTheory intervalIntegral

@[expose] public section

namespace ArcsAlgo.LLT

theorem unit_mono {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (h : MonotoneOn f (Set.Icc x (x + 1))) :
    f x ≤ ∫ t in x..x + 1, f t ∧ ∫ t in x..x + 1, f t ≤ f (x + 1) := by
  have hx : x ≤ x + 1 := by linarith
  constructor
  · have := integral_mono_on hx (continuous_const.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _)
      (fun t ht => h ⟨le_refl x, hx⟩ ht ht.1)
    simpa using this
  · have := integral_mono_on hx (hf.intervalIntegrable (μ := volume) _ _) (continuous_const.intervalIntegrable (μ := volume) _ _)
      (fun t ht => h ht ⟨hx, le_refl _⟩ ht.2)
    simpa using this

theorem unit_anti {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (h : AntitoneOn f (Set.Icc x (x + 1))) :
    f (x + 1) ≤ ∫ t in x..x + 1, f t ∧ ∫ t in x..x + 1, f t ≤ f x := by
  have hx : x ≤ x + 1 := by linarith
  constructor
  · have := integral_mono_on hx (continuous_const.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _)
      (fun t ht => h ht ⟨hx, le_refl _⟩ ht.2)
    simpa using this
  · have := integral_mono_on hx (hf.intervalIntegrable (μ := volume) _ _) (continuous_const.intervalIntegrable (μ := volume) _ _)
      (fun t ht => h ⟨le_refl x, hx⟩ ht ht.1)
    simpa using this

theorem integral_split_nat {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) (n : ℕ) :
    ∫ t in a..a + (n + 1 : ℕ), f t = (∫ t in a..a + n, f t) + ∫ t in a + n..a + n + 1, f t := by
  rw [integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _)]
  congr 1; push_cast; ring

theorem sum_mono_le {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) (n : ℕ)
    (h : MonotoneOn f (Set.Icc a (a + n))) :
    ∑ i ∈ range n, f (a + i) ≤ ∫ t in a..a + n, f t ∧
      ∫ t in a..a + n, f t ≤ ∑ i ∈ range n, f (a + i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : MonotoneOn f (Set.Icc a (a + n)) := h.mono (Set.Icc_subset_Icc le_rfl (by push_cast; linarith))
    have hu : MonotoneOn f (Set.Icc (a + n) (a + n + 1)) :=
      h.mono (Set.Icc_subset_Icc (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) (by push_cast; linarith))
    obtain ⟨h1, h2⟩ := ih h'
    obtain ⟨h3, h4⟩ := unit_mono hf hu
    rw [integral_split_nat hf, sum_range_succ, sum_range_succ]
    constructor <;> linarith

theorem sum_anti_le {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) (n : ℕ)
    (h : AntitoneOn f (Set.Icc a (a + n))) :
    ∑ i ∈ range n, f (a + i + 1) ≤ ∫ t in a..a + n, f t ∧
      ∫ t in a..a + n, f t ≤ ∑ i ∈ range n, f (a + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : AntitoneOn f (Set.Icc a (a + n)) := h.mono (Set.Icc_subset_Icc le_rfl (by push_cast; linarith))
    have hu : AntitoneOn f (Set.Icc (a + n) (a + n + 1)) :=
      h.mono (Set.Icc_subset_Icc (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) (by push_cast; linarith))
    obtain ⟨h1, h2⟩ := ih h'
    obtain ⟨h3, h4⟩ := unit_anti hf hu
    rw [integral_split_nat hf, sum_range_succ, sum_range_succ]
    constructor <;> linarith

/-- **Riemann sums of a unimodal function**: if `0 ≤ f ≤ F`, `f` increases up to `c` and decreases
after, and `a ≤ c ≤ a + N`, then `|Σ_{i=0}^N f(a+i) − ∫_a^{a+N} f| ≤ 2F`. -/
theorem sum_unimodal {f : ℝ → ℝ} (hf : Continuous f) {F : ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfF : ∀ x, f x ≤ F) {c : ℝ} (hmono : MonotoneOn f (Set.Iic c)) (hanti : AntitoneOn f (Set.Ici c))
    (a : ℝ) (N : ℕ) (hac : a ≤ c) (hcN : c ≤ a + N) :
    |∑ i ∈ range (N + 1), f (a + i) - ∫ t in a..a + N, f t| ≤ 2 * F := by
  set n := ⌊c - a⌋₊ with hn
  have hn1 : (n : ℝ) ≤ c - a := Nat.floor_le (by linarith)
  have hn2 : c - a < n + 1 := Nat.lt_floor_add_one _
  have hnN : n ≤ N := by
    have : (n : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hF : 0 ≤ F := (hf0 0).trans (hfF 0)
  -- the increasing part
  have hinc := sum_mono_le hf a n (hmono.mono (fun x hx => by simp only [Set.mem_Iic]; linarith [hx.2]))
  rcases Nat.lt_or_ge n N with hlt | hge
  · -- a middle interval and a decreasing part
    set L := N - n - 1
    have hNL : N = n + 1 + L := by omega
    set b : ℝ := a + n + 1
    have hdec := sum_anti_le hf b L (hanti.mono (fun x hx => by
      simp only [Set.mem_Ici]; have := hx.1; simp only [b] at this; linarith))
    have hmid0 : 0 ≤ ∫ t in a + n..a + n + 1, f t :=
      integral_nonneg (by linarith) (fun t _ => hf0 t)
    have hmidF : ∫ t in a + n..a + n + 1, f t ≤ F := by
      have := integral_mono_on (by linarith : a + n ≤ a + n + 1) (hf.intervalIntegrable (μ := volume) _ _)
        (continuous_const.intervalIntegrable (μ := volume) _ _) (fun t _ => hfF t)
      simpa using this
    have hint : ∫ t in a..a + N, f t = (∫ t in a..a + n, f t) + (∫ t in a + n..a + n + 1, f t) +
        ∫ t in b..b + L, f t := by
      rw [integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _),
        integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _)]
      congr 1; simp only [b]; rw [hNL]; push_cast; ring
    have hsum : ∑ i ∈ range (N + 1), f (a + i) = ∑ i ∈ range n, f (a + i) + f (a + n) +
        (f b + ∑ i ∈ range L, f (b + i + 1)) := by
      rw [hNL, show n + 1 + L + 1 = (n + 1) + (L + 1) by ring, sum_range_add, sum_range_succ,
        sum_range_succ']
      simp only [b]; push_cast
      have : ∀ i : ℕ, f (a + ((n : ℝ) + 1 + ((i : ℝ) + 1))) = f (a + n + 1 + i + 1) := fun i => by
        ring_nf
      simp only [this]; ring_nf
    have hsum' : ∑ i ∈ range n, f (a + i + 1) + ∑ i ∈ range L, f (b + i) ≤
        ∑ i ∈ range (N + 1), f (a + i) := by
      rw [hNL, show n + 1 + L + 1 = (n + 1) + (L + 1) by ring, sum_range_add, sum_range_succ']
      have e1 : ∑ i ∈ range n, f (a + i + 1) = ∑ i ∈ range n, f (a + ((i + 1 : ℕ) : ℝ)) := by
        refine sum_congr rfl fun i _ => ?_; push_cast; ring_nf
      have e2 : ∑ i ∈ range L, f (b + i) ≤ ∑ i ∈ range (L + 1), f (a + ((n + 1 + i : ℕ) : ℝ)) := by
        rw [sum_range_succ]
        have : ∑ i ∈ range L, f (b + i) = ∑ i ∈ range L, f (a + ((n + 1 + i : ℕ) : ℝ)) := by
          refine sum_congr rfl fun i _ => ?_; simp only [b]; push_cast; ring_nf
        rw [this]; linarith [hf0 (a + ((n + 1 + L : ℕ) : ℝ))]
      have := hf0 (a + ((0 : ℕ) : ℝ))
      rw [e1]; linarith
    rw [abs_le]; constructor
    · linarith [hfF (a + n), hfF b]
    · linarith [hfF (a + n), hfF b]
  · -- c lies in the last unit: the sum is increasing up to a + N
    have hnN' : n = N := le_antisymm hnN hge
    rw [← hnN']
    rw [sum_range_succ]
    have e1 : ∑ i ∈ range n, f (a + i + 1) ≤ ∑ i ∈ range n, f (a + i) + f (a + n) := by
      have := sum_range_succ' (fun i : ℕ => f (a + i)) n
      have h0 := hf0 (a + ((0 : ℕ) : ℝ))
      simp only [Nat.cast_add, Nat.cast_one] at this
      have e : ∑ i ∈ range n, f (a + i + 1) = ∑ i ∈ range n, f (a + ((i : ℝ) + 1)) := by
        refine sum_congr rfl fun i _ => by ring_nf
      rw [e]; rw [sum_range_succ] at this; linarith
    rw [abs_le]; constructor
    · linarith [hfF (a + n)]
    · linarith [hfF (a + n)]

end ArcsAlgo.LLT
