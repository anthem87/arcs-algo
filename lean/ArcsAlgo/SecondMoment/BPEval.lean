module

public import ArcsAlgo.SecondMoment.BPCumYS
set_option autoImplicit false

/-!
# Proposition B′: the Edgeworth polynomials of the five lattice vectors

From the book's generic `edgeP` (`edgeP_diag`), with the compositions enumerated (`sum_composition`,
`compList`) and the cumulants of `BPCumX`, `BPCumYS`: `P_r(−φ_V)(x) = φ_V(x)·Q_r(x)` with `Q_r` explicit, for
`S = w` (`r ≤ 3`), `Y = (w, εw)` (`r ≤ 3`), `X = (w, εw, ε′w)` (`r ≤ 3`), `X′ = (εw, ε′w)` and `Y′ = εw` (`r = 2, 4`).
-/

open Finset Matrix Polynomial

@[expose] public section

namespace ArcsAlgo.LLT

/-! ### Compositions of small integers -/

/-- The lists of positive integers with sum `n`, by their first part (`f` is a fuel `≥ n`). -/
def compF : ℕ → ℕ → List (List ℕ)
  | 0, n => if n = 0 then [[]] else []
  | _ + 1, 0 => [[]]
  | f + 1, n + 1 => (List.range (n + 1)).flatMap fun k => (compF f (n - k)).map fun l => (k + 1) :: l

def compList (n : ℕ) : List (List ℕ) := compF n n

theorem mem_compF (f n : ℕ) (hf : n ≤ f) (l : List ℕ) :
    l ∈ compF f n ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = n := by
  induction f generalizing n l with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    simp only [compF, if_true, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩
      rcases l with _ | ⟨a, l⟩
      · rfl
      · have := h1 a (by simp); simp at h2; omega
  | succ f ih =>
    rcases n with _ | n
    · simp only [compF, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        rcases l with _ | ⟨a, l⟩
        · rfl
        · have := h1 a (by simp); simp at h2; omega
    · simp only [compF, List.mem_flatMap, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨k, hk, l', hl', rfl⟩
        obtain ⟨h1, h2⟩ := (ih (n - k) (by omega) l').mp hl'
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with h | h
          · omega
          · exact h1 x h
        · simp only [List.sum_cons]; omega
      · rintro ⟨h1, h2⟩
        rcases l with _ | ⟨a, l⟩
        · simp at h2
        · have ha := h1 a (by simp)
          simp only [List.sum_cons] at h2
          refine ⟨a - 1, by omega, l, (ih (n - (a - 1)) (by omega) l).mpr
            ⟨fun x hx => h1 x (by simp [hx]), by omega⟩, ?_⟩
          congr 1; omega

theorem mem_compList (n : ℕ) (l : List ℕ) : l ∈ compList n ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = n :=
  mem_compF n n le_rfl l

theorem sum_composition {β : Type*} [AddCommMonoid β] (n : ℕ) (F : List ℕ → β) :
    ∑ c : Composition n, F c.blocks = ∑ l ∈ (compList n).toFinset, F l := by
  rw [← Finset.sum_image (f := F) (g := Composition.blocks) (s := Finset.univ)
    (fun c _ c' _ h => Composition.ext h)]
  congr 1
  ext l
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset, mem_compList]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨fun x hx => c.blocks_pos hx, c.blocks_sum⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨l, fun hx => h1 _ hx, h2⟩, rfl⟩

example : (compList 3).toFinset = {[1, 1, 1], [1, 2], [2, 1], [3]} := by decide

/-! ### Hermite polynomials -/

theorem herm2 : hermite 2 = X ^ 2 - 1 := by rw [hermite_succ, hermite_one]; simp; ring
theorem herm3 : hermite 3 = X ^ 3 - 3 * X := by rw [hermite_succ, herm2]; simp; ring
theorem herm4 : hermite 4 = X ^ 4 - 6 * X ^ 2 + 3 := by rw [hermite_succ, herm3]; simp; ring
theorem herm5 : hermite 5 = X ^ 5 - 10 * X ^ 3 + 15 * X := by rw [hermite_succ, herm4]; simp; ring
theorem herm6 : hermite 6 = X ^ 6 - 15 * X ^ 4 + 45 * X ^ 2 - 15 := by rw [hermite_succ, herm5]; simp; ring
theorem herm7 : hermite 7 = X ^ 7 - 21 * X ^ 5 + 105 * X ^ 3 - 105 * X := by
  rw [hermite_succ, herm6]; simp; ring
theorem herm8 : hermite 8 = X ^ 8 - 28 * X ^ 6 + 210 * X ^ 4 - 420 * X ^ 2 + 105 := by
  rw [hermite_succ, herm7]; simp; ring
theorem herm9 : hermite 9 = X ^ 9 - 36 * X ^ 7 + 378 * X ^ 5 - 1260 * X ^ 3 + 945 * X := by
  rw [hermite_succ, herm8]; simp; ring

/-- The Hermite polynomials `He_0, …, He_9`, as functions. -/
noncomputable def heP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t
  | 2, t => t ^ 2 - 1
  | 3, t => t ^ 3 - 3 * t
  | 4, t => t ^ 4 - 6 * t ^ 2 + 3
  | 5, t => t ^ 5 - 10 * t ^ 3 + 15 * t
  | 6, t => t ^ 6 - 15 * t ^ 4 + 45 * t ^ 2 - 15
  | 7, t => t ^ 7 - 21 * t ^ 5 + 105 * t ^ 3 - 105 * t
  | 8, t => t ^ 8 - 28 * t ^ 6 + 210 * t ^ 4 - 420 * t ^ 2 + 105
  | 9, t => t ^ 9 - 36 * t ^ 7 + 378 * t ^ 5 - 1260 * t ^ 3 + 945 * t
  | _, _ => 0

/-! ### `S = w`: the Edgeworth polynomials -/

section S

variable {M : ℕ}

theorem cumul_S (hM : 1 ≤ M) (α : Fin 1 → ℕ) : cumul (pS M) (xi1 M) α = cS M (α 0) := by
  rw [cumul_eq, cumL_eq_cS hM, count_alist]

theorem cumul_Y (hM : 1 ≤ M) (α : Fin 2 → ℕ) : cumul (pY M) (xiY M) α = cY M (α 0) (α 1) := by
  rw [cumul_eq, cumL_eq_cY hM, count_alist, count_alist]

theorem cumul_X (hM : 1 ≤ M) (α : Fin 3 → ℕ) : cumul (pX M) (xiX M) α = cX M (α 0) (α 1) (α 2) := by
  rw [cumul_eq, cumL_eq_cX hM, count_alist, count_alist, count_alist]

theorem cumul_Xu (hM : 1 ≤ M) (α : Fin 2 → ℕ) : cumul (pX M) (xiXu M) α = cXu M (α 0) (α 1) := by
  rw [cumul_eq, cumL_eq_cXu hM, count_alist, count_alist]

theorem cumul_Yu (hM : 1 ≤ M) (α : Fin 1 → ℕ) : cumul (pY M) (xiYu M) α = cYu M (α 0) := by
  rw [cumul_eq, cumL_eq_cYu hM, count_alist]

theorem vmean_Xu (hM : 1 ≤ M) : vmean (pX M) (xiXu M) = ![0, 0] := by
  ext j; fin_cases j <;> simp only [vmean] <;> rw [sum_X4]
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiXu, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiXu, sg]; ring)]; simp

theorem vcov_Xu (hM : 1 ≤ M) : vcov (pX M) (xiXu M) = diagonal ![ew2 M, ew2 M] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j k
  simp only [vcov, vmean_Xu hM]
  set c : ℝ := 1 / (4 * M)
  fin_cases j <;> fin_cases k <;> rw [sum_X4]
  · rw [sum_quad _ (4 * c) 0 0 (fun a => by simp [xiXu, sg]; ring)]
    simp [ew2, c]; field_simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiXu, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiXu, sg]; ring)]; simp
  · rw [sum_quad _ (4 * c) 0 0 (fun a => by simp [xiXu, sg]; ring)]
    simp [ew2, c]; field_simp

theorem vmean_Yu (hM : 1 ≤ M) : vmean (pY M) (xiYu M) = ![0] := by
  ext j; fin_cases j; simp only [vmean]; rw [sum_Y2]
  rw [sum_quad _ 0 0 0 (fun a => by simp [xiYu, sg]; ring)]; simp

theorem vcov_Yu (hM : 1 ≤ M) : vcov (pY M) (xiYu M) = diagonal ![ew2 M] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j k
  simp only [vcov, vmean_Yu hM]
  set c : ℝ := 1 / (2 * M)
  fin_cases j; fin_cases k; rw [sum_Y2]
  rw [sum_quad _ (2 * c) 0 0 (fun a => by simp [xiYu, sg]; ring)]
  simp [ew2, c]; field_simp

end S

section Gen

variable {M : ℕ}

set_option maxHeartbeats 4000000 in
theorem edgeP_S1 (hM : 2 ≤ M) (x : Fin 1 → ℝ) :
    edgeP (pS M) (xi1 M) 1 x = gaussDens (vcov (pS M) (xi1 M)) x *
      (cS M 3 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) / 6) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact sig2_pos' hM
  rw [edgeP_diag _ _ _ (vcov_1 hM1) hD, vcov_1 hM1]
  rw [show (∑ c : Composition 1, (1 / (c.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] c.blocks 0 x) =
    ∑ c : Composition 1, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pS M) (xi1 M) ![sig2 M] l 0 x) c.blocks from rfl,
    sum_composition 1 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] l 0 x)]
  rw [show (compList 1).toFinset = {[1]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 1 3 = {![3]} := by decide
  simp [evB, h3, cumul_S hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_S2 (hM : 2 ≤ M) (x : Fin 1 → ℝ) :
    edgeP (pS M) (xi1 M) 2 x = gaussDens (vcov (pS M) (xi1 M)) x *
      (cS M 3 * cS M 3 * (1 / √(sig2 M)) ^ 6 * ((x 0 / √(sig2 M)) ^ 6 - 15 * (x 0 / √(sig2 M)) ^ 4 + 45 * (x 0 / √(sig2 M)) ^ 2 - 15) / 72 +
        cS M 4 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) / 24) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact sig2_pos' hM
  rw [edgeP_diag _ _ _ (vcov_1 hM1) hD, vcov_1 hM1]
  rw [show (∑ c : Composition 2, (1 / (c.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] c.blocks 0 x) =
    ∑ c : Composition 2, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pS M) (xi1 M) ![sig2 M] l 0 x) c.blocks from rfl,
    sum_composition 2 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] l 0 x)]
  rw [show (compList 2).toFinset = {[1, 1], [2]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 1 3 = {![3]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 1 4 = {![4]} := by decide
  simp [evB, h3, h4, cumul_S hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_S3 (hM : 2 ≤ M) (x : Fin 1 → ℝ) :
    edgeP (pS M) (xi1 M) 3 x = gaussDens (vcov (pS M) (xi1 M)) x *
      (cS M 3 * cS M 3 * cS M 3 * (1 / √(sig2 M)) ^ 9 * ((x 0 / √(sig2 M)) ^ 9 - 36 * (x 0 / √(sig2 M)) ^ 7 + 378 * (x 0 / √(sig2 M)) ^ 5 - 1260 * (x 0 / √(sig2 M)) ^ 3 + 945 * (x 0 / √(sig2 M))) / 1296 +
        cS M 3 * cS M 4 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) / 288 +
        cS M 4 * cS M 3 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) / 288 +
        cS M 5 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) / 120) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact sig2_pos' hM
  rw [edgeP_diag _ _ _ (vcov_1 hM1) hD, vcov_1 hM1]
  rw [show (∑ c : Composition 3, (1 / (c.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] c.blocks 0 x) =
    ∑ c : Composition 3, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pS M) (xi1 M) ![sig2 M] l 0 x) c.blocks from rfl,
    sum_composition 3 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pS M) (xi1 M) ![sig2 M] l 0 x)]
  rw [show (compList 3).toFinset = {[1, 1, 1], [1, 2], [2, 1], [3]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 1 3 = {![3]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 1 4 = {![4]} := by decide
  have h5 : Finset.Nat.antidiagonalTuple 1 5 = {![5]} := by decide
  simp [evB, h3, h4, h5, cumul_S hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Y1 (hM : 2 ≤ M) (x : Fin 2 → ℝ) :
    edgeP (pY M) (xiY M) 1 x = gaussDens (vcov (pY M) (xiY M)) x *
      (cY M 1 2 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 2 +
        cY M 3 0 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) / 6) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_Y hM1) hD, vcov_Y hM1]
  rw [show (∑ c : Composition 1, (1 / (c.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 1, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 1 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x)]
  rw [show (compList 1).toFinset = {[1]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 2 3 = {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by decide
  simp [evB, h3, cumul_Y hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cY_odd1 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_two]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Y2 (hM : 2 ≤ M) (x : Fin 2 → ℝ) :
    edgeP (pY M) (xiY M) 2 x = gaussDens (vcov (pY M) (xiY M)) x *
      (cY M 1 2 * cY M 1 2 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 8 +
        cY M 1 2 * cY M 3 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 24 +
        cY M 3 0 * cY M 1 2 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 24 +
        cY M 3 0 * cY M 3 0 * (1 / √(sig2 M)) ^ 6 * ((x 0 / √(sig2 M)) ^ 6 - 15 * (x 0 / √(sig2 M)) ^ 4 + 45 * (x 0 / √(sig2 M)) ^ 2 - 15) * (1 / √(ew2 M)) ^ 0 * (1) / 72 +
        cY M 0 4 * (1 / √(sig2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 24 +
        cY M 2 2 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 4 +
        cY M 4 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) / 24) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_Y hM1) hD, vcov_Y hM1]
  rw [show (∑ c : Composition 2, (1 / (c.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 2, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 2 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x)]
  rw [show (compList 2).toFinset = {[1, 1], [2]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 2 3 = {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 2 4 = {![0, 4], ![1, 3], ![2, 2], ![3, 1], ![4, 0]} := by decide
  simp [evB, h3, h4, cumul_Y hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cY_odd1 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_two]
  ring


set_option maxHeartbeats 4000000 in
theorem edgeP_Y3 (hM : 2 ≤ M) (x : Fin 2 → ℝ) :
    edgeP (pY M) (xiY M) 3 x = gaussDens (vcov (pY M) (xiY M)) x *
      (cY M 1 2 * cY M 1 2 * cY M 1 2 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 48 +
        cY M 1 2 * cY M 1 2 * cY M 3 0 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 144 +
        cY M 1 2 * cY M 3 0 * cY M 1 2 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 144 +
        cY M 1 2 * cY M 3 0 * cY M 3 0 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 432 +
        cY M 3 0 * cY M 1 2 * cY M 1 2 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 144 +
        cY M 3 0 * cY M 1 2 * cY M 3 0 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 432 +
        cY M 3 0 * cY M 3 0 * cY M 1 2 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 432 +
        cY M 3 0 * cY M 3 0 * cY M 3 0 * (1 / √(sig2 M)) ^ 9 * ((x 0 / √(sig2 M)) ^ 9 - 36 * (x 0 / √(sig2 M)) ^ 7 + 378 * (x 0 / √(sig2 M)) ^ 5 - 1260 * (x 0 / √(sig2 M)) ^ 3 + 945 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) / 1296 +
        cY M 1 2 * cY M 0 4 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 96 +
        cY M 1 2 * cY M 2 2 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 16 +
        cY M 1 2 * cY M 4 0 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 96 +
        cY M 3 0 * cY M 0 4 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 288 +
        cY M 3 0 * cY M 2 2 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 48 +
        cY M 3 0 * cY M 4 0 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) / 288 +
        cY M 0 4 * cY M 1 2 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 96 +
        cY M 0 4 * cY M 3 0 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 288 +
        cY M 2 2 * cY M 1 2 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 16 +
        cY M 2 2 * cY M 3 0 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 48 +
        cY M 4 0 * cY M 1 2 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 96 +
        cY M 4 0 * cY M 3 0 * (1 / √(sig2 M)) ^ 7 * ((x 0 / √(sig2 M)) ^ 7 - 21 * (x 0 / √(sig2 M)) ^ 5 + 105 * (x 0 / √(sig2 M)) ^ 3 - 105 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) / 288 +
        cY M 1 4 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 24 +
        cY M 3 2 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 12 +
        cY M 5 0 * (1 / √(sig2 M)) ^ 5 * ((x 0 / √(sig2 M)) ^ 5 - 10 * (x 0 / √(sig2 M)) ^ 3 + 15 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) / 120) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_Y hM1) hD, vcov_Y hM1]
  rw [show (∑ c : Composition 3, (1 / (c.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 3, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 3 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pY M) (xiY M) ![sig2 M, ew2 M] l 0 x)]
  rw [show (compList 3).toFinset = {[1, 1, 1], [1, 2], [2, 1], [3]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 2 3 = {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 2 4 = {![0, 4], ![1, 3], ![2, 2], ![3, 1], ![4, 0]} := by decide
  have h5 : Finset.Nat.antidiagonalTuple 2 5 = {![0, 5], ![1, 4], ![2, 3], ![3, 2], ![4, 1], ![5, 0]} := by decide
  simp [evB, h3, h4, h5, cumul_Y hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cY_odd1 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_two]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_X1 (hM : 2 ≤ M) (x : Fin 3 → ℝ) :
    edgeP (pX M) (xiX M) 1 x = gaussDens (vcov (pX M) (xiX M)) x *
      (cX M 1 0 2 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 2 +
        cX M 1 2 0 * (1 / √(sig2 M)) ^ 1 * ((x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) / 2 +
        cX M 3 0 0 * (1 / √(sig2 M)) ^ 3 * ((x 0 / √(sig2 M)) ^ 3 - 3 * (x 0 / √(sig2 M))) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 0 * (1) / 6) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M, ew2 M] : Fin 3 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_X hM1) hD, vcov_X hM1]
  rw [show (∑ c : Composition 1, (1 / (c.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 1, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 1 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x)]
  rw [show (compList 1).toFinset = {[1]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 3 3 = {![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0]} := by decide
  simp [evB, h3, cumul_X hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cX_odd1 hM1, cX_odd2 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_three]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_X2 (hM : 2 ≤ M) (x : Fin 3 → ℝ) :
    edgeP (pX M) (xiX M) 2 x = gaussDens (vcov (pX M) (xiX M)) x *
      (cX M 1 0 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 4 * ((x 2 / √(ew2 M)) ^ 4 - 6 * (x 2 / √(ew2 M)) ^ 2 + 3) / 8 +
        cX M 1 0 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 8 +
        cX M 1 0 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 24 +
        cX M 1 2 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 8 +
        cX M 1 2 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) / 8 +
        cX M 1 2 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) / 24 +
        cX M 3 0 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 24 +
        cX M 3 0 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) / 24 +
        cX M 3 0 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ 6 * ((x 0 / √(sig2 M)) ^ 6 - 15 * (x 0 / √(sig2 M)) ^ 4 + 45 * (x 0 / √(sig2 M)) ^ 2 - 15) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 0 * (1) / 72 +
        cX M 0 0 4 * (1 / √(sig2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 4 * ((x 2 / √(ew2 M)) ^ 4 - 6 * (x 2 / √(ew2 M)) ^ 2 + 3) / 24 +
        cX M 0 2 2 * (1 / √(sig2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 4 +
        cX M 0 4 0 * (1 / √(sig2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) / 24 +
        cX M 2 0 2 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 2 * ((x 2 / √(ew2 M)) ^ 2 - 1) / 4 +
        cX M 2 2 0 * (1 / √(sig2 M)) ^ 2 * ((x 0 / √(sig2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 0 * (1) / 4 +
        cX M 4 0 0 * (1 / √(sig2 M)) ^ 4 * ((x 0 / √(sig2 M)) ^ 4 - 6 * (x 0 / √(sig2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 0 * (1) / 24) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M, ew2 M] : Fin 3 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_X hM1) hD, vcov_X hM1]
  rw [show (∑ c : Composition 2, (1 / (c.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 2, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 2 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x)]
  rw [show (compList 2).toFinset = {[1, 1], [2]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 3 3 = {![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 3 4 = {![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]} := by decide
  simp [evB, h3, h4, cumul_X hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cX_odd1 hM1, cX_odd2 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_three]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Xu2 (hM : 2 ≤ M) (x : Fin 2 → ℝ) :
    edgeP (pX M) (xiXu M) 2 x = gaussDens (vcov (pX M) (xiXu M)) x *
      (cXu M 0 4 * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 24 +
        cXu M 2 2 * (1 / √(ew2 M)) ^ 2 * ((x 0 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 4 +
        cXu M 4 0 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 0 * (1) / 24) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_Xu hM1) hD, vcov_Xu hM1]
  rw [show (∑ c : Composition 2, (1 / (c.length.factorial : ℝ)) * evB (pX M) (xiXu M) ![ew2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 2, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pX M) (xiXu M) ![ew2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 2 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pX M) (xiXu M) ![ew2 M, ew2 M] l 0 x)]
  rw [show (compList 2).toFinset = {[1, 1], [2]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 2 3 = {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 2 4 = {![0, 4], ![1, 3], ![2, 2], ![3, 1], ![4, 0]} := by decide
  simp [evB, h3, h4, cumul_Xu hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cXu_odd0 hM1, cXu_odd1 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_two]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Xu4 (hM : 2 ≤ M) (x : Fin 2 → ℝ) :
    edgeP (pX M) (xiXu M) 4 x = gaussDens (vcov (pX M) (xiXu M)) x *
      (cXu M 0 4 * cXu M 0 4 * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 8 * ((x 1 / √(ew2 M)) ^ 8 - 28 * (x 1 / √(ew2 M)) ^ 6 + 210 * (x 1 / √(ew2 M)) ^ 4 - 420 * (x 1 / √(ew2 M)) ^ 2 + 105) / 1152 +
        cXu M 0 4 * cXu M 2 2 * (1 / √(ew2 M)) ^ 2 * ((x 0 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 192 +
        cXu M 0 4 * cXu M 4 0 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 1152 +
        cXu M 2 2 * cXu M 0 4 * (1 / √(ew2 M)) ^ 2 * ((x 0 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 192 +
        cXu M 2 2 * cXu M 2 2 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 32 +
        cXu M 2 2 * cXu M 4 0 * (1 / √(ew2 M)) ^ 6 * ((x 0 / √(ew2 M)) ^ 6 - 15 * (x 0 / √(ew2 M)) ^ 4 + 45 * (x 0 / √(ew2 M)) ^ 2 - 15) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 192 +
        cXu M 4 0 * cXu M 0 4 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 1152 +
        cXu M 4 0 * cXu M 2 2 * (1 / √(ew2 M)) ^ 6 * ((x 0 / √(ew2 M)) ^ 6 - 15 * (x 0 / √(ew2 M)) ^ 4 + 45 * (x 0 / √(ew2 M)) ^ 2 - 15) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 192 +
        cXu M 4 0 * cXu M 4 0 * (1 / √(ew2 M)) ^ 8 * ((x 0 / √(ew2 M)) ^ 8 - 28 * (x 0 / √(ew2 M)) ^ 6 + 210 * (x 0 / √(ew2 M)) ^ 4 - 420 * (x 0 / √(ew2 M)) ^ 2 + 105) * (1 / √(ew2 M)) ^ 0 * (1) / 1152 +
        cXu M 0 6 * (1 / √(ew2 M)) ^ 0 * (1) * (1 / √(ew2 M)) ^ 6 * ((x 1 / √(ew2 M)) ^ 6 - 15 * (x 1 / √(ew2 M)) ^ 4 + 45 * (x 1 / √(ew2 M)) ^ 2 - 15) / 720 +
        cXu M 2 4 * (1 / √(ew2 M)) ^ 2 * ((x 0 / √(ew2 M)) ^ 2 - 1) * (1 / √(ew2 M)) ^ 4 * ((x 1 / √(ew2 M)) ^ 4 - 6 * (x 1 / √(ew2 M)) ^ 2 + 3) / 48 +
        cXu M 4 2 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) * (1 / √(ew2 M)) ^ 2 * ((x 1 / √(ew2 M)) ^ 2 - 1) / 48 +
        cXu M 6 0 * (1 / √(ew2 M)) ^ 6 * ((x 0 / √(ew2 M)) ^ 6 - 15 * (x 0 / √(ew2 M)) ^ 4 + 45 * (x 0 / √(ew2 M)) ^ 2 - 15) * (1 / √(ew2 M)) ^ 0 * (1) / 720) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M, ew2 M] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_Xu hM1) hD, vcov_Xu hM1]
  rw [show (∑ c : Composition 4, (1 / (c.length.factorial : ℝ)) * evB (pX M) (xiXu M) ![ew2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 4, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pX M) (xiXu M) ![ew2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 4 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pX M) (xiXu M) ![ew2 M, ew2 M] l 0 x)]
  rw [show (compList 4).toFinset = {[1, 1, 1, 1], [1, 1, 2], [1, 2, 1], [1, 3], [2, 1, 1], [2, 2], [3, 1], [4]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 2 3 = {![0, 3], ![1, 2], ![2, 1], ![3, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 2 4 = {![0, 4], ![1, 3], ![2, 2], ![3, 1], ![4, 0]} := by decide
  have h5 : Finset.Nat.antidiagonalTuple 2 5 = {![0, 5], ![1, 4], ![2, 3], ![3, 2], ![4, 1], ![5, 0]} := by decide
  have h6 : Finset.Nat.antidiagonalTuple 2 6 = {![0, 6], ![1, 5], ![2, 4], ![3, 3], ![4, 2], ![5, 1], ![6, 0]} := by decide
  simp [evB, h3, h4, h5, h6, cumul_Xu hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cXu_odd0 hM1, cXu_odd1 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_two]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Yu2 (hM : 2 ≤ M) (x : Fin 1 → ℝ) :
    edgeP (pY M) (xiYu M) 2 x = gaussDens (vcov (pY M) (xiYu M)) x *
      (cYu M 4 * (1 / √(ew2 M)) ^ 4 * ((x 0 / √(ew2 M)) ^ 4 - 6 * (x 0 / √(ew2 M)) ^ 2 + 3) / 24) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact ew2_pos M
  rw [edgeP_diag _ _ _ (vcov_Yu hM1) hD, vcov_Yu hM1]
  rw [show (∑ c : Composition 2, (1 / (c.length.factorial : ℝ)) * evB (pY M) (xiYu M) ![ew2 M] c.blocks 0 x) =
    ∑ c : Composition 2, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pY M) (xiYu M) ![ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 2 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pY M) (xiYu M) ![ew2 M] l 0 x)]
  rw [show (compList 2).toFinset = {[1, 1], [2]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 1 3 = {![3]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 1 4 = {![4]} := by decide
  simp [evB, h3, h4, cumul_Yu hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cYu_odd hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9]
  ring

set_option maxHeartbeats 4000000 in
theorem edgeP_Yu4 (hM : 2 ≤ M) (x : Fin 1 → ℝ) :
    edgeP (pY M) (xiYu M) 4 x = gaussDens (vcov (pY M) (xiYu M)) x *
      (cYu M 4 * cYu M 4 * (1 / √(ew2 M)) ^ 8 * ((x 0 / √(ew2 M)) ^ 8 - 28 * (x 0 / √(ew2 M)) ^ 6 + 210 * (x 0 / √(ew2 M)) ^ 4 - 420 * (x 0 / √(ew2 M)) ^ 2 + 105) / 1152 +
        cYu M 6 * (1 / √(ew2 M)) ^ 6 * ((x 0 / √(ew2 M)) ^ 6 - 15 * (x 0 / √(ew2 M)) ^ 4 + 45 * (x 0 / √(ew2 M)) ^ 2 - 15) / 720) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![ew2 M] : Fin 1 → ℝ) i := fun i => by fin_cases i; exact ew2_pos M
  rw [edgeP_diag _ _ _ (vcov_Yu hM1) hD, vcov_Yu hM1]
  rw [show (∑ c : Composition 4, (1 / (c.length.factorial : ℝ)) * evB (pY M) (xiYu M) ![ew2 M] c.blocks 0 x) =
    ∑ c : Composition 4, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pY M) (xiYu M) ![ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 4 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pY M) (xiYu M) ![ew2 M] l 0 x)]
  rw [show (compList 4).toFinset = {[1, 1, 1, 1], [1, 1, 2], [1, 2, 1], [1, 3], [2, 1, 1], [2, 2], [3, 1], [4]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 1 3 = {![3]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 1 4 = {![4]} := by decide
  have h5 : Finset.Nat.antidiagonalTuple 1 5 = {![5]} := by decide
  have h6 : Finset.Nat.antidiagonalTuple 1 6 = {![6]} := by decide
  simp [evB, h3, h4, h5, h6, cumul_Yu hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, cYu_odd hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9]
  ring


set_option maxHeartbeats 4000000 in
theorem edgeP_X3 (hM : 2 ≤ M) (x : Fin 3 → ℝ) :
    edgeP (pX M) (xiX M) 3 x = gaussDens (vcov (pX M) (xiX M)) x *
      (cX M 1 0 2 * cX M 1 0 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 2 / √(ew2 M)) / 48 +
        cX M 1 0 2 * cX M 1 0 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 48 +
        cX M 1 0 2 * cX M 1 0 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 144 +
        cX M 1 0 2 * cX M 1 2 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 48 +
        cX M 1 0 2 * cX M 1 2 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 1 0 2 * cX M 1 2 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 1 0 2 * cX M 3 0 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 144 +
        cX M 1 0 2 * cX M 3 0 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 1 0 2 * cX M 3 0 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 432 +
        cX M 1 2 0 * cX M 1 0 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 48 +
        cX M 1 2 0 * cX M 1 0 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 1 2 0 * cX M 1 0 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 1 2 0 * cX M 1 2 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 1 2 0 * cX M 1 2 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 48 +
        cX M 1 2 0 * cX M 1 2 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 144 +
        cX M 1 2 0 * cX M 3 0 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 1 2 0 * cX M 3 0 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 144 +
        cX M 1 2 0 * cX M 3 0 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 432 +
        cX M 3 0 0 * cX M 1 0 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 144 +
        cX M 3 0 0 * cX M 1 0 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 3 0 0 * cX M 1 0 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 432 +
        cX M 3 0 0 * cX M 1 2 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 144 +
        cX M 3 0 0 * cX M 1 2 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 144 +
        cX M 3 0 0 * cX M 1 2 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 432 +
        cX M 3 0 0 * cX M 3 0 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 432 +
        cX M 3 0 0 * cX M 3 0 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 432 +
        cX M 3 0 0 * cX M 3 0 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (9 : ℕ) * heP 9 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 1296 +
        cX M 1 0 2 * cX M 0 0 4 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 2 / √(ew2 M)) / 96 +
        cX M 1 0 2 * cX M 0 2 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 16 +
        cX M 1 0 2 * cX M 0 4 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 96 +
        cX M 1 0 2 * cX M 2 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 16 +
        cX M 1 0 2 * cX M 2 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 1 0 2 * cX M 4 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 96 +
        cX M 1 2 0 * cX M 0 0 4 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 96 +
        cX M 1 2 0 * cX M 0 2 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 1 2 0 * cX M 0 4 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 96 +
        cX M 1 2 0 * cX M 2 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 1 2 0 * cX M 2 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 16 +
        cX M 1 2 0 * cX M 4 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 96 +
        cX M 3 0 0 * cX M 0 0 4 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 288 +
        cX M 3 0 0 * cX M 0 2 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 3 0 0 * cX M 0 4 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 288 +
        cX M 3 0 0 * cX M 2 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 3 0 0 * cX M 2 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 48 +
        cX M 3 0 0 * cX M 4 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 288 +
        cX M 0 0 4 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 2 / √(ew2 M)) / 96 +
        cX M 0 0 4 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 96 +
        cX M 0 0 4 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 288 +
        cX M 0 2 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 16 +
        cX M 0 2 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 0 2 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 0 4 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 96 +
        cX M 0 4 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (6 : ℕ) * heP 6 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 96 +
        cX M 0 4 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 288 +
        cX M 2 0 2 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 16 +
        cX M 2 0 2 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 2 0 2 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 48 +
        cX M 2 2 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 16 +
        cX M 2 2 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 16 +
        cX M 2 2 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 48 +
        cX M 4 0 0 * cX M 1 0 2 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 96 +
        cX M 4 0 0 * cX M 1 2 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 96 +
        cX M 4 0 0 * cX M 3 0 0 * (1 / √(sig2 M)) ^ (7 : ℕ) * heP 7 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 288 +
        cX M 1 0 4 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 2 / √(ew2 M)) / 24 +
        cX M 1 2 2 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 4 +
        cX M 1 4 0 * (1 / √(sig2 M)) ^ (1 : ℕ) * heP 1 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (4 : ℕ) * heP 4 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 24 +
        cX M 3 0 2 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 2 / √(ew2 M)) / 12 +
        cX M 3 2 0 * (1 / √(sig2 M)) ^ (3 : ℕ) * heP 3 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (2 : ℕ) * heP 2 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 12 +
        cX M 5 0 0 * (1 / √(sig2 M)) ^ (5 : ℕ) * heP 5 (x 0 / √(sig2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 1 / √(ew2 M)) * (1 / √(ew2 M)) ^ (0 : ℕ) * heP 0 (x 2 / √(ew2 M)) / 120) := by
  have hM1 : 1 ≤ M := by omega
  have hD : ∀ i, 0 < (![sig2 M, ew2 M, ew2 M] : Fin 3 → ℝ) i := fun i => by
    fin_cases i <;> simp [sig2_pos' hM, ew2_pos]
  rw [edgeP_diag _ _ _ (vcov_X hM1) hD, vcov_X hM1]
  rw [show (∑ c : Composition 3, (1 / (c.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] c.blocks 0 x) =
    ∑ c : Composition 3, (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) *
      evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x) c.blocks from rfl,
    sum_composition 3 (fun l : List ℕ => (1 / (l.length.factorial : ℝ)) * evB (pX M) (xiX M) ![sig2 M, ew2 M, ew2 M] l 0 x)]
  rw [show (compList 3).toFinset = {[1, 1, 1], [1, 2], [2, 1], [3]} by decide]
  have h3 : Finset.Nat.antidiagonalTuple 3 3 = {![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0]} := by decide
  have h4 : Finset.Nat.antidiagonalTuple 3 4 = {![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]} := by decide
  have h5 : Finset.Nat.antidiagonalTuple 3 5 = {![0, 0, 5], ![0, 1, 4], ![0, 2, 3], ![0, 3, 2], ![0, 4, 1], ![0, 5, 0], ![1, 0, 4], ![1, 1, 3], ![1, 2, 2], ![1, 3, 1], ![1, 4, 0], ![2, 0, 3], ![2, 1, 2], ![2, 2, 1], ![2, 3, 0], ![3, 0, 2], ![3, 1, 1], ![3, 2, 0], ![4, 0, 1], ![4, 1, 0], ![5, 0, 0]} := by decide
  simp [evB, h3, h4, h5, cumul_X hM1, Tg_eval hD, mfact, Nat.factorial, Nat.odd_iff, heP, cX_odd1 hM1, cX_odd2 hM1, herm2, herm3, herm4, herm5, herm6, herm7, herm8, herm9, Fin.prod_univ_three]
  ring


-- GENERATED

end Gen

end ArcsAlgo.LLT
