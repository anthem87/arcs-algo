module

public import ArcsAlgo.SecondMoment.BR22
public import ArcsAlgo.LocalLimit.CharFun
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.StarOrdered
set_option autoImplicit false

/-!
# The lattice vectors of Proposition B′ satisfy the hypotheses of [BR, §22] (paper §6.3)

For weights uniform in `{1, …, M}`, `M ≥ 2`, and independent uniform signs `ε, ε′`:

* `X = (w, εw, ε′w)`, `Y = (w, εw)` and `w` are given as laws on finite parameter spaces with
  uniform weights, so the copies are independent by construction (`lawPow`).
* Minimal lattices (`minLat_X`, `minLat_Y`, `minLat_1`): `{a ≡ b ≡ c (mod 2)}` of index 4
  (`index_parX`), `{a ≡ b (mod 2)}` of index 2 (`index_parY`), and `ℤ` (index 1).
* Means and covariances (`vmean_X`, `vcov_X`, …): mean `(μ, 0, 0)`, covariance
  `diag(σ², Ew², Ew²)`, non-degenerate (`posDef_X`, `posDef_Y`, `posDef_1`). The vectors are
  bounded, so all moments are finite.
* The conditioning on `S_E` is turned into unconditioned local probabilities
  (`card_Y`, `card_X`, `card_1`): `Σ_{S_E = s} Z(u) = #{(w, ε) : ΣY = (s, u)}` and
  `Σ_{S_E = s} Z(u)² = #{(w, ε, ε′) : ΣX = (s, u, u)}`.
-/

open Finset Matrix

@[expose] public section

namespace ArcsAlgo.LLT

def sg (b : Bool) : ℤ := if b then 1 else -1

/-- The vector `X = (w, εw, ε′w)` of Proposition B′. -/
def xiX (M : ℕ) (a : Fin M × Bool × Bool) : Fin 3 → ℤ :=
  ![(a.1 : ℤ) + 1, sg a.2.1 * ((a.1 : ℤ) + 1), sg a.2.2 * ((a.1 : ℤ) + 1)]

/-- The lattice `{a ≡ b ≡ c (mod 2)}`, as the kernel of the parities of `b − a` and `c − a`. -/
def parX : (Fin 3 → ℤ) →+ ZMod 2 × ZMod 2 where
  toFun v := (((v 1 - v 0 : ℤ) : ZMod 2), ((v 2 - v 0 : ℤ) : ZMod 2))
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply, Prod.mk_add_mk]; push_cast; ring_nf

theorem parX_surj : Function.Surjective parX := by
  rintro ⟨x, y⟩
  refine ⟨![0, (x.val : ℤ), (y.val : ℤ)], ?_⟩
  simp [parX]

theorem index_parX : parX.ker.index = 4 := by
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ parX_surj]
  simp [Nat.card_eq_fintype_card]

theorem mem_ker_parX (v : Fin 3 → ℤ) :
    v ∈ parX.ker ↔ (2 : ℤ) ∣ v 1 - v 0 ∧ (2 : ℤ) ∣ v 2 - v 0 := by
  simp only [AddMonoidHom.mem_ker, parX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_eq_zero]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]


def xiY (M : ℕ) (a : Fin M × Bool) : Fin 2 → ℤ :=
  ![(a.1 : ℤ) + 1, sg a.2 * ((a.1 : ℤ) + 1)]

def xi1 (M : ℕ) (a : Fin M) : Fin 1 → ℤ := ![(a : ℤ) + 1]

def parY : (Fin 2 → ℤ) →+ ZMod 2 where
  toFun v := ((v 1 - v 0 : ℤ) : ZMod 2)
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply]; push_cast; ring_nf

theorem parY_surj : Function.Surjective parY := by
  intro x
  refine ⟨![0, (x.val : ℤ)], ?_⟩
  simp [parY]

theorem index_parY : parY.ker.index = 2 := by
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ parY_surj]
  simp [Nat.card_eq_fintype_card]

theorem mem_ker_parY (v : Fin 2 → ℤ) : v ∈ parY.ker ↔ (2 : ℤ) ∣ v 1 - v 0 := by
  simp only [AddMonoidHom.mem_ker, parY, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

theorem sg_mul_sub (b : Bool) (w : ℤ) : (2 : ℤ) ∣ sg b * w - w := by
  cases b <;> simp [sg] <;> omega

theorem closure_X {M : ℕ} (hM : 2 ≤ M) :
    AddSubgroup.closure {v | ∃ a b : Fin M × Bool × Bool, v = xiX M a - xiX M b} = parX.ker := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro v ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, mem_ker_parX]
    have h1 := sg_mul_sub a.2.1 ((a.1 : ℤ) + 1)
    have h2 := sg_mul_sub b.2.1 ((b.1 : ℤ) + 1)
    have h3 := sg_mul_sub a.2.2 ((a.1 : ℤ) + 1)
    have h4 := sg_mul_sub b.2.2 ((b.1 : ℤ) + 1)
    simp only [xiX, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    constructor <;> omega
  · intro v hv
    rw [mem_ker_parX] at hv
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hv
    set S := {v | ∃ a b : Fin M × Bool × Bool, v = xiX M a - xiX M b}
    have i0 : (0 : ℕ) < M := by omega
    have i1 : (1 : ℕ) < M := by omega
    have g1 : ![1, 1, 1] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨1, i1⟩, true, true), (⟨0, i0⟩, true, true), by ext j; fin_cases j <;> simp [xiX, sg]⟩
    have g2 : ![0, 2, 0] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨0, i0⟩, true, true), (⟨0, i0⟩, false, true), by ext j; fin_cases j <;> simp [xiX, sg]⟩
    have g3 : ![0, 0, 2] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨0, i0⟩, true, true), (⟨0, i0⟩, true, false), by ext j; fin_cases j <;> simp [xiX, sg]⟩
    have : v = v 0 • ![1, 1, 1] + k • ![0, 2, 0] + l • ![0, 0, 2] := by
      ext j; fin_cases j <;> simp <;> omega
    rw [this]
    exact add_mem (add_mem (AddSubgroup.zsmul_mem _ g1 _) (AddSubgroup.zsmul_mem _ g2 _))
      (AddSubgroup.zsmul_mem _ g3 _)

theorem closure_Y {M : ℕ} (hM : 2 ≤ M) :
    AddSubgroup.closure {v | ∃ a b : Fin M × Bool, v = xiY M a - xiY M b} = parY.ker := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro v ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, mem_ker_parY]
    have h1 := sg_mul_sub a.2 ((a.1 : ℤ) + 1)
    have h2 := sg_mul_sub b.2 ((b.1 : ℤ) + 1)
    simp only [xiY, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    omega
  · intro v hv
    rw [mem_ker_parY] at hv
    obtain ⟨k, hk⟩ := hv
    set S := {v | ∃ a b : Fin M × Bool, v = xiY M a - xiY M b}
    have i0 : (0 : ℕ) < M := by omega
    have i1 : (1 : ℕ) < M := by omega
    have g1 : ![1, 1] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨1, i1⟩, true), (⟨0, i0⟩, true), by ext j; fin_cases j <;> simp [xiY, sg]⟩
    have g2 : ![0, 2] ∈ AddSubgroup.closure S := AddSubgroup.subset_closure
      ⟨(⟨0, i0⟩, true), (⟨0, i0⟩, false), by ext j; fin_cases j <;> simp [xiY, sg]⟩
    have : v = v 0 • ![1, 1] + k • ![0, 2] := by
      ext j; fin_cases j <;> simp <;> omega
    rw [this]
    exact add_mem (AddSubgroup.zsmul_mem _ g1 _) (AddSubgroup.zsmul_mem _ g2 _)

theorem closure_1 {M : ℕ} (hM : 2 ≤ M) :
    AddSubgroup.closure {v | ∃ a b : Fin M, v = xi1 M a - xi1 M b} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have i0 : (0 : ℕ) < M := by omega
  have i1 : (1 : ℕ) < M := by omega
  have g1 : ![1] ∈ AddSubgroup.closure {v | ∃ a b : Fin M, v = xi1 M a - xi1 M b} :=
    AddSubgroup.subset_closure ⟨⟨1, i1⟩, ⟨0, i0⟩, by ext j; fin_cases j; simp [xi1]⟩
  have : v = v 0 • ![1] := by ext j; fin_cases j; simp
  rw [this]; exact AddSubgroup.zsmul_mem _ g1 _


theorem sum_w (M : ℕ) : ∑ a : Fin M, ((a : ℝ) + 1) = (M : ℝ) * (M + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) + 1)]
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_w2 (M : ℕ) : ∑ a : Fin M, ((a : ℝ) + 1) ^ 2 = (M : ℝ) * (M + 1) * (2 * M + 1) / 6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) ^ 2)]
  induction M with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sums over `Fin M` of a quadratic in `w = a + 1`. -/
theorem sum_quad {M : ℕ} (f : Fin M → ℝ) (α β γ : ℝ)
    (hf : ∀ a, f a = α * ((a : ℝ) + 1) ^ 2 + β * ((a : ℝ) + 1) + γ) :
    ∑ a, f a = α * ((M : ℝ) * (M + 1) * (2 * M + 1) / 6) + β * ((M : ℝ) * (M + 1) / 2) + γ * M := by
  simp only [hf]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_w, sum_w2]
  simp; ring

theorem sum_X4 {M : ℕ} (g : Fin M × Bool × Bool → ℝ) :
    ∑ a, g a = ∑ a : Fin M, (g (a, true, true) + g (a, true, false) + g (a, false, true) +
      g (a, false, false)) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]; ring

noncomputable def ew2 (M : ℕ) : ℝ := ((M : ℝ) + 1) * (2 * M + 1) / 6

theorem vmean_X {M : ℕ} (hM : 1 ≤ M) :
    vmean (fun _ => (1 / (4 * M) : ℝ)) (xiX M) = ![((M : ℝ) + 1) / 2, 0, 0] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j; fin_cases j <;> simp only [vmean] <;> rw [sum_X4]
  · rw [sum_quad _ 0 (4 / (4 * M)) 0 (fun a => by simp [xiX, sg]; ring)]
    simp; field_simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp

theorem vcov_X {M : ℕ} (hM : 1 ≤ M) :
    vcov (fun _ => (1 / (4 * M) : ℝ)) (xiX M) = diagonal ![sig2 M, ew2 M, ew2 M] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j k
  simp only [vcov, vmean_X hM]
  set c : ℝ := 1 / (4 * M)
  set μ : ℝ := ((M : ℝ) + 1) / 2
  fin_cases j <;> fin_cases k <;> rw [sum_X4]
  · rw [sum_quad _ (4 * c) (-8 * c * μ) (4 * c * μ ^ 2) (fun a => by simp [xiX, sg]; ring)]
    simp [sig2, c, μ]; field_simp; ring
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ (4 * c) 0 0 (fun a => by simp [xiX, sg]; ring)]
    simp [ew2, c]; field_simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiX, sg]; ring)]; simp
  · rw [sum_quad _ (4 * c) 0 0 (fun a => by simp [xiX, sg]; ring)]
    simp [ew2, c]; field_simp


theorem sum_Y2 {M : ℕ} (g : Fin M × Bool → ℝ) :
    ∑ a, g a = ∑ a : Fin M, (g (a, true) + g (a, false)) := by
  rw [Fintype.sum_prod_type]; simp

theorem vmean_Y {M : ℕ} (hM : 1 ≤ M) :
    vmean (fun _ => (1 / (2 * M) : ℝ)) (xiY M) = ![((M : ℝ) + 1) / 2, 0] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j; fin_cases j <;> simp only [vmean] <;> rw [sum_Y2]
  · rw [sum_quad _ 0 (2 / (2 * M)) 0 (fun a => by simp [xiY, sg]; ring)]
    simp; field_simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiY, sg]; ring)]; simp

theorem vcov_Y {M : ℕ} (hM : 1 ≤ M) :
    vcov (fun _ => (1 / (2 * M) : ℝ)) (xiY M) = diagonal ![sig2 M, ew2 M] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j k
  simp only [vcov, vmean_Y hM]
  set c : ℝ := 1 / (2 * M)
  set μ : ℝ := ((M : ℝ) + 1) / 2
  fin_cases j <;> fin_cases k <;> rw [sum_Y2]
  · rw [sum_quad _ (2 * c) (-4 * c * μ) (2 * c * μ ^ 2) (fun a => by simp [xiY, sg]; ring)]
    simp [sig2, c, μ]; field_simp; ring
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiY, sg]; ring)]; simp
  · rw [sum_quad _ 0 0 0 (fun a => by simp [xiY, sg]; ring)]; simp
  · rw [sum_quad _ (2 * c) 0 0 (fun a => by simp [xiY, sg]; ring)]
    simp [ew2, c]; field_simp

theorem vmean_1 {M : ℕ} (hM : 1 ≤ M) :
    vmean (fun _ => (1 / M : ℝ)) (xi1 M) = ![((M : ℝ) + 1) / 2] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j; fin_cases j; simp only [vmean]
  rw [sum_quad _ 0 (1 / M) 0 (fun a => by simp [xi1])]
  simp; field_simp

theorem vcov_1 {M : ℕ} (hM : 1 ≤ M) :
    vcov (fun _ => (1 / M : ℝ)) (xi1 M) = diagonal ![sig2 M] := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  ext j k
  simp only [vcov, vmean_1 hM]
  set c : ℝ := 1 / M
  set μ : ℝ := ((M : ℝ) + 1) / 2
  fin_cases j; fin_cases k
  rw [sum_quad _ c (-2 * c * μ) (c * μ ^ 2) (fun a => by simp [xi1]; ring)]
  simp [sig2, c, μ]; field_simp; ring

theorem sig2_pos' {M : ℕ} (hM : 2 ≤ M) : 0 < sig2 M := by
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sig2; nlinarith

theorem ew2_pos (M : ℕ) : 0 < ew2 M := by unfold ew2; positivity

theorem posDef_X {M : ℕ} (hM : 2 ≤ M) :
    (vcov (fun _ => (1 / (4 * M) : ℝ)) (xiX M)).PosDef := by
  rw [vcov_X (by omega), posDef_diagonal_iff]
  intro i; fin_cases i <;> simp [sig2_pos' hM, ew2_pos]

theorem posDef_Y {M : ℕ} (hM : 2 ≤ M) :
    (vcov (fun _ => (1 / (2 * M) : ℝ)) (xiY M)).PosDef := by
  rw [vcov_Y (by omega), posDef_diagonal_iff]
  intro i; fin_cases i <;> simp [sig2_pos' hM, ew2_pos]

theorem posDef_1 {M : ℕ} (hM : 2 ≤ M) :
    (vcov (fun _ => (1 / M : ℝ)) (xi1 M)).PosDef := by
  rw [vcov_1 (by omega), posDef_diagonal_iff]
  intro i; fin_cases i; simp [sig2_pos' hM]

theorem minLat_const {Ω : Type} {d : ℕ} {c : ℝ} (hc : 0 < c) (ξ : Ω → Fin d → ℤ) :
    minLat (fun _ => c) ξ = AddSubgroup.closure {v | ∃ a b, v = ξ a - ξ b} := by
  unfold minLat; congr 1; ext v; simp [hc]

theorem minLat_X {M : ℕ} (hM : 2 ≤ M) :
    minLat (fun _ => (1 / (4 * M) : ℝ)) (xiX M) = parX.ker := by
  rw [minLat_const (by positivity), closure_X hM]

theorem minLat_Y {M : ℕ} (hM : 2 ≤ M) :
    minLat (fun _ => (1 / (2 * M) : ℝ)) (xiY M) = parY.ker := by
  rw [minLat_const (by positivity), closure_Y hM]

theorem minLat_1 {M : ℕ} (hM : 2 ≤ M) :
    minLat (fun _ => (1 / M : ℝ)) (xi1 M) = ⊤ := by
  rw [minLat_const (by have : (0 : ℝ) < M := (by exact_mod_cast (by omega : 0 < M)); positivity),
    closure_1 hM]

theorem sum_const_p {Ω : Type} [Fintype Ω] (c : ℝ) (hc : c * Fintype.card Ω = 1) :
    ∑ _a : Ω, c = 1 := by
  simp [mul_comm, hc]

theorem lawPow_const {Ω : Type} [Fintype Ω] {d : ℕ} (c : ℝ) (ξ : Ω → Fin d → ℤ) (n : ℕ)
    (x : Fin d → ℤ) :
    lawPow (fun _ => c) ξ n x = c ^ n * (univ.filter fun ω : Fin n → Ω => ∑ i, ξ (ω i) = x).card := by
  unfold lawPow
  rw [← sum_filter]; simp [mul_comm]

/-! ### The endgame count and the three lattice laws -/

def Sw {m M : ℕ} (w : Fin m → Fin M) : ℤ := ∑ i, ((w i : ℤ) + 1)

def Tsg {m M : ℕ} (w : Fin m → Fin M) (ε : Fin m → Bool) : ℤ := ∑ i, sg (ε i) * ((w i : ℤ) + 1)

/-- `Z(u) = #{ε ∈ {±1}^E : Σ ε_i w_i = u}`. -/
def Zc {m M : ℕ} (w : Fin m → Fin M) (u : ℤ) : ℕ := (univ.filter fun ε => Tsg w ε = u).card

theorem vec1_eq (v : Fin 1 → ℤ) (a : ℤ) : v = ![a] ↔ v 0 = a := by
  constructor
  · rintro rfl; rfl
  · intro h; funext j; fin_cases j; simpa using h

theorem vec2_eq (v : Fin 2 → ℤ) (a b : ℤ) : v = ![a, b] ↔ v 0 = a ∧ v 1 = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩; funext j; fin_cases j <;> simp [h0, h1]

theorem vec3_eq (v : Fin 3 → ℤ) (a b c : ℤ) : v = ![a, b, c] ↔ v 0 = a ∧ v 1 = b ∧ v 2 = c := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2⟩; funext j; fin_cases j <;> simp [h0, h1, h2]

theorem card_1 {m M : ℕ} (s : ℤ) :
    (univ.filter fun ω : Fin m → Fin M => ∑ i, xi1 M (ω i) = ![s]).card =
      (univ.filter fun w : Fin m → Fin M => Sw w = s).card := by
  congr 1; apply Finset.filter_congr; intro ω _
  rw [vec1_eq, Finset.sum_apply]; simp [Sw, xi1]

/-- The pairs `(w, ε)` with `Σw = s` and `Σεw = u` are counted by the law of `Y = (w, εw)`. -/
theorem card_Y {m M : ℕ} (s u : ℤ) :
    (univ.filter fun ω : Fin m → Fin M × Bool => ∑ i, xiY M (ω i) = ![s, u]).card =
      ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), Zc w u := by
  let e : (Fin m → Fin M × Bool) ≃ (Fin m → Fin M) × (Fin m → Bool) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
      invFun := fun t i => (t.1 i, t.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_equiv e _ (fun t => if Sw t.1 = s ∧ Tsg t.1 t.2 = u then 1 else 0)]
  · rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun w _ => ?_
    by_cases hs : Sw w = s
    · simp only [hs, true_and]
      rw [Zc, card_eq_sum_ones, sum_filter, if_pos trivial]
    · simp [hs]
  · intro ω
    simp only [vec2_eq, Finset.sum_apply, xiY, Sw, Tsg, e, Equiv.coe_fn_mk]
    simp

/-- The triples `(w, ε, ε′)` are counted by the law of `X = (w, εw, ε′w)`. -/
theorem card_X {m M : ℕ} (s u : ℤ) :
    (univ.filter fun ω : Fin m → Fin M × Bool × Bool => ∑ i, xiX M (ω i) = ![s, u, u]).card =
      ∑ w ∈ univ.filter (fun w : Fin m → Fin M => Sw w = s), Zc w u ^ 2 := by
  let e : (Fin m → Fin M × Bool × Bool) ≃ (Fin m → Fin M) × ((Fin m → Bool) × (Fin m → Bool)) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2.1, fun i => (ω i).2.2)
      invFun := fun t i => (t.1 i, t.2.1 i, t.2.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [card_eq_sum_ones, sum_filter]
  rw [Fintype.sum_equiv e _
    (fun t => if Sw t.1 = s ∧ Tsg t.1 t.2.1 = u ∧ Tsg t.1 t.2.2 = u then 1 else 0)]
  · rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun w _ => ?_
    by_cases hs : Sw w = s
    · simp only [hs, true_and]
      rw [sq, Zc, card_eq_sum_ones, sum_filter, sum_mul_sum, Fintype.sum_prod_type]
      refine sum_congr rfl fun ε _ => sum_congr rfl fun ε' _ => ?_
      by_cases h1 : Tsg w ε = u <;> by_cases h2 : Tsg w ε' = u <;> simp [h1, h2]
    · simp [hs]
  · intro ω
    simp only [vec3_eq, Finset.sum_apply, xiX, Sw, Tsg, e, Equiv.coe_fn_mk]
    split_ifs <;> simp_all

theorem gaussDens_diag {d : ℕ} (D : Fin d → ℝ) (hD : ∀ i, 0 < D i) (y : Fin d → ℝ) :
    gaussDens (diagonal D) y =
      Real.exp (-(1 / 2) * ∑ i, y i ^ 2 / D i) / (√(2 * Real.pi) ^ d * √(∏ i, D i)) := by
  have hinv : (diagonal D)⁻¹ = diagonal fun i => (D i)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hD i).ne'
  unfold gaussDens
  rw [hinv, det_diagonal]
  congr 3
  simp only [dotProduct, mulVec_diagonal]
  refine sum_congr rfl fun i _ => ?_
  field_simp

end ArcsAlgo.LLT
