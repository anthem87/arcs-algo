module

public import ArcsAlgo.Uniform.RppRounds
set_option autoImplicit false

/-!
# Theorem R″: the parameters (paper §6.7)

* `Hm`: the block size, `(σ√m)^{4/3} ≤ 2^m ≤ 2(σ√m)^{4/3}`, written as `σ⁴m² ≤ 8^m ≤ 8σ⁴m²`;
  `exists_Hm`: the least `m ≥ 1` with `2^m ≥ (σ√m)^{4/3}` satisfies it (`M ≥ 4`).
* `m_large`, `lam_large` (`λ_m⁶ ≥ (M/256)²`), `mpsi_small` (`(mψ)^{12} ≤ m^{18}/8^m`).
* `params_Rpp`: with `P₀ = ⌊λ_m/2⌋`, for `M` large: `m ≥ m₀`, `P₀ ≥ 100` and
  `p ≥ (1 − ε)/(6 ln(mM))`.
* `thmRpp`: **Theorem R″**: with `R(1 − 2e^{−g²/6})(1 − ε)/((1 + ε)·6 ln(mM)) ≥ ln(1/δ)` rounds, on
  `|T − S/2| ≤ S_G/2 − RmM` every round fails with probability `≤ δ`.

The only hypothesis is that of Lemma K (`RosserSchoenfeld`, cited). The running time
(`O(m 2^{m/4} + m 2^{m/2}/P₀)` per round, hence `2^{b/3+o(b)}`) is not formalized.
-/

open Finset Real Filter Topology

@[expose] public section

namespace ArcsAlgo.LLT

open ArcsAlgo ArcsAlgo.PrimeK

/-- The block size of Theorem R″: `(σ√m)^{4/3} ≤ 2^m ≤ 2(σ√m)^{4/3}`, written without roots as
`σ⁴m² ≤ 8^m ≤ 8σ⁴m²`; the least `m ≥ 1` with `2^m ≥ (σ√m)^{4/3}` satisfies it (`exists_Hm`). -/
def Hm (M m : ℕ) : Prop :=
  sig2 M ^ 2 * (m : ℝ) ^ 2 ≤ (8 : ℝ) ^ m ∧ (8 : ℝ) ^ m ≤ 8 * sig2 M ^ 2 * (m : ℝ) ^ 2

theorem sig2_ge16 {M : ℕ} (hM : 2 ≤ M) : (M : ℝ) ^ 2 / 16 ≤ sig2 M := by
  unfold sig2
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

theorem sig2_le (M : ℕ) : sig2 M ≤ (M : ℝ) ^ 2 / 12 := by unfold sig2; linarith

theorem cMB_le {M : ℕ} (hM : 2 ≤ M) : cMB M ≤ 5 / 8 := by
  unfold cMB
  have : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 1 / (2 * (M : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : 1 / (6 * (M : ℝ) ^ 2) ≤ 1 / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- **Existence of the block size**: for `M ≥ 4` the least `m ≥ 1` with `σ⁴m² ≤ 8^m` satisfies `Hm`. -/
theorem exists_Hm {M : ℕ} (hM : 4 ≤ M) : ∃ m : ℕ, 1 ≤ m ∧ Hm M m := by
  classical
  have hσ1 : 1 ≤ sig2 M := by
    unfold sig2; have : (4 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hex : ∃ m : ℕ, 1 ≤ m ∧ sig2 M ^ 2 * (m : ℝ) ^ 2 ≤ (8 : ℝ) ^ m := by
    refine ⟨⌈sig2 M ^ 2⌉₊ + 1, by omega, ?_⟩
    set n := ⌈sig2 M ^ 2⌉₊ + 1
    have h1 : sig2 M ^ 2 ≤ (2 : ℝ) ^ n := by
      have : sig2 M ^ 2 ≤ n := by
        have := Nat.le_ceil (sig2 M ^ 2); simp only [n]; push_cast; linarith
      exact this.trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
    have h2 : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
      have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        _ = (4 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc sig2 M ^ 2 * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n * (4 : ℝ) ^ n :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (8 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  set m := Nat.find hex
  obtain ⟨hm1, hm⟩ := Nat.find_spec hex
  refine ⟨m, hm1, hm, ?_⟩
  rcases Nat.lt_or_ge 1 m with h | h
  · have hmin := Nat.find_min hex (show m - 1 < m by omega)
    have hlt : (8 : ℝ) ^ (m - 1) < sig2 M ^ 2 * ((m - 1 : ℕ) : ℝ) ^ 2 := by
      by_contra hc; push Not at hc; exact hmin ⟨by omega, hc⟩
    have e : (8 : ℝ) ^ m = 8 * 8 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have hle : ((m - 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le m 1) 2
    have : 0 ≤ sig2 M ^ 2 := sq_nonneg _
    rw [e]; nlinarith
  · have hm1' : m = 1 := le_antisymm h hm1
    rw [hm1']; simp only [pow_one, Nat.cast_one, one_pow, mul_one]
    nlinarith

/-- `m → ∞` as `M → ∞` under `σ⁴m² ≤ 8^m`. -/
theorem m_large (k : ℕ) {M m : ℕ} (hM : 4 * 8 ^ k ≤ M) (hm : 1 ≤ m)
    (h : sig2 M ^ 2 * (m : ℝ) ^ 2 ≤ (8 : ℝ) ^ m) : k ≤ m := by
  by_contra hc
  push Not at hc
  have hM2 : 2 ≤ M := le_trans (by have := Nat.one_le_pow k 8 (by norm_num); omega) hM
  have hN : (4 : ℝ) * 8 ^ k ≤ M := by exact_mod_cast hM
  have h8 : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
  have hs := sig2_ge16 hM2
  have hsq : ((4 : ℝ) * 8 ^ k) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
  have hs1 : (8 : ℝ) ^ k ≤ sig2 M := by nlinarith
  have hs2 : sig2 M ≤ sig2 M ^ 2 := by nlinarith
  have hm' : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlt : (8 : ℝ) ^ m < 8 ^ k := pow_lt_pow_right₀ (by norm_num) hc
  have : (8 : ℝ) ^ k ≤ sig2 M ^ 2 * (m : ℝ) ^ 2 := by nlinarith
  linarith

/-- `λ_m⁶ ≥ (M/256)²` under `σ⁴m² ≤ 8^m`. -/
theorem lam_large {M m : ℕ} (hM : 2 ≤ M) (hm : 1 ≤ m)
    (h : sig2 M ^ 2 * (m : ℝ) ^ 2 ≤ (8 : ℝ) ^ m) : ((M : ℝ) / 256) ^ 2 ≤ lamM M m ^ 6 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < cMB M := by unfold cMB; positivity
  have hc := cMB_le hM
  set q := 2 * π * m * cMB M with hq
  have hq0 : 0 < q := by positivity
  have hl2 : lamM M m ^ 2 = 4 * 4 ^ m / ((M : ℝ) ^ 2 * q) := by
    unfold lamM
    have h4m : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e4 : ((2 : ℝ) ^ (m + 1)) ^ 2 = 4 * 4 ^ m := by rw [h4m]; ring
    rw [div_pow, mul_pow, Real.sq_sqrt hq0.le, e4]
  have h64 : (64 : ℝ) ^ m = ((8 : ℝ) ^ m) ^ 2 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have h64' : ((4 : ℝ) ^ m) ^ 3 = (64 : ℝ) ^ m := by
    rw [show (64 : ℝ) = 4 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have hl6 : lamM M m ^ 6 = 64 * 64 ^ m / ((M : ℝ) ^ 6 * q ^ 3) := by
    rw [show lamM M m ^ 6 = (lamM M m ^ 2) ^ 3 by ring, hl2, div_pow, mul_pow, ← h64']; ring
  have hs := sig2_ge16 hM
  have hs0 : 0 ≤ sig2 M := le_trans (by positivity) hs
  have h8 : (sig2 M ^ 2 * (m : ℝ) ^ 2) ^ 2 ≤ (64 : ℝ) ^ m := by
    rw [h64]; exact pow_le_pow_left₀ (by positivity) h 2
  have hσ4 : ((M : ℝ) ^ 2 / 16) ^ 4 ≤ sig2 M ^ 4 := pow_le_pow_left₀ (by positivity) hs 4
  have hq3 : q ^ 3 ≤ 62 * (m : ℝ) ^ 3 := by
    have hpi := Real.pi_lt_d2
    have hpc : π * cMB M ≤ 3.15 * (5 / 8) := mul_le_mul hpi.le hc hc0.le (by norm_num)
    have : q ≤ 3.9375 * m := by rw [hq]; nlinarith [hpc, hm']
    calc q ^ 3 ≤ (3.9375 * (m : ℝ)) ^ 3 := pow_le_pow_left₀ hq0.le this 3
      _ ≤ 62 * (m : ℝ) ^ 3 := by
          rw [mul_pow]; have : (3.9375 : ℝ) ^ 3 ≤ 62 := by norm_num
          nlinarith [pow_pos (by linarith : (0 : ℝ) < m) 3]
  rw [hl6, le_div_iff₀ (by positivity)]
  have hm3 : 0 < (m : ℝ) ^ 3 := by positivity
  have hM6 : 0 < (M : ℝ) ^ 6 := by positivity
  calc ((M : ℝ) / 256) ^ 2 * ((M : ℝ) ^ 6 * q ^ 3)
      ≤ ((M : ℝ) / 256) ^ 2 * ((M : ℝ) ^ 6 * (62 * (m : ℝ) ^ 3)) := by gcongr
    _ ≤ 64 * (((M : ℝ) ^ 2 / 16) ^ 4 * (m : ℝ) ^ 4) := by
        have : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm' (by norm_num)
        have e1 : ((M : ℝ) / 256) ^ 2 * ((M : ℝ) ^ 6 * (62 * (m : ℝ) ^ 3)) =
            62 * ((M : ℝ) ^ 8 / 65536 * (m : ℝ) ^ 3) := by ring
        have e2 : 64 * (((M : ℝ) ^ 2 / 16) ^ 4 * (m : ℝ) ^ 4) = 64 * ((M : ℝ) ^ 8 / 65536 * (m : ℝ) ^ 4) := by
          ring
        rw [e1, e2]
        have : 0 ≤ (M : ℝ) ^ 8 / 65536 := by positivity
        nlinarith
    _ ≤ 64 * (sig2 M ^ 4 * (m : ℝ) ^ 4) := by gcongr
    _ = 64 * (sig2 M ^ 2 * (m : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ 64 * 64 ^ m := by gcongr

/-- `(mψ)^{12} ≤ m^{18}/8^m` under `8^m ≤ 8σ⁴m²`, `ψ = 2^{m/2}/M`. -/
theorem mpsi_small {M m : ℕ} (hM : 2 ≤ M) (h : (8 : ℝ) ^ m ≤ 8 * sig2 M ^ 2 * (m : ℝ) ^ 2) :
    ((m : ℝ) * (√((2 : ℝ) ^ m) / M)) ^ 12 ≤ (m : ℝ) ^ 18 / 8 ^ m := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hs0 : 0 ≤ sig2 M := le_trans (by positivity) (sig2_ge16 hM)
  have hs := sig2_le M
  have h1 : (8 : ℝ) ^ m ≤ (M : ℝ) ^ 4 * (m : ℝ) ^ 2 / 18 := by
    have : sig2 M ^ 2 ≤ ((M : ℝ) ^ 2 / 12) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    have h0 : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hy : (√((2 : ℝ) ^ m)) ^ 2 = 2 ^ m := Real.sq_sqrt (by positivity)
  have h83 : ((2 : ℝ) ^ m) ^ 3 = 8 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e : ((m : ℝ) * (√((2 : ℝ) ^ m) / M)) ^ 12 = (m : ℝ) ^ 12 * ((8 : ℝ) ^ m) ^ 2 / (M : ℝ) ^ 12 := by
    rw [mul_pow, div_pow, show (√((2 : ℝ) ^ m)) ^ 12 = ((√((2 : ℝ) ^ m)) ^ 2) ^ 6 by ring, hy,
      show ((2 : ℝ) ^ m) ^ 6 = (((2 : ℝ) ^ m) ^ 3) ^ 2 by ring, h83]
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : ((8 : ℝ) ^ m) ^ 3 ≤ ((M : ℝ) ^ 4 * (m : ℝ) ^ 2 / 18) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have e2 : ((M : ℝ) ^ 4 * (m : ℝ) ^ 2 / 18) ^ 3 = (M : ℝ) ^ 12 * (m : ℝ) ^ 6 / 5832 := by ring
  rw [e2] at h3
  have e3 : (m : ℝ) ^ 12 * ((8 : ℝ) ^ m) ^ 2 * (8 : ℝ) ^ m = (m : ℝ) ^ 12 * ((8 : ℝ) ^ m) ^ 3 := by ring
  rw [e3]
  have : (0 : ℝ) ≤ (m : ℝ) ^ 12 := by positivity
  have h4 : (m : ℝ) ^ 12 * ((8 : ℝ) ^ m) ^ 3 ≤ (m : ℝ) ^ 12 * ((M : ℝ) ^ 12 * (m : ℝ) ^ 6 / 5832) :=
    mul_le_mul_of_nonneg_left h3 this
  have e4 : (m : ℝ) ^ 12 * ((M : ℝ) ^ 12 * (m : ℝ) ^ 6 / 5832) = (m : ℝ) ^ 18 * (M : ℝ) ^ 12 / 5832 := by
    ring
  rw [e4] at h4
  have : 0 ≤ (m : ℝ) ^ 18 * (M : ℝ) ^ 12 := by positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- **The parameters of Theorem R″** (paper §6.7): with `m` as in `Hm` and `P₀ = ⌊λ_m/2⌋`, for
every `m₀`, every `ε ∈ (0, 1)` and fixed `g`, for `M` large enough: `m ≥ m₀`, `P₀ ≥ 100` and
`p ≥ (1 − ε)/(6 ln(mM))`. -/
theorem params_Rpp (g : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (m₀ : ℕ) :
    ∃ M₀ : ℕ, ∀ M m : ℕ, M₀ ≤ M → 1 ≤ m → Hm M m →
      m₀ ≤ m ∧ 100 ≤ ⌊lamM M m / 2⌋₊ ∧
        (1 - ε) / (6 * log (m * M)) ≤ pRpp g M m ⌊lamM M m / 2⌋₊ := by
  set η := 1 / (3 * exp (g ^ 2 / 2)) with hη
  have he1 : 1 ≤ exp (g ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 3 := by
    rw [hη, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hev := (tendsto_pow_const_div_const_pow_of_one_lt 18 (by norm_num : (1 : ℝ) < 8)).eventually
    (ge_mem_nhds (show (0 : ℝ) < η ^ 12 by positivity))
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hev
  set k := max m₀ k₁
  set Λ := max 200 (4 / ε)
  have hΛ : 200 ≤ Λ := le_max_left _ _
  refine ⟨max (max (4 * 8 ^ k) (⌈256 * Λ ^ 3⌉₊)) (⌈exp (1 / ε)⌉₊), fun M m hM hm hH => ?_⟩
  have hMk : 4 * 8 ^ k ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMΛ : 256 * Λ ^ 3 ≤ (M : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM)
  have hMe : exp (1 / ε) ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hM)
  have hM2 : 2 ≤ M := le_trans (by have := Nat.one_le_pow k 8 (by norm_num); omega) hMk
  have hkm := m_large k hMk hm hH.1
  have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hkm
  have hk1m : k₁ ≤ m := le_trans (le_max_right _ _) hkm
  -- `λ_m ≥ Λ`
  have hL := lamM_pos hM2 hm
  have hlam : Λ ≤ lamM M m := by
    have h6 := lam_large hM2 hm hH.1
    have : (Λ ^ 3) ^ 2 ≤ ((M : ℝ) / 256) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by rw [le_div_iff₀ (by norm_num)]; linarith) 2
    have h' : Λ ^ 6 ≤ lamM M m ^ 6 := by rw [show Λ ^ 6 = (Λ ^ 3) ^ 2 by ring]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hL.le (by norm_num)).mp h'
  have hP : 100 ≤ ⌊lamM M m / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  refine ⟨hm0, hP, ?_⟩
  -- the pieces of `p⁻¹`
  have hP2 : 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m ≤ 1 := by
    rw [div_le_one hL]; have := Nat.floor_le (show 0 ≤ lamM M m / 2 by positivity); linarith
  set t := (m : ℝ) * (√((2 : ℝ) ^ m) / M)
  have ht0 : 0 ≤ t := by positivity
  have ht : t ≤ η := by
    have h12 := (mpsi_small hM2 hH.2).trans (hk₁ m hk1m)
    exact (pow_le_pow_iff_left₀ ht0 hη0.le (by norm_num)).mp h12
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set ψ := √((2 : ℝ) ^ m) / M
  have hψ0 : 0 ≤ ψ := by positivity
  have hV : 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) ≤ 1 := by
    have h1 : (m : ℝ) * (3 * ψ + ψ ^ 2) ≤ 3 * t + t ^ 2 := by
      simp only [t]; nlinarith [mul_nonneg hψ0 hψ0]
    have h2 : 3 * t + t ^ 2 ≤ 4 * η := by nlinarith
    have h3 : exp (g ^ 2 / 2) * (4 * η) = 4 / 3 := by rw [hη]; field_simp
    calc 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) = 0.72 * exp (g ^ 2 / 2) * (m * (3 * ψ + ψ ^ 2)) := by
          ring
      _ ≤ 0.72 * exp (g ^ 2 / 2) * (4 * η) := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 0.72 * (exp (g ^ 2 / 2) * (4 * η)) := by ring
      _ ≤ 1 := by rw [h3]; norm_num
  have hV0 : 0 ≤ 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2) := by positivity
  have h2L : 2 / lamM M m ≤ ε / 2 := by
    rw [div_le_iff₀ hL]
    have : 4 / ε ≤ lamM M m := le_trans (le_max_right _ _) hlam
    rw [div_le_iff₀ hε0] at this; nlinarith
  have hlogM : 1 / ε ≤ log M := by
    rw [← Real.log_exp (1 / ε)]; exact Real.log_le_log (Real.exp_pos _) hMe
  set Lg := 6 * log (m * M)
  have hLg : 4 / ε ≤ Lg := by
    have : log (M : ℝ) ≤ log (m * M) := Real.log_le_log (by positivity) (by nlinarith)
    have : 6 / ε ≤ Lg := by
      simp only [Lg]; have := mul_le_mul_of_nonneg_left hlogM (by norm_num : (0 : ℝ) ≤ 6)
      rw [show (6 : ℝ) * (1 / ε) = 6 / ε by ring] at this; linarith
    have : 4 / ε ≤ 6 / ε := div_le_div_of_nonneg_right (by norm_num) hε0.le
    linarith
  have hLg0 : 0 < Lg := lt_of_lt_of_le (by positivity) hLg
  -- `p⁻¹ ≤ 2 + L(1 + ε/2) ≤ L(1 + ε) ≤ L/(1 − ε)`
  have hinv : 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2)) +
      Lg * (1 + 2 / lamM M m) ≤ Lg / (1 - ε) := by
    have hA : 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2)) ≤ 2 := by
      have h0 : 0 ≤ 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m := by positivity
      nlinarith
    have hB : Lg * (1 + 2 / lamM M m) ≤ Lg * (1 + ε / 2) := by gcongr
    have hC : 2 ≤ Lg * (ε / 2) := by
      rw [div_le_iff₀ hε0] at hLg; nlinarith
    have hD : Lg * (1 + ε) ≤ Lg / (1 - ε) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hpos : 0 < 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2)) +
      Lg * (1 + 2 / lamM M m) := by
    have : 0 ≤ 2 * (⌊lamM M m / 2⌋₊ : ℝ) / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m * (3 * ψ + ψ ^ 2)) := by
      positivity
    have : 0 < Lg * (1 + 2 / lamM M m) := by positivity
    linarith
  unfold pRpp
  rw [show (1 - ε) / Lg = 1 / (Lg / (1 - ε)) by field_simp]
  exact one_div_le_one_div_of_le hpos hinv

set_option maxHeartbeats 2000000 in
/-- **Theorem R″** (paper §6.7). Fix `g ≥ 0` with `2e^{−g²/6} < 1` (say `g = 3`), `ε ∈ (0, 1)` and
`δ > 0`. For `M` large enough, take `m` as in `Hm`, `P₀ = ⌊λ_m/2⌋`, halves with `|A| = ⌊m/2⌋`,
and `R` blocks with `R·(1 − 2e^{−g²/6})(1 − ε)/((1 + ε)·6 ln(mM)) ≥ ln(1/δ)`. Then, on the event
`|T − S/2| ≤ S_G/2 − RmM`, every round fails with probability at most `δ`: `P₀ ≥ 100` and
`p ≥ (1 − ε)/(6 ln(mM))` (`params_Rpp`) feed `thmRpp_gen`. The only hypothesis is that of Lemma K
(Rosser–Schoenfeld). The running time is not formalized. -/
theorem thmRpp (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) (hge : 2 * exp (-(g ^ 2 / 6)) < 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M h m R : ℕ, M₀ ≤ M → 1 ≤ m → Hm M m → ∀ A : Finset (Fin m), A.card = m / 2 →
      log (1 / δ) ≤ (1 - 2 * exp (-(g ^ 2 / 6))) * ((1 - ε) / (1 + ε) / (6 * log (m * M))) * R →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr ⌊lamM M m / 2⌋₊ A (wB j)
              (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤ δ := by
  obtain ⟨m₀, h₀⟩ := thmRpp_gen hRS hg hε0
  obtain ⟨M₁, h₁⟩ := params_Rpp g hε0 hε1 m₀
  refine ⟨max M₁ 2, fun M h m R hM hm hH A hA hR T K hK => ?_⟩
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hm0, hP, hp⟩ := h₁ M m hM1 hm hH
  refine (h₀ M h m R ⌊lamM M m / 2⌋₊ hM2 hm0 hP A hA T K hK).trans ?_
  have he : 0 ≤ 1 - 2 * exp (-(g ^ 2 / 6)) := by linarith
  set x := (1 - 2 * exp (-(g ^ 2 / 6))) * (pRpp g M m ⌊lamM M m / 2⌋₊ / (1 + ε))
  have hp1 := pRpp_le_one g (P₀ := ⌊lamM M m / 2⌋₊) hM2 hm
  have hp0 := pRpp_nonneg g (P₀ := ⌊lamM M m / 2⌋₊) hM2 hm
  have hx1 : x ≤ 1 := by
    have h1 : 1 - 2 * exp (-(g ^ 2 / 6)) ≤ 1 := by linarith [Real.exp_pos (-(g ^ 2 / 6))]
    have h2 : pRpp g M m ⌊lamM M m / 2⌋₊ / (1 + ε) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h3 : 0 ≤ pRpp g M m ⌊lamM M m / 2⌋₊ / (1 + ε) := div_nonneg hp0 (by linarith)
    simp only [x]; nlinarith
  refine pow_le_delta hx1 hδ (le_trans hR ?_)
  simp only [x]
  have : (1 - ε) / (1 + ε) / (6 * log (m * M)) ≤ pRpp g M m ⌊lamM M m / 2⌋₊ / (1 + ε) := by
    rw [div_div, mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right hp (by linarith)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left this he
  nlinarith

end ArcsAlgo.LLT
