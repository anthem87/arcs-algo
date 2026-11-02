module

public import ArcsAlgo.LemmaL3
set_option autoImplicit false

/-!
# Lemma L: neighbourhood of an arc (paper §3.5)

* `L_det`: with `M = ⌊√N⌋`, `β = X/N`, `ε = 1/N` and a bound `E` for `|π(n;q,r) − li(n)/φ(q)|` on
  `[M, N]`: `|F_N(e(a/q + X/N))| ≤ 2^n exp((N/log N)(A_q(X)/φ(q) − log 2) + (X+2)/(X log N) + M + V
  + φ(q)E(2 log N + V))`, `V = (4X + 2) log N` (steps A–D: `FN_reduce`, `class_sum_le`, `seqVar_G`,
  `int_G_le`, `sum_logcos`).
* `norm_FW_neg_add`: `|F_W(e(−θ + k))| = |F_W(e(θ))|`, which reduces `X < 0` to `X > 0` (`a ↦ q − a`).
* `lemmaL`: for `N ≥ N₀`, `3 ≤ q ≤ (log N)^B`, `(a, q) = 1`, `N^{−1/2} ≤ |X| ≤ (log N)^B/q`:
  `|F_N(e(a/q + X/N))| ≤ 2^n exp((N/log N)(A_q(|X|)/φ(q) − log 2) + 3N/log² N)`.

The only hypothesis is `SiegelWalfisz`. Stated multiplicatively: the log form of the paper reads
`log 0 = −∞` at a zero of `F_N`.
-/

open Finset Real

@[expose] public section

namespace ArcsAlgo.Core

open ArcsAlgo.Classical

theorem seqVar_mono {f : ℝ → ℝ} {a b V V' : ℝ} (h : SeqVar f a b V) (hVV : V ≤ V') : SeqVar f a b V' :=
  fun k u hu hus => (h k u hu hus).trans hVV

set_option maxHeartbeats 2000000 in
/-- **Lemma L, deterministic form**: for `3 ≤ M ≤ N`, `X > 0`, `β = X/N`, `ε = 1/N`, and
`|π(n; q, r) − li(n)/φ(q)| ≤ E` for `(r, q) = 1`, `M ≤ n ≤ N`:
`|F_N(e(a/q + X/N))| ≤ 2^{|W_N|} exp((N/log N)(A_q(X)/φ(q) − log 2) + (X + 2)/(X log N) + M + V
+ φ(q)E(2 log N + V))`, `V = (4X + 2) log N`. -/
theorem L_det {q a M N : ℕ} (hq : 3 ≤ q) (ha : a.Coprime q) (hM : 3 ≤ M) (hMN : M ≤ N) {X : ℝ} (hX : 0 < X)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ r ∈ resQ q, ∀ n : ℕ, M ≤ n → n ≤ N → |(cntQ n q r : ℝ) - liK 0 n / q.totient| ≤ E) :
    ‖FW (WN N) ((a : ℝ) / q + X / N)‖ ≤ 2 ^ (WN N).card * Real.exp ((N / Real.log N) * (Aq q X / q.totient - Real.log 2) +
      (X + 2) / (X * Real.log N) + M + (4 * X + 2) * Real.log N +
        q.totient * E * (2 * Real.log N + (4 * X + 2) * Real.log N)) := by
  have hq1 : 1 ≤ q := by omega
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast le_trans hM hMN
  have hNpos : (0 : ℝ) < N := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set β : ℝ := X / N with hβdef
  have hβ : 0 < β := by positivity
  set ε : ℝ := 1 / N with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one hNpos]; linarith
  have hlogε : -Real.log ε = Real.log N := by rw [hεdef, one_div, Real.log_inv, neg_neg]
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set V : ℝ := (4 * X + 2) * Real.log N
  have hNβ : (N : ℝ) * β = X := by rw [hβdef]; field_simp
  refine (FN_reduce hq M N β hε).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  -- one class
  set c : ℕ → ℝ := fun r => ((r * a : ℕ) : ℝ) / q
  have hclass : ∀ r ∈ resQ q, ∑ p ∈ (Ioc M N).filter (fun n => n.Prime ∧ n % q = r), Gq q a r β ε p ≤
      (1 / q.totient) * (1 / (β * Real.log N) * ((∫ y in c r..c r + X, Real.log (cos (π * y))) + (X + 2) * ε +
        M * β * Real.log N)) + V / q.totient + E * (2 * Real.log N + V) := by
    intro r hr
    have hrq : r < q := mem_range.mp (mem_filter.mp hr).1
    have hset : (Ioc M N).filter (fun n => n.Prime ∧ n % q = r) = (Ioc M N).filter (fun n => n.Prime ∧ n % q = r % q) := by
      rw [Nat.mod_eq_of_lt hrq]
    rw [hset]
    set f : ℝ → ℝ := fun t => hEps ε (c r + t * β)
    have hfG : ∀ p : ℕ, Gq q a r β ε p = f p := fun p => rfl
    rw [sum_congr rfl fun p _ => hfG p]
    have hfc : ContinuousOn f (Set.Icc (M : ℝ) N) := ((hEps_cont ε hε).comp (by fun_prop)).continuousOn
    have hS : ∀ t ∈ Set.Icc (M : ℝ) N, |f t| ≤ Real.log N := by
      intro t _
      have h1 := hEps_le ε (c r + t * β) hε1
      have h2 := hEps_ge hε (c r + t * β)
      rw [abs_le]; constructor <;> linarith
    have hV : SeqVar f M N V := by
      refine seqVar_mono (seqVar_G hε hε1 (c r) hβ.le hMN') ?_
      rw [hlogε]
      have : ((N : ℝ) - M) * β ≤ X := by rw [← hNβ]; nlinarith
      simp only [V]; nlinarith
    have hcs := class_sum_le (f := f) hq1 hM hMN hfc (hE r hr) hS hV hE0
    have hint := int_G_le hε hε1 (c r) hβ hM hMN
    rw [hNβ, hlogε] at hint
    have h1φ : 0 ≤ 1 / (q.totient : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hint h1φ
    linarith
  refine (sum_le_sum hclass).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
    sum_const, card_resQ, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
  have hsl := sum_logcos hq ha hX
  simp only [c] at hsl ⊢
  rw [hsl]
  simp only [sum_const, card_resQ, nsmul_eq_mul]
  rw [hβdef, hεdef]
  field_simp

theorem norm_FW_neg_add (W : Finset ℕ) (θ : ℝ) (k : ℤ) : ‖FW W (-θ + k)‖ = ‖FW W θ‖ := by
  rw [norm_FW, norm_FW]
  refine congrArg (fun x => 2 ^ W.card * x) (prod_congr rfl fun w _ => ?_)
  rw [show π * (w * (-θ + k)) = -(π * (w * θ)) + ((w * k : ℤ) : ℝ) * π by push_cast; ring,
    Real.cos_add_int_mul_pi, Real.cos_neg, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

set_option maxHeartbeats 4000000 in
/-- **Lemma L (neighbourhood of an arc)** (paper §3.5). Fix `B > 0`. For `N ≥ N₀`, `3 ≤ q ≤ (log N)^B`,
`(a, q) = 1` and `N^{−1/2} ≤ |X| ≤ (log N)^B/q`:
`|F_N(e(a/q + X/N))| ≤ 2^n exp((N/log N)(A_q(|X|)/φ(q) − log 2) + 3N/log² N)`, `n = |W_N|`; i.e.
`log|F_N(e(θ))| ≤ n log 2 + (N/log N)(A_q(|X|)/φ(q) − log 2) + O_B(N/log² N)`. The only hypothesis is
Siegel–Walfisz. Stated multiplicatively (the log form reads `log 0 = −∞`). -/
theorem lemmaL (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ Real.log N ^ B → a.Coprime q →
      ∀ X : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |X| → |X| ≤ Real.log N ^ B / q →
        ‖FW (WN N) ((a : ℝ) / q + X / N)‖ ≤ 2 ^ (WN N).card *
          Real.exp ((N / Real.log N) * (Aq q |X| / q.totient - Real.log 2) + 3 * N / Real.log N ^ 2) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hsw⟩ := hSW (2 * B) (by positivity)
  obtain ⟨E1, hE1, hE1'⟩ := ev_poly_exp 2 one_pos 4
  obtain ⟨E2, hE2, hE2'⟩ := ev_poly_exp (B + 3) one_pos 6
  obtain ⟨E3, hE3, hE3'⟩ := ev_poly_exp (2 * B + 3) (by positivity : 0 < c₀ / 2) (8 * C₀)
  set L₁ := max (max E1 E2) (max E3 16)
  refine ⟨⌈Real.exp L₁⌉₊ + 16, fun N hN q a hq hqL ha X hXlo hXhi => ?_⟩
  set Nr : ℝ := (N : ℝ) with hNr
  set L := Real.log Nr
  have hN16 : (16 : ℝ) ≤ Nr := by have : 16 ≤ N := by omega
                                  rw [hNr]; exact_mod_cast this
  have hNpos : 0 < Nr := by linarith
  have hLL : L₁ ≤ L := by
    have : Real.exp L₁ ≤ Nr := le_trans (Nat.le_ceil _) (by rw [hNr]; exact_mod_cast (by omega : ⌈Real.exp L₁⌉₊ ≤ N))
    rw [← Real.exp_le_exp, Real.exp_log hNpos]; exact this
  have hL16 : 16 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  have hL1' : E1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hL2' : E2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL3' : E3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp L = Nr := Real.exp_log hNpos
  have hq1 : 1 ≤ q := by omega
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ1 : 1 ≤ L ^ B := Real.one_le_rpow (by linarith) hB.le
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hsqrtN : √Nr = Real.exp (L / 2) := by
    rw [← hexpL, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  have hsqLL : √L ≤ L / 4 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  -- `M = ⌊√N⌋`
  set M : ℕ := ⌊√Nr⌋₊
  have hM1 : (M : ℝ) ≤ √Nr := Nat.floor_le (Real.sqrt_nonneg _)
  have hM2 : √Nr - 1 < M := Nat.sub_one_lt_floor _
  have hsq4 : (4 : ℝ) ≤ √Nr := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN16
  have hM3 : 3 ≤ M := by have : (3 : ℝ) ≤ M := by linarith
                         exact_mod_cast this
  have hMN : M ≤ N := by
    have : (M : ℝ) ≤ Nr := by
      have : √Nr ≤ Nr := by rw [Real.sqrt_le_left (by positivity)]; nlinarith
      linarith
    rw [hNr] at this; exact_mod_cast this
  -- Siegel–Walfisz on `[M, N]`
  set E : ℝ := C₀ * Nr * Real.exp (-(c₀ / 2) * √L)
  have hE0 : 0 ≤ E := by positivity
  have hE : ∀ r ∈ resQ q, ∀ n : ℕ, M ≤ n → n ≤ N → |(cntQ n q r : ℝ) - liK 0 n / q.totient| ≤ E := by
    intro r hr n hn1 hn2
    have hn : (√Nr / 2 : ℝ) ≤ n := by
      have : (M : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have hn2' : (n : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hn2
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogn : L / 4 ≤ Real.log n := by
      have h1 := Real.log_le_log (by positivity) hn
      rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hNpos.le] at h1
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hqn : (q : ℝ) ≤ Real.log n ^ (2 * B) := by
      refine hqL.trans ?_
      have h1 : L ^ B ≤ ((L / 4) ^ 2) ^ B := Real.rpow_le_rpow hL0.le (by nlinarith) hB.le
      have h2 : ((L / 4) ^ 2) ^ B = (L / 4) ^ (2 * B) := by rw [Real.rpow_mul (by linarith), Real.rpow_two]
      have h3 : (L / 4) ^ (2 * B) ≤ Real.log n ^ (2 * B) := Real.rpow_le_rpow (by linarith) hlogn (by positivity)
      linarith
    have hn2'' : 2 ≤ n := by omega
    have h := hsw n hn2'' q r hq1 hqn (mem_filter.mp hr).2
    refine h.trans ?_
    have hsq : √L / 2 ≤ √(Real.log n) := by
      have : √(L / 4) ≤ √(Real.log n) := Real.sqrt_le_sqrt hlogn
      rwa [Real.sqrt_div' L (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    have he : Real.exp (-c₀ * √(Real.log n)) ≤ Real.exp (-(c₀ / 2) * √L) := Real.exp_le_exp.mpr (by nlinarith)
    have : (0 : ℝ) ≤ Real.exp (-c₀ * √(Real.log n)) := (Real.exp_pos _).le
    calc C₀ * n * Real.exp (-c₀ * √(Real.log n)) ≤ C₀ * Nr * Real.exp (-c₀ * √(Real.log n)) := by gcongr
      _ ≤ C₀ * Nr * Real.exp (-(c₀ / 2) * √L) := by gcongr
  -- the positive case
  have hpos : ∀ a' : ℕ, a'.Coprime q → ∀ Y : ℝ, Nr ^ (-(1 / 2 : ℝ)) ≤ Y → Y ≤ L ^ B / q →
      ‖FW (WN N) ((a' : ℝ) / q + Y / N)‖ ≤ 2 ^ (WN N).card *
        Real.exp ((N / Real.log N) * (Aq q Y / q.totient - Real.log 2) + 3 * N / Real.log N ^ 2) := by
    intro a' ha' Y hY1 hY2
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    refine (L_det hq ha' hM3 hMN hY0 hE0 hE).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    rw [← hNr]
    -- the errors
    have hYL : Y ≤ L ^ B := hY2.trans (div_le_self (by positivity) (by linarith))
    have hinvY : 1 / Y ≤ √Nr := by
      rw [div_le_iff₀ hY0]
      have : Nr ^ (-(1 / 2 : ℝ)) * √Nr = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; norm_num
      nlinarith [Real.sqrt_nonneg Nr]
    have e1 : (Y + 2) / (Y * L) + M ≤ 4 * √Nr := by
      have : (Y + 2) / (Y * L) ≤ 1 + 2 * √Nr := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : 1 ≤ L := by linarith
        have : 2 ≤ 2 * √Nr * Y := by have := hinvY; rw [div_le_iff₀ hY0] at this; linarith
        nlinarith
      linarith
    have he1 : 4 * L ^ (2 : ℝ) ≤ Real.exp (1 * √L) := hE1' L hL1'
    rw [Real.rpow_two] at he1
    have hsq : 4 * √Nr ≤ Nr / L ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : 4 * L ^ 2 ≤ √Nr := by
        rw [hsqrtN]; exact he1.trans (Real.exp_le_exp.mpr (by nlinarith))
      have hsN : √Nr * √Nr = Nr := Real.mul_self_sqrt hNpos.le
      nlinarith [Real.sqrt_nonneg Nr]
    have he2 : 6 * L ^ (B + 3) ≤ Real.exp (1 * √L) := hE2' L hL2'
    have hV : (4 * Y + 2) * L ≤ Nr / L ^ 2 := by
      have h1 : (4 * Y + 2) * L ≤ 6 * L ^ (B + 1) := by
        rw [Real.rpow_add hL0, Real.rpow_one]; nlinarith
      have h2 : 6 * L ^ (B + 1) * L ^ 2 = 6 * L ^ (B + 3) := by
        rw [mul_assoc, ← Real.rpow_two, ← Real.rpow_add hL0]; ring_nf
      have h3 : Real.exp (1 * √L) ≤ Nr := by rw [← hexpL]; exact Real.exp_le_exp.mpr (by nlinarith)
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg L]
    have he3 : 8 * C₀ * L ^ (2 * B + 3) ≤ Real.exp (c₀ / 2 * √L) := hE3' L hL3'
    have hSWt : q.totient * E * (2 * L + (4 * Y + 2) * L) ≤ Nr / L ^ 2 := by
      have hpoly : (q.totient : ℝ) * (2 * L + (4 * Y + 2) * L) ≤ 8 * L ^ (2 * B + 1) := by
        have h1 : (q.totient : ℝ) ≤ L ^ B := hφ.trans hqL
        have h2 : 2 * L + (4 * Y + 2) * L ≤ 8 * L ^ (B + 1) := by
          rw [Real.rpow_add hL0, Real.rpow_one]; nlinarith
        have h3 : L ^ B * L ^ (B + 1) = L ^ (2 * B + 1) := by
          rw [← Real.rpow_add hL0]; ring_nf
        have : 0 ≤ 2 * L + (4 * Y + 2) * L := by positivity
        nlinarith [Real.rpow_nonneg hL0.le (B + 1)]
      have hexp : Real.exp (c₀ / 2 * √L) * Real.exp (-(c₀ / 2) * √L) = 1 := by rw [← Real.exp_add]; ring_nf; simp
      have h4 : L ^ (2 * B + 1) * L ^ 2 = L ^ (2 * B + 3) := by
        rw [← Real.rpow_two, ← Real.rpow_add hL0]; ring_nf
      rw [le_div_iff₀ (by positivity)]
      have hp : 0 < Real.exp (-(c₀ / 2) * √L) := Real.exp_pos _
      calc q.totient * E * (2 * L + (4 * Y + 2) * L) * L ^ 2
          = C₀ * Nr * Real.exp (-(c₀ / 2) * √L) * ((q.totient : ℝ) * (2 * L + (4 * Y + 2) * L)) * L ^ 2 := by
            simp only [E]; ring
        _ ≤ C₀ * Nr * Real.exp (-(c₀ / 2) * √L) * (8 * L ^ (2 * B + 1)) * L ^ 2 := by gcongr
        _ = Nr * (8 * C₀ * L ^ (2 * B + 3)) * Real.exp (-(c₀ / 2) * √L) := by rw [← h4]; ring
        _ ≤ Nr * Real.exp (c₀ / 2 * √L) * Real.exp (-(c₀ / 2) * √L) := by gcongr
        _ = Nr := by rw [mul_assoc, hexp, mul_one]
    have : 3 * Nr / L ^ 2 = Nr / L ^ 2 + Nr / L ^ 2 + Nr / L ^ 2 := by ring
    linarith
  -- the sign of `X`
  rcases le_or_gt 0 X with hX | hX
  · rw [abs_of_nonneg hX] at hXlo hXhi ⊢
    exact hpos a ha X hXlo hXhi
  · rw [abs_of_neg hX] at hXlo hXhi ⊢
    set a' := q - a % q
    have hamod : a % q < q := Nat.mod_lt _ (by omega)
    have ha' : a'.Coprime q := by
      have h1 : (a % q).Coprime q := by
        rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact ha
      exact (Nat.coprime_self_sub_left hamod.le).mpr h1
    set k : ℕ := a / q
    have hint : (a : ℝ) / q + X / N = -((a' : ℝ) / q + (-X) / N) + (((k + 1 : ℕ) : ℤ) : ℝ) := by
      have h := Nat.div_add_mod a q
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hk : (a : ℝ) = q * k + (a % q : ℕ) := by exact_mod_cast h.symm
      simp only [a']
      rw [Nat.cast_sub hamod.le, hk, Int.cast_natCast]
      push_cast
      field_simp
      ring
    rw [hint, norm_FW_neg_add]
    exact hpos a' ha' (-X) hXlo hXhi


end ArcsAlgo.Core
