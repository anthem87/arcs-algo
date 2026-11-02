module

public import ArcsAlgo.Propagation
set_option autoImplicit false

/-!
# Definitional variables: soundness of Ext, probing, probing to depth ℓ (paper §7.5)

Boolean variables. A partial assignment is `ρ : V → Option Bool`; the solutions are a finite set
`S` of total assignments. A propagator `P` maps `ρ` to `none` (failure) or to an extension of
`ρ`; it is *sound* if it fails only when no solution is consistent with `ρ`, and keeps every
solution consistent with `ρ`.

* Proposition 7.8: `filter_keeps` (arc consistency keeps every solution), `xor_combination`
  (every GF(2) combination of satisfied rows is satisfied: Gauss is sound), the rows of the local
  linearization (`local_rows`), and `Sound.bind` (sound steps compose).
* Proposition 7.10: `probeVar_sound`, `probeVar_relation` (the parity row recorded by probing
  holds on every solution).
* Proposition 7.10′: (a) `probe_sound`; (b) `probe_cost`; (c) `probe_complete` for a strong
  backdoor in the sense of [WGS].
-/

@[expose] public section

namespace ArcsAlgo.Probing

open Finset

variable {V : Type*} [DecidableEq V]

/-- A partial assignment. -/
abbrev PA (V : Type*) := V → Option Bool

/-- A total assignment `s` is consistent with `ρ`. -/
def Consistent (s : V → Bool) (ρ : PA V) : Prop := ∀ v b, ρ v = some b → s v = b

/-- `σ` extends `ρ`. -/
def Extends (σ ρ : PA V) : Prop := ∀ v b, ρ v = some b → σ v = some b

/-- A sound propagator for the solutions `S`. -/
structure Sound (S : Finset (V → Bool)) (P : PA V → Option (PA V)) : Prop where
  fail : ∀ ρ, P ρ = none → ∀ s ∈ S, ¬ Consistent s ρ
  ext : ∀ ρ ρ', P ρ = some ρ' → Extends ρ' ρ
  keep : ∀ ρ ρ', P ρ = some ρ' → ∀ s ∈ S, Consistent s ρ → Consistent s ρ'

omit [DecidableEq V] in
theorem Extends.trans {ρ σ τ : PA V} (h1 : Extends τ σ) (h2 : Extends σ ρ) : Extends τ ρ :=
  fun v b h => h1 v b (h2 v b h)

omit [DecidableEq V] in
/-- Sound steps compose (the induction on the rounds in the proof of Proposition 7.8). -/
theorem Sound.bind {S : Finset (V → Bool)} {P Q : PA V → Option (PA V)} (hP : Sound S P)
    (hQ : Sound S Q) : Sound S fun ρ => (P ρ).bind Q := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ h s hs hc
    cases hPρ : P ρ with
    | none => exact hP.fail ρ hPρ s hs hc
    | some σ =>
      rw [hPρ, Option.bind_some] at h
      exact hQ.fail σ h s hs (hP.keep ρ σ hPρ s hs hc)
  · intro ρ τ h
    cases hPρ : P ρ with
    | none => rw [hPρ] at h; simp at h
    | some σ =>
      rw [hPρ, Option.bind_some] at h
      exact (hQ.ext σ τ h).trans (hP.ext ρ σ hPρ)
  · intro ρ τ h s hs hc
    cases hPρ : P ρ with
    | none => rw [hPρ] at h; simp at h
    | some σ =>
      rw [hPρ, Option.bind_some] at h
      exact hQ.keep σ τ h s hs (hP.keep ρ σ hPρ s hs hc)

/-! ### Proposition 7.8: the steps of Ext are sound -/

open ArcsAlgo.Propagation in
/-- **Proposition 7.8, arc consistency** (paper §7.5): the filter `T_c` keeps every solution:
if `s` satisfies `c` and lies in `W`, it lies in `T_c(W)`. -/
theorem filter_keeps [Fintype V] {Val : Type*} [Fintype Val] [DecidableEq Val] (c : Constraint V Val)
    (W : Dom V Val) (s : V → Val) (hs : c.sat s = true) (hW : ∀ v, s v ∈ W v) :
    ∀ v, s v ∈ Propagation.filter c W v := by
  intro v
  simp only [Propagation.filter]
  split_ifs
  · simp only [proj, mem_filter]
    exact ⟨hW v, s, rfl, hs, fun u _ => hW u⟩
  · exact hW v

/-- **Proposition 7.8, local linearization** (paper §7.5, step 2 of Ext): with one input known,
a definition becomes linear; every row so obtained holds on every assignment that satisfies the
definition. -/
theorem local_rows (a b c : Bool) :
    (a && true) = a ∧ (a && false) = false ∧ (a || false) = a ∧ (a || true) = true ∧
      (if true then a else b) = a ∧ (if false then a else b) = b ∧ (if c then a else a) = a := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### Probing -/

/-- Probing one free variable `A` with a propagator `P` (paper §7.5): run `P` with `A = 0` and
with `A = 1`; if both fail, fail; if one fails, adopt the values of the other branch; otherwise
keep the values on which the two branches agree. A variable that is already fixed is probed by
running `P` on the current state. -/
def probeVar (P : PA V → Option (PA V)) (ρ : PA V) (A : V) : Option (PA V) :=
  if ρ A ≠ none then P ρ else
    match P (Function.update ρ A (some false)), P (Function.update ρ A (some true)) with
    | none, none => none
    | none, some r => some r
    | some r, none => some r
    | some r0, some r1 => some fun v => if r0 v = r1 v then r0 v else ρ v

theorem consistent_update {s : V → Bool} {ρ : PA V} (h : Consistent s ρ) (A : V) :
    Consistent s (Function.update ρ A (some (s A))) := by
  intro v b hv
  by_cases hvA : v = A
  · subst hvA; simp at hv; exact hv
  · rw [Function.update_of_ne hvA] at hv; exact h v b hv

theorem extends_update {ρ : PA V} {A : V} (hA : ρ A = none) (a : Bool) :
    Extends (Function.update ρ A (some a)) ρ := by
  intro v b hv
  by_cases hvA : v = A
  · subst hvA; rw [hA] at hv; simp at hv
  · rw [Function.update_of_ne hvA]; exact hv

/-- Every solution consistent with `ρ` lies in one of the two branches. -/
theorem branch {s : V → Bool} {ρ : PA V} (h : Consistent s ρ) (A : V) :
    Consistent s (Function.update ρ A (some false)) ∨ Consistent s (Function.update ρ A (some true)) := by
  cases hs : s A
  · left; rw [← hs]; exact consistent_update h A
  · right; rw [← hs]; exact consistent_update h A

/-- **Proposition 7.10 (soundness of probing)** (paper §7.5): probing one variable with a sound
propagator is sound. -/
theorem probeVar_sound {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P)
    (A : V) : Sound S fun ρ => probeVar P ρ A := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ h s hs hc
    simp only [probeVar] at h
    split_ifs at h with hA
    · exact hP.fail ρ h s hs hc
    split at h <;> try simp at h
    rename_i h0 h1
    rcases branch hc A with hb | hb
    · exact hP.fail _ h0 s hs hb
    · exact hP.fail _ h1 s hs hb
  · intro ρ ρ' h
    simp only [probeVar] at h
    split_ifs at h with hA
    · exact hP.ext ρ ρ' h
    · push Not at hA
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
      · rename_i r _ h1
        exact (hP.ext _ r h1).trans (extends_update hA true)
      · rename_i r h0 _
        exact (hP.ext _ r h0).trans (extends_update hA false)
      · rename_i r0 r1 h0 h1
        intro v b hv
        have e0 := (hP.ext _ r0 h0).trans (extends_update hA false) v b hv
        have e1 := (hP.ext _ r1 h1).trans (extends_update hA true) v b hv
        simp [e0, e1]
  · intro ρ ρ' h s hs hc
    simp only [probeVar] at h
    split_ifs at h with hA
    · exact hP.keep ρ ρ' h s hs hc
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
      · rename_i r h0 h1
        rcases branch hc A with hb | hb
        · exact absurd hb (hP.fail _ h0 s hs)
        · exact hP.keep _ r h1 s hs hb
      · rename_i r h0 h1
        rcases branch hc A with hb | hb
        · exact hP.keep _ r h0 s hs hb
        · exact absurd hb (hP.fail _ h1 s hs)
      · rename_i r0 r1 h0 h1
        intro v b hv
        dsimp only at hv
        split_ifs at hv with hr
        · rcases branch hc A with hb | hb
          · exact hP.keep _ r0 h0 s hs hb v b hv
          · exact hP.keep _ r1 h1 s hs hb v b (hr ▸ hv)
        · exact hc v b hv

/-- **Proposition 7.10, the parity rows** (paper §7.5): if `B` is determined in both branches,
`B = b₀` with `A = 0` and `B = b₁` with `A = 1`, then on every solution consistent with `ρ`,
`B = b₀` when `A = 0` and `B = b₁` when `A = 1` (so `B = A ⊕ b₀` when `b₁ = ¬b₀`, and `B` is forced
when `b₀ = b₁`). -/
theorem probeVar_relation {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P)
    (ρ : PA V) (A B : V) (r0 r1 : PA V) (b0 b1 : Bool)
    (h0 : P (Function.update ρ A (some false)) = some r0) (h1 : P (Function.update ρ A (some true)) = some r1)
    (hb0 : r0 B = some b0) (hb1 : r1 B = some b1) :
    ∀ s ∈ S, Consistent s ρ → s B = if s A then b1 else b0 := by
  intro s hs hc
  cases hsA : s A
  · have := consistent_update hc A
    rw [hsA] at this
    exact hP.keep _ r0 h0 s hs this B b0 hb0
  · have := consistent_update hc A
    rw [hsA] at this
    exact hP.keep _ r1 h1 s hs this B b1 hb1

/-- One round of probing over the variables `vs`. -/
def round (P : PA V → Option (PA V)) : List V → PA V → Option (PA V)
  | [], ρ => some ρ
  | A :: vs, ρ => (probeVar P ρ A).bind (round P vs)

/-- Rounds repeated until nothing changes (at most `k` rounds). -/
def iterRounds [Fintype V] (P : PA V → Option (PA V)) (vs : List V) : ℕ → PA V → Option (PA V)
  | 0, ρ => some ρ
  | k + 1, ρ => (round P vs ρ).bind fun ρ' => if ρ' = ρ then some ρ else iterRounds P vs k ρ'

/-- Probing to depth `ℓ` (paper Proposition 7.10′): `Probe₀ = Ext`, and `Probe_{ℓ+1}` runs
`Probe_ℓ`, then probes every free variable with `Probe_ℓ`, repeated until nothing changes. -/
def probe [Fintype V] (E : PA V → Option (PA V)) (vs : List V) : ℕ → PA V → Option (PA V)
  | 0 => E
  | ℓ + 1 => fun ρ => (probe E vs ℓ ρ).bind (iterRounds (probe E vs ℓ) vs (Fintype.card V + 1))

omit [DecidableEq V] in
theorem sound_some {S : Finset (V → Bool)} : Sound S (fun ρ : PA V => some ρ) :=
  ⟨fun _ h => by simp at h, fun _ _ h => by simp at h; subst h; exact fun _ _ h => h,
    fun _ _ h _ _ hc => by simp at h; subst h; exact hc⟩

theorem round_sound {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P) :
    ∀ vs : List V, Sound S (round P vs)
  | [] => sound_some
  | A :: vs => (probeVar_sound hP A).bind (round_sound hP vs)

theorem iterRounds_sound [Fintype V] {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P)
    (vs : List V) : ∀ k, Sound S (iterRounds P vs k)
  | 0 => sound_some
  | k + 1 => by
    · refine ⟨?_, ?_, ?_⟩
      · intro ρ hρ s hs hc
        simp only [iterRounds] at hρ
        cases hr : round P vs ρ with
        | none => exact (round_sound hP vs).fail ρ hr s hs hc
        | some ρ' =>
          rw [hr, Option.bind_some] at hρ
          split_ifs at hρ
          exact (iterRounds_sound hP vs k).fail ρ' hρ s hs ((round_sound hP vs).keep ρ ρ' hr s hs hc)
      · intro ρ τ hρ
        simp only [iterRounds] at hρ
        cases hr : round P vs ρ with
        | none => rw [hr] at hρ; simp at hρ
        | some ρ' =>
          rw [hr, Option.bind_some] at hρ
          split_ifs at hρ with he
          · simp at hρ; subst hρ; exact fun _ _ h => h
          · exact ((iterRounds_sound hP vs k).ext ρ' τ hρ).trans ((round_sound hP vs).ext ρ ρ' hr)
      · intro ρ τ hρ s hs hc
        simp only [iterRounds] at hρ
        cases hr : round P vs ρ with
        | none => rw [hr] at hρ; simp at hρ
        | some ρ' =>
          rw [hr, Option.bind_some] at hρ
          split_ifs at hρ with he
          · simp at hρ; subst hρ; exact hc
          · exact (iterRounds_sound hP vs k).keep ρ' τ hρ s hs ((round_sound hP vs).keep ρ ρ' hr s hs hc)

/-- **Proposition 7.10′ (a)** (paper §7.5): every value found by `Probe_ℓ` holds on every
solution, and `Probe_ℓ` fails only when no solution is consistent with `ρ`. -/
theorem probe_sound [Fintype V] {S : Finset (V → Bool)} {E : PA V → Option (PA V)} (hE : Sound S E)
    (vs : List V) : ∀ ℓ, Sound S (probe E vs ℓ)
  | 0 => hE
  | ℓ + 1 => (probe_sound hE vs ℓ).bind (iterRounds_sound (probe_sound hE vs ℓ) vs _)

/-! ### Proposition 7.10′ (b): the cost -/

/-- Calls to `Ext` in one round of probing to depth `ℓ` when every inner call of `Probe_{ℓ−1}`
is one round: `c₀ = 1`, `c_ℓ = 2n·c_{ℓ−1}`. -/
def callsOneRound (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | ℓ + 1 => 2 * n * callsOneRound n ℓ

/-- **Proposition 7.10′ (b)** (paper §7.5): if each inner `Probe_{ℓ−1}` runs a single round, one
round of probing to depth `ℓ` makes `2n` calls of `Probe_{ℓ−1}`, hence `(2n)^ℓ` runs of Ext. -/
theorem probe_cost (n ℓ : ℕ) : callsOneRound n ℓ = (2 * n) ^ ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [callsOneRound, ih, pow_succ, mul_comm]

/-! ### Proposition 7.10′ (c): completeness with a strong backdoor -/

/-- `Bs` is a strong backdoor for `E` at `ρ` [WGS]: for every extension of `ρ` that assigns every
variable of `Bs`, `E` either fails or returns a solution. -/
def StrongBackdoor (S : Finset (V → Bool)) (E : PA V → Option (PA V)) (ρ : PA V) (Bs : Finset V) :
    Prop :=
  ∀ σ, Extends σ ρ → (∀ v ∈ Bs, σ v ≠ none) →
    E σ = none ∨ ∃ s ∈ S, Consistent s σ ∧ E σ = some fun v => some (s v)

/-- `P` decides at `ρ`: it fails exactly when no solution is consistent with `ρ`, and otherwise it
fixes every variable that is constant on the solutions consistent with `ρ`. -/
def Decides (S : Finset (V → Bool)) (P : PA V → Option (PA V)) (ρ : PA V) : Prop :=
  (P ρ = none ↔ ∀ s ∈ S, ¬ Consistent s ρ) ∧
    ∀ ρ', P ρ = some ρ' → (∃ s ∈ S, Consistent s ρ) →
      ∀ v b, (∀ s ∈ S, Consistent s ρ → s v = b) → ρ' v = some b

omit [DecidableEq V] in
theorem consistent_of_extends {s : V → Bool} {σ ρ : PA V} (h : Extends σ ρ) (hs : Consistent s σ) :
    Consistent s ρ := fun v b hv => hs v b (h v b hv)

theorem backdoor_mono {S : Finset (V → Bool)} {E : PA V → Option (PA V)} {ρ τ : PA V}
    {A : V} {Bs : Finset V} (h : StrongBackdoor S E ρ (insert A Bs)) (hτ : Extends τ ρ)
    (hA : τ A ≠ none) : StrongBackdoor S E τ Bs := by
  intro σ hσ hB
  apply h σ (hσ.trans hτ)
  intro v hv
  rcases Finset.mem_insert.1 hv with rfl | hv
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hA
    rw [hσ v b hb]; simp
  · exact hB v hv

omit [DecidableEq V] in
theorem decides_bind {S : Finset (V → Bool)} {P Q : PA V → Option (PA V)} {ρ : PA V}
    (hd : Decides S P ρ) (hP : Sound S P) (hQ : Sound S Q) :
    Decides S (fun σ => (P σ).bind Q) ρ := by
  constructor
  · constructor
    · intro h s hs hc
      cases hPρ : P ρ with
      | none => exact hd.1.1 hPρ s hs hc
      | some ρ1 =>
        simp only [hPρ, Option.bind_some] at h
        exact hQ.fail ρ1 h s hs (hP.keep ρ ρ1 hPρ s hs hc)
    · intro h
      simp [hd.1.2 h]
  · intro ρ' h hex v b hb
    cases hPρ : P ρ with
    | none => simp [hPρ] at h
    | some ρ1 =>
      simp only [hPρ, Option.bind_some] at h
      exact hQ.ext ρ1 ρ' h v b (hd.2 ρ1 hPρ hex v b hb)

omit [DecidableEq V] in
theorem sols_of_some {S : Finset (V → Bool)} {P : PA V → Option (PA V)} {σ r : PA V}
    (hσ : Decides S P σ) (hr : P σ = some r) : ∃ s ∈ S, Consistent s σ := by
  by_contra hne
  push Not at hne
  have := hσ.1.2 hne
  rw [hr] at this
  simp at this

theorem probeVar_decides {S : Finset (V → Bool)} {P : PA V → Option (PA V)}
    {ρ : PA V} {A : V} (hIH : ∀ τ, Extends τ ρ → τ A ≠ none → Decides S P τ)
    {τ : PA V} (hτ : Extends τ ρ) : Decides S (fun σ => probeVar P σ A) τ := by
  by_cases hA : τ A ≠ none
  · have hd := hIH τ hτ hA
    have he : probeVar P τ A = P τ := by simp [probeVar, hA]
    unfold Decides at hd ⊢
    dsimp only
    rw [he]; exact hd
  push Not at hA
  have e0 : Extends (Function.update τ A (some false)) τ := extends_update hA false
  have e1 : Extends (Function.update τ A (some true)) τ := extends_update hA true
  have h0 := hIH _ (e0.trans hτ) (by simp)
  have h1 := hIH _ (e1.trans hτ) (by simp)
  have hpv : probeVar P τ A =
      match P (Function.update τ A (some false)), P (Function.update τ A (some true)) with
      | none, none => none
      | none, some r => some r
      | some r, none => some r
      | some r0, some r1 => some fun v => if r0 v = r1 v then r0 v else τ v := by
    simp [probeVar, hA]
  show (probeVar P τ A = none ↔ _) ∧ ∀ ρ', probeVar P τ A = some ρ' → _
  rw [hpv]
  cases hr0 : P (Function.update τ A (some false)) with
  | none =>
    cases hr1 : P (Function.update τ A (some true)) with
    | none =>
      refine ⟨⟨fun _ s hs hc => ?_, fun _ => rfl⟩, fun ρ' h => by simp at h⟩
      rcases branch hc A with hb | hb
      · exact h0.1.1 hr0 s hs hb
      · exact h1.1.1 hr1 s hs hb
    | some r1 =>
      obtain ⟨s1, hs1, hc1⟩ := sols_of_some h1 hr1
      refine ⟨⟨fun h => by simp at h, fun h => absurd (consistent_of_extends e1 hc1) (h s1 hs1)⟩, ?_⟩
      intro ρ' h _ v b hb
      simp only [Option.some.injEq] at h
      subst h
      exact h1.2 _ hr1 ⟨s1, hs1, hc1⟩ v b fun s hs hc => hb s hs (consistent_of_extends e1 hc)
  | some r0 =>
    cases hr1 : P (Function.update τ A (some true)) with
    | none =>
      obtain ⟨s0, hs0, hc0⟩ := sols_of_some h0 hr0
      refine ⟨⟨fun h => by simp at h, fun h => absurd (consistent_of_extends e0 hc0) (h s0 hs0)⟩, ?_⟩
      intro ρ' h _ v b hb
      simp only [Option.some.injEq] at h
      subst h
      exact h0.2 _ hr0 ⟨s0, hs0, hc0⟩ v b fun s hs hc => hb s hs (consistent_of_extends e0 hc)
    | some r1 =>
      obtain ⟨s0, hs0, hc0⟩ := sols_of_some h0 hr0
      obtain ⟨s1, hs1, hc1⟩ := sols_of_some h1 hr1
      refine ⟨⟨fun h => by simp at h, fun h => absurd (consistent_of_extends e0 hc0) (h s0 hs0)⟩, ?_⟩
      intro ρ' h _ v b hb
      simp only [Option.some.injEq] at h
      subst h
      have a0 := h0.2 _ hr0 ⟨s0, hs0, hc0⟩ v b fun s hs hc => hb s hs (consistent_of_extends e0 hc)
      have a1 := h1.2 _ hr1 ⟨s1, hs1, hc1⟩ v b fun s hs hc => hb s hs (consistent_of_extends e1 hc)
      simp [a0, a1]

omit [DecidableEq V] in
/-- A step that keeps the solutions transfers decision from the new state to the old one. -/
theorem decides_after {S : Finset (V → Bool)} {Q : PA V → Option (PA V)} {τ τ' : PA V}
    (hext : Extends τ' τ) (hkeep : ∀ s ∈ S, Consistent s τ → Consistent s τ')
    (hd : Decides S Q τ') :
    (Q τ' = none ↔ ∀ s ∈ S, ¬ Consistent s τ) ∧
      ∀ ρ', Q τ' = some ρ' → (∃ s ∈ S, Consistent s τ) →
        ∀ v b, (∀ s ∈ S, Consistent s τ → s v = b) → ρ' v = some b := by
  refine ⟨⟨fun h s hs hc => hd.1.1 h s hs (hkeep s hs hc),
    fun h => hd.1.2 fun s hs hc => h s hs (consistent_of_extends hext hc)⟩, ?_⟩
  intro ρ' h hex v b hb
  obtain ⟨s0, hs0, hc0⟩ := hex
  exact hd.2 ρ' h ⟨s0, hs0, hkeep s0 hs0 hc0⟩ v b fun s hs hc => hb s hs (consistent_of_extends hext hc)

theorem round_cons (P : PA V → Option (PA V)) (A : V) (vs : List V) :
    round P (A :: vs) = fun ρ => (probeVar P ρ A).bind (round P vs) := rfl

theorem round_decides {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P)
    {ρ : PA V} {A : V} (hIH : ∀ τ, Extends τ ρ → τ A ≠ none → Decides S P τ) :
    ∀ vs : List V, A ∈ vs → ∀ τ, Extends τ ρ → Decides S (round P vs) τ
  | [], h => by simp at h
  | B :: rest, hmem => by
    intro τ hτ
    rw [round_cons]
    by_cases hBA : B = A
    · subst hBA
      exact decides_bind (probeVar_decides hIH hτ) (probeVar_sound hP B) (round_sound hP rest)
    · have hA' : A ∈ rest := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm hBA
        · exact h
      unfold Decides
      dsimp only
      cases hpb : probeVar P τ B with
      | none =>
        refine ⟨⟨fun _ => (probeVar_sound hP B).fail τ hpb, fun _ => rfl⟩, fun ρ' h => by simp at h⟩
      | some τ'' =>
        simp only [Option.bind_some]
        have hext := (probeVar_sound hP B).ext τ τ'' hpb
        exact decides_after hext (fun s hs hc => (probeVar_sound hP B).keep τ τ'' hpb s hs hc)
          (round_decides hP hIH rest hA' τ'' (hext.trans hτ))

theorem iterRounds_decides [Fintype V] {S : Finset (V → Bool)} {P : PA V → Option (PA V)} (hP : Sound S P)
    {ρ : PA V} {A : V} (hIH : ∀ τ, Extends τ ρ → τ A ≠ none → Decides S P τ)
    (vs : List V) (hA : A ∈ vs) (k : ℕ) (τ : PA V) (hτ : Extends τ ρ) :
    Decides S (iterRounds P vs (k + 1)) τ := by
  have hr := round_decides hP hIH vs hA τ hτ
  unfold Decides
  simp only [iterRounds]
  cases hrt : round P vs τ with
  | none =>
    refine ⟨⟨fun _ => hr.1.1 hrt, fun _ => rfl⟩, fun ρ' h => by simp at h⟩
  | some τ' =>
    simp only [Option.bind_some]
    obtain ⟨s0, hs0, hc0⟩ := sols_of_some hr hrt
    have hkeep := fun s hs hc => (round_sound hP vs).keep τ τ' hrt s hs hc
    have hext := (round_sound hP vs).ext τ τ' hrt
    refine ⟨⟨fun h => ?_, fun h => absurd hc0 (h s0 hs0)⟩, ?_⟩
    · split_ifs at h with he
      exact absurd (hkeep s0 hs0 hc0) ((iterRounds_sound hP vs k).fail τ' h s0 hs0)
    · intro ρ' h hex v b hb
      have hv := hr.2 τ' hrt hex v b hb
      split_ifs at h with he
      · simp only [Option.some.injEq] at h
        subst h; rw [← he]; exact hv
      · exact (iterRounds_sound hP vs k).ext τ' ρ' h v b hv

/-- **Proposition 7.10′ (c)** (paper §7.5; `Probe_ℓ` probes every variable, already fixed or not):
if some set `Bs` of at most `ℓ` variables is a strong backdoor for Ext at `ρ` [WGS] (for every
assignment of `Bs`, Ext either fails or returns a solution), then `Probe_ℓ` fails if and only if no
solution is consistent with `ρ`, and otherwise fixes every variable that is constant on the
solutions. -/
theorem probe_complete [Fintype V] {S : Finset (V → Bool)} {E : PA V → Option (PA V)} (hE : Sound S E)
    (vs : List V) (hvs : ∀ v, v ∈ vs) :
    ∀ ℓ (ρ : PA V) (Bs : Finset V), Bs.card ≤ ℓ → StrongBackdoor S E ρ Bs →
      Decides S (probe E vs ℓ) ρ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ρ Bs hcard hB
    have hBs : Bs = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hBs
    rcases hB ρ (fun _ _ h => h) (by simp) with hn | ⟨s, hs, hc, hEρ⟩
    · exact ⟨⟨fun _ => hE.fail ρ hn, fun _ => hn⟩, fun ρ' h => by simp [probe, hn] at h⟩
    · refine ⟨⟨fun h => by simp [probe, hEρ] at h, fun h => absurd hc (h s hs)⟩, ?_⟩
      intro ρ' h _ v b hb
      simp only [probe, hEρ, Option.some.injEq] at h
      subst h
      simp [hb s hs hc]
  | succ ℓ ih =>
    intro ρ Bs hcard hB
    have hPsound := probe_sound hE vs ℓ
    by_cases hc : Bs.card ≤ ℓ
    · exact decides_bind (ih ρ Bs hc hB) hPsound (iterRounds_sound hPsound vs _)
    · obtain ⟨A, hA⟩ : Bs.Nonempty := Finset.card_pos.1 (by omega)
      have hcard' : (Bs.erase A).card ≤ ℓ := by rw [Finset.card_erase_of_mem hA]; omega
      have hB' : StrongBackdoor S E ρ (insert A (Bs.erase A)) := by
        rwa [Finset.insert_erase hA]
      have hIH : ∀ τ, Extends τ ρ → τ A ≠ none → Decides S (probe E vs ℓ) τ :=
        fun τ hτ hτA => ih τ _ hcard' (backdoor_mono hB' hτ hτA)
      unfold Decides
      simp only [probe]
      cases hP : probe E vs ℓ ρ with
      | none =>
        exact ⟨⟨fun _ => hPsound.fail ρ hP, fun _ => rfl⟩, fun ρ' h => by simp at h⟩
      | some ρ1 =>
        simp only [Option.bind_some]
        have hext := hPsound.ext ρ ρ1 hP
        exact decides_after hext (fun s hs hc => hPsound.keep ρ ρ1 hP s hs hc)
          (iterRounds_decides hPsound hIH vs (hvs A) (Fintype.card V) ρ1 hext)

end ArcsAlgo.Probing
