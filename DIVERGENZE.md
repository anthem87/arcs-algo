# Divergenze tra il paper e gli enunciati Lean (10 voci)

## Introduzione

Questo documento serve ad allineare il `.tex` del paper *Arcs of Π(1+z^p): prime races, the Gaussian core, Dirichlet L-functions and a certified solver for Subset Sum* (A. Mennillo) con gli enunciati effettivamente dimostrati in Lean 4.

- **Paper**: `~/Projects/prism-polya/release/ALGO_13/paper/paper_subset_arcs_propagation_rev1.md`, versione del 2 novembre 2026, ore 01:00. Tutti i numeri di riga si riferiscono a questo file. Le citazioni sono testuali; con "[…]" si omettono parti identiche in Lean.
- **Lean**: `~/Projects/arcs-algo/lean/ArcsAlgo/` (i percorsi sotto sono relativi a questa cartella). Gli enunciati Lean sono copiati testualmente dal sorgente, dalla parola `theorem`/`def` fino a `:= by` escluso (o fino alla fine della definizione).
- **Checklist**: `~/Projects/prism-polya/release/ALGO_13/LEAN_CHECKLIST_61.md`, sezione "Status".

Avvertenza importante. Il file rev1 contiene **già** parecchie delle correzioni elencate nella checklist (per esempio la nuova β(L) nel Lemma Q, e^{g²/2} nel Lemma V e nel Teorema R″, λ_m al posto di ρ_m, l'ordine topologico sulle classi nel Teorema 7.2, μ(W) + 1 nel Teorema 7.4, "finitely supported law" nel Lemma J, c₂(M, u) nella Proposizione B′). Il confronto sotto è quindi **rev1 contro Lean**. Dove una correzione della checklist è già nel rev1 lo segnalo, così si può controllare che il `.tex` sia allineato al rev1 e non a una versione precedente. Per il Lemma B riporto anche il testo della versione precedente (`paper_subset_arcs_propagation.md`), perché è quella con O(m^{−1/2+3η}) per ogni η ∈ (0, 1/6).

Le ipotesi classiche (Siegel–Walfisz, Vinogradov–Vaughan, Jackson, Rosser–Schoenfeld, [BR, Thm 22.1]) compaiono in Lean come argomenti di tipo `Prop` (`hSW : SiegelWalfisz` ecc.), non come assiomi.

## Tabella riassuntiva

| # | Voce | Riga paper | Dichiarazioni Lean principali | Tipo di divergenza |
|---|---|---|---|---|
| 1 | Lemma Q | 171 | `LemmaQ.lean`: `lemmaQ1`, `lemmaQ1_avg`, `lemmaQ2`, `rhsQ_anti`, `lemmaQ2_Rq`, `Rq_bound`, `Rq_bound_tau`, `lemmaQ3`; `RemarkLobe.lean`: `anti_first_min` | allineato al rev1 attuale; Lean più generale in (2), (3) (q ≥ 1, ogni X > 0, 2^{ω(q)} ≤ τ(q)); ℓ_q ≤ R_q non enunciato a sé |
| 2 | Teorema E | 280 | `EdgeE2.lean`: `thmE`, `thmE2`; `ThmE1.lean`: `thmE1`, `thmE1_B40`; `ThmE3.lean`: `thmE3`; `EdgeRel.lean`: `thmE2_rel` | allineato al rev1 attuale (s̃* nel caso 𝒱 = {w}; ℓ*_q in (2) e (3), ora `ellq` anche in Lean); Lean più esplicito: δ con N₀(δ), costanti esplicite, termini esponenzialmente piccoli a parte; B > 40 serve solo per (1) |
| 3 | Remark (the formula of Proposition C) | 311 | `RemarkPropC.lean`: `thmC2_rel`, `thmC2_paper`; `RemarkPropCV.lean`: `thmC2_vanish` | allineato al rev1 attuale; antecedente esplicito \|ν\| ≤ C_νN^{3/2+ε/2}; Lean più forte nel caso 𝒱 = ∅ (−1 + 6ε, costante 12); q ∈ 𝔈 non richiesto |
| 4 | Proposizione B′ | 722 | `SecondMoment/BPCondT.lean`: `propBprime_cond`; `SecondMoment/BPUT.lean`: `propBprime_uncond`; `SecondMoment/BPConst.lean`: `CCu_eq` | allineato al rev1 attuale (λ al denominatore, condizionamento sulla parità); g ≥ 0; [BR, Theorem 22.1] come ipotesi; limiti per M → ∞ formalizzati |
| 5 | Teorema 7.2 | 981 | `Structural.lean`: `Tstruct_idem`, `Tstruct_of_closed`, `inject_dom`, `Eval_fixes`, `Eval_nonempty`, `Eval_fixes_exactly`, `Eval_blocks_counterexample`, `parity_supported`, `def_supported`, `Tstruct_not_idem_counterexample` | allineato al rev1 attuale; Lean ha Val = Bool, il paper Val generico (§8 formalizzato a parte in `Chain.lean`); Par dato dal suo risultato; costi O(·) non formalizzati |
| 6 | Teorema 7.4 | 1001 | `Propagation.lean`: `Tcomp_le`, `Tcomp_mono`, `Tcomp_eq_self_iff`, `Tfail_stable`, `Tcomp_bound_counterexample`, `limit_greatest`, `limit_supported`, `limit_perm`, `schedule_eq_limit` | allineato al rev1 attuale (V e Val finiti, T_fail, domini non vuoti); (iv) come permutazione o schedule; vincoli generici |
| 7 | Lemma J | 877 | `RandomWeights.lean`: `roundSuccess_ge` | allineato al rev1 attuale; forma astratta (masse non normalizzate, Z_r arbitrari); convenzione 0/0 = 0 |
| 8 | Lemma V | 907 | `Uniform/LemV2.lean`: `lemmaV`, `sum_pairPA`, `DeqA`; `Uniform/RppRate.lean`: `lemmaV_core`, `lemmaV_rate` | allineato al rev1 attuale (enunciato e prova): (1 + O(m^{−1/5})) = (1 + C(g) m^{−1/5}) con m₀(g) (`lemmaV_rate`); anche la forma (1 + ε) con m₀(g, ε) (`lemmaV`); g ≥ 0; il denominatore è λ = E[Z \| S_E = s], ora anche nel paper; e^{g²/2} già nel rev1 |
| 9 | Teorema R″ | 930 | `Uniform/RppRound.lean`: `succB_ge`, `succB_unif`, `pRpp`; `Uniform/RppRounds.lean`: `thmRpp_gen`; `Uniform/RppAsymp.lean`: `Hm`, `exists_Hm`, `params_Rpp`, `thmRpp`; `Uniform/RppRate.lean`: `pRate`, `succB_rate`, `thmRpp_rate`, `Hm_of_isLeast`, `pRate_ge`, `thmRpp_asymp` | allineato al rev1 attuale: p_rate (`thmRpp_rate`, `ARCS.theoremR''_rate`) e parte asintotica con m minimo, P₀ = ⌊λ_m/2⌋, R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})p_rate)⌉ (`thmRpp_asymp`, `ARCS.theoremR''`); O(m^{−1/5}) come C(g) m^{−1/5}, o(1) come ε, "M large" come M ≥ M₀; la forma con ε (`thmRpp`) resta nella libreria; costo e tempo non formalizzati |
| 10 | Lemma B | 696 | `Uniform/LemmaB1.lean`: `lemmaB1_unif`; `Uniform/LemmaB2.lean`: `lemmaB2_unif`, `lemmaB3_unif`, `lemmaB2_rate`, `lemmaB3_rate`; `SecondMoment/LemmaB.lean`: `lemmaB_fixedM` | (2), (3): tasso O(m^{−1/5}) uniforme in M dimostrato (rev1 coperto); non coperto O(m^{−1/2+3η}) per ogni η (versione precedente); (1) in forma o(1); g ≥ 0 |

---

## 1. Lemma Q

### Paper (riga 171, rev1 attuale)

> **Lemma Q (lobes of every arc).** Let q ≥ 3, h_q(x) = log|Φ_q(−e(x))| and κ = Cl₂(π/3)/π = 0.32307…
> 1. h_q is strictly decreasing on [0, 1/(2q)), so A_q is strictly decreasing on (0, 1/(2q)), A_q(X) < φ(q)c_q for 0 < X < 1/(2q), and X_q ≥ 1/(2q).
> 2. For every X ≥ 1/(2q),
> $$A_q(X)\le\sum_{\mu(q/d)=1}\min\Big(\log 2,\frac{\kappa}{dX}\Big)+\sum_{\mu(q/d)=-1}\beta(dX),\qquad \beta(L)=\begin{cases}\max\Big(\kappa,\ \min\big(\kappa/L,\ \log\tfrac{e}{2L}\big)\Big) & L\le1,\\ \kappa/L & L>1,\end{cases}$$
> and the right side is non-increasing in X. Writing R_q for its value at X = 1/(2q) divided by φ(q),
> $$\ell_q\le R_q\le\frac{2^{\omega(q)-1}(1+\log2+\log\operatorname{rad}q)}{\varphi(q)}\le\frac{\tau(q)\log(2eq)}{2\varphi(q)}.$$
> 3. For X ≥ 1, A_q(X)/φ(q) ≤ κτ(q)/φ(q).

Definizioni usate (riga 142): A_q(X) = X⁻¹∫₀^X log|Φ_q(−e(x))| dx, con A_q(0) = log|Φ_q(−1)|; c_q = A_q(0)/φ(q); ℓ_q = sup{A_q(X)/φ(q) : X ≥ X_q}, dove X_q è il primo minimo locale di A_q.

### Lean

Definizioni (`LemmaP.lean:36`, `:39`; `Clausen.lean:36`; `LemmaQ.lean:273`, `:277`; `RemarkLobe.lean:217`):

```lean
noncomputable def hq (q : ℕ) (x : ℝ) : ℝ := Real.log ‖(cyclotomic q ℂ).eval (-ee x)‖
noncomputable def Aq (q : ℕ) (X : ℝ) : ℝ := (∫ x in (0 : ℝ)..X, hq q x) / X
noncomputable def kappa : ℝ := -2 * Cl (1 / 6)
noncomputable def betaQ (L : ℝ) : ℝ :=
  if L ≤ 1 then max kappa (min (kappa / L) (Real.log (Real.exp 1 / (2 * L)))) else kappa / L
noncomputable def termQ (m : ℤ) (L : ℝ) : ℝ :=
  if m = 1 then min (Real.log 2) (kappa / L) else if m = -1 then betaQ L else 0
def firstLocalMin (q : ℕ) (X : ℝ) : Prop :=
  0 < X ∧ IsLocalMin (Aq q) X ∧ ∀ y ∈ Set.Ioo 0 X, ¬ IsLocalMin (Aq q) y
```

(1) — `ArcsAlgo.Core.lemmaQ1` (`LemmaQ.lean:624`), `ArcsAlgo.Core.lemmaQ1_avg` (`LemmaQ.lean:655`), `ArcsAlgo.Core.anti_first_min` (`RemarkLobe.lean:222`):

```lean
theorem lemmaQ1 {q : ℕ} (h3 : 3 ≤ q) : StrictAntiOn (hq q) (Set.Ico 0 (1 / (2 * q)))
```
```lean
theorem lemmaQ1_avg {q : ℕ} (h3 : 3 ≤ q) :
    (∀ X ∈ Set.Ioo (0 : ℝ) (1 / (2 * q)), Aq q X < hq q 0) ∧
      StrictAntiOn (Aq q) (Set.Ioo 0 (1 / (2 * q)))
```
```lean
theorem anti_first_min {q : ℕ} (h3 : 3 ≤ q) {Xq : ℝ} (hX : firstLocalMin q Xq) :
    1 / (2 * q) ≤ Xq ∧ ∀ x y, 0 < x → x ≤ y → y ≤ Xq → Aq q y ≤ Aq q x
```

(2) — `lemmaQ2` (`LemmaQ.lean:319`), `rhsQ_anti` (`:347`), `lemmaQ2_Rq` (`:356`), `Rq_bound` (`:423`), `Rq_bound_tau` (`:471`):

```lean
theorem lemmaQ2 {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 0 < X) :
    Aq q X ≤ ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X)
```
```lean
theorem rhsQ_anti {q : ℕ} {X X' : ℝ} (hX : 0 < X) (hXX : X ≤ X') :
    ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X') ≤
      ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * X)
```
```lean
theorem lemmaQ2_Rq {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 1 / (2 * q) ≤ X) :
    Aq q X ≤ ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q)))
```
```lean
theorem Rq_bound {q : ℕ} (hq : 1 < q) :
    ∑ y ∈ q.divisorsAntidiagonal, termQ (μ y.1) (y.2 * (1 / (2 * q))) ≤
      (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q))
```
```lean
theorem Rq_bound_tau {q : ℕ} (hq : 1 < q) :
    (2 : ℝ) ^ ω q / 2 * (1 + Real.log 2 + Real.log (radQ q)) ≤
      (q.divisors.card : ℝ) * Real.log (2 * Real.exp 1 * q) / 2
```

(3) — `lemmaQ3` (`LemmaQ.lean:498`):

```lean
theorem lemmaQ3 {q : ℕ} (hq0 : 0 < q) {X : ℝ} (hX : 1 ≤ X) : Aq q X ≤ kappa * 2 ^ ω q
```

**Lettura.** κ = −2Cl(1/6) con Cl(u) = ∫₀^u log|2 sin πt| dt (quindi κ = Cl₂(π/3)/π). (1) Per q ≥ 3, h_q è strettamente decrescente su [0, 1/(2q)). Per 0 < X < 1/(2q) vale A_q(X) < h_q(0) = φ(q)c_q, e A_q è strettamente decrescente su (0, 1/(2q)). Per ogni primo minimo locale X_q di A_q si ha X_q ≥ 1/(2q), e A_q è non crescente su (0, X_q]. (2) Per q ≥ 1 e **ogni** X > 0 vale A_q(X) ≤ Σ_{d|q} term(μ(q/d), dX), con il β corretto; il membro destro è non crescente in X; quindi A_q(X) ≤ φ(q)R_q per X ≥ 1/(2q). Per q ≥ 2: φ(q)R_q ≤ 2^{ω(q)−1}(1 + log 2 + log rad q) ≤ τ(q) log(2eq)/2. (3) Per q ≥ 1 e X ≥ 1: A_q(X) ≤ κ·2^{ω(q)}.

### Differenza

- **β(L)**: la formula del rev1 coincide con `betaQ`. La correzione della checklist è dunque già nel rev1. Va controllato che il `.tex` non riporti ancora il β precedente, che non è non crescente perché κ > 1 − log 2.
- **(1)**: **allineato al rev1 attuale.** Il paper dice ora "strictly decreasing on [0, 1/(2q))", A_q strettamente decrescente su (0, 1/(2q)) e A_q(X) < φ(q)c_q per 0 < X < 1/(2q), come `lemmaQ1` e `lemmaQ1_avg`; X_q ≥ 1/(2q) è `anti_first_min` (per ogni primo minimo locale X_q).
- **(2)**: Lean vale per ogni X > 0 e q ≥ 1, il paper per X ≥ 1/(2q) e q ≥ 3 (Lean è più generale). La catena "ℓ_q ≤ R_q" **non è enunciata come teorema Lean a sé**. Lean ha A_q(X) ≤ φ(q)R_q per X ≥ 1/(2q) (`lemmaQ2_Rq`), da cui ℓ_q ≤ R_q segue con X_q ≥ 1/(2q) (`anti_first_min`). Le due stime di R_q valgono in Lean per q ≥ 2.
- **(3)**: Lean dimostra A_q(X) ≤ κ·2^{ω(q)} per q ≥ 1, che è più forte di κτ(q) perché 2^{ω(q)} ≤ τ(q). La forma con τ(q) non è un enunciato Lean separato (compare solo nel docstring).

**Wording suggerito.**
Nessuno: il Lemma Q del rev1 attuale corrisponde a `lemmaQ1`, `lemmaQ1_avg`, `anti_first_min`, `lemmaQ2`–`Rq_bound_tau`, `lemmaQ3` (Lean è più generale in (2) e (3): ogni X > 0, q ≥ 1, e κ·2^{ω(q)} ≤ κτ(q)). ℓ_q ≤ R_q segue da `lemmaQ2_Rq` e `anti_first_min`, senza un teorema Lean a sé.

---

## 2. Teorema E (arc expansion)

### Paper (riga 280, rev1 attuale)

> **Theorem E (arc expansion).** Fix B > 40 (B = 48 makes the error in (1) O(1/log N)) and 0 < ε < 1/8 (the statements for larger ε follow). As N → ∞, for 3 ≤ q ≤ 𝔓:
> 1. (minor arcs) sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + O((log N)^{5−B/8}) + O(M^{−1/2}))π(N)).
> 2. (emerging arcs) Let q ∈ 𝔈. With the cumulants κ_j* of Lemma W(3), s* = √κ₂* and z = (T − κ₁*)/s*, put
> $$\widehat H(T)=e^{-iTt^*}\,G(\theta^*)\,\frac{\varphi(z)}{s^*}\Big(1+\frac{\kappa_3^*}{6s^{*3}}He_3(z)+\frac{\kappa_4^*}{24s^{*4}}He_4(z)+\frac{\kappa_3^{*2}}{72s^{*6}}He_6(z)\Big).$$
> If 𝒱(a/q) = ∅, put 𝒜*_{a/q}(T) = e(−Ta/q)Ĥ(T) and Ω = 1. If 𝒱(a/q) = {w}, write 1 + e(wθ) = −iwt·e^{iwt/2}sinc(wt/2) and replace G by G̃ = G·e^{iwt/2}sinc(wt/2) in Ĥ: its value G̃(θ*) = G(θ*)e^{iwt*/2}sinc(wt*/2) replaces G(θ*), and the cumulants of G̃ at t*, those of G plus those of e^{iwt/2}sinc(wt/2) at t* (see the note after the theorem), replace the κ_j*. Put 𝒜*_{a/q}(T) = e(−Ta/q)·w·(d/dT)Ĥ(T) and Ω = w(|t*| + 1/s̃*), where s̃* is the square root of the second cumulant of G̃ at t*; s̃* takes the place of s* in Ĥ, in Ω and in the error term below. θ* stays the peak of |G|. Then, for every T,
> $$R_{a/q}(T)=\mathcal A^*_{a/q}(T)+O\Big(\Omega\,|G(\theta^*)|\,\frac{N^{-3/2+2\varepsilon}}{s^*}\Big)+O\big(2^ne^{(-\log2+\ell^*_q+o(1))\pi(N)}\big),\qquad \ell^*_q=\sup_{X\ge1/(2q)}\frac{A_q(X)}{\varphi(q)} .$$
> In particular, if 𝒱(a/q) = ∅, then R_{a/q}(T) = 𝒜*_{a/q}(T)(1 + O(N^{−1+2ε})) + O(2^n e^{(−log 2 + ℓ*_q + o(1))π(N)}) uniformly for |z| ≤ √(log N).
> 3. (other arcs) For q ∉ 𝔈, |R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ*_q + o(1))π(N)), and ℓ*_q = ℓ_q whenever A_q has a first local minimum X_q (Remark below).

### Lean

Enunciato riassuntivo `ArcsAlgo.Core.thmE` (`EdgeE2.lean:136`):

```lean
theorem thmE (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 40 < B)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ θ : ℝ, minorArc B N θ →
        ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 + δ) * Nat.primeCounting N)) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((∀ w ∈ WN N, ¬ vanish q a w) →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sS N ((a : ℝ) / q + ts / (2 * π)) +
                5 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))) ∧
        (∀ w₀ ∈ WN N, vanish q a w₀ →
          ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ ts T) T)‖ ≤
            ‖Gw (WN N) q a ((a : ℝ) / q + ts / (2 * π))‖ *
              (w₀ * (|ts| + 1 / sV N q a w₀ ts) * ((N : ℝ) ^ (-(3 / 2 : ℝ) + 2 * ε) / sV N q a w₀ ts) +
                w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
                4 * Real.exp (-((N : ℝ) ^ (2 * ε)) / (512 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N)))) ∧
      (∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q → ¬ emerging q → ∀ T : ℝ,
        ‖Rarc B N q a T‖ ≤
          2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))
```

I tre congiunti sono rispettivamente:
- (1) `thmE1_B40` (`ThmE1.lean:561`), con ipotesi `40 < B` e la stessa conclusione del primo congiunto, ricavata dalla forma esplicita `thmE1` (`ThmE1.lean:309`):

```lean
theorem thmE1 (hSW : SiegelWalfisz) (hVV : VinogradovVaughan) (hJ : JacksonThm) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ θ : ℝ, minorArc B N θ →
      ‖FW (WN N) θ‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 +
        C * (Real.log N ^ (5 - B / 8) + (Real.log N ^ (B / 4)) ^ (-(1 / 2 : ℝ)))) * Nat.primeCounting N)
```
- (2) `thmE2` (`EdgeE2.lean:62`): la conclusione è testualmente il secondo congiunto di `thmE`, ma le ipotesi sono `(hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8) {δ : ℝ} (hδ : 0 < δ)`, cioè B > 0 e niente Vinogradov–Vaughan né Jackson.
- (3) `thmE3` (`ThmE3.lean:202`), con ipotesi `(hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ)` e conclusione testualmente uguale al terzo congiunto.

"In particular" — `ArcsAlgo.Core.thmE2_rel` (`EdgeRel.lean:108`):

```lean
theorem thmE2_rel (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → emerging q → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) →
      ∀ ts : ℝ, |ts| ≤ 4 * |nuW (WN N) q a| / S2W (WN N) q a → Fw' (WN N) q a ts = 0 → ∀ T : ℝ,
        ((T - (kS N ((a : ℝ) / q + ts / (2 * π)) 1).re) / sS N ((a : ℝ) / q + ts / (2 * π))) ^ 2 ≤ Real.log N →
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ ≤
          12 * (N : ℝ) ^ (-1 + 2 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * Hhat N ts ((a : ℝ) / q + ts / (2 * π)) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))
```

Definizioni rilevanti: `PP B N = (log N)^B` (= 𝔓, `ThmE3.lean:38`); `Rarc` = ∫ su |θ − a/q| ≤ 𝔓/(qN) (`ThmE3.lean:41`); `WN N` = {1} ∪ {p ≤ N} (`ArcCore.lean:173`); `ellq q X₀ = sup_{X ≥ X₀} A_q(X)/φ(q)` (`CorQprime.lean:294`); `ellE q = max 0 (ellq q (1/(2q)))` (`ThmE3.lean:45`), uguale a `ellq q (1/(2q))` per `ellE_eq` (`EdgeLobes.lean:77`).

**Lettura.** Siano B > 40, 0 < ε < 1/8, δ > 0. Esiste N₀ tale che per ogni N ≥ N₀ valgono le tre parti.
- (1) Per ogni θ ∈ 𝔪: |F_N(e(θ))| ≤ 2^n e^{(−log 2 + δ)π(N)}. Per ogni B > 0 vale inoltre la forma esplicita con C((log N)^{5−B/8} + M^{−1/2}), M = (log N)^{B/4}.
- (2) Per 3 ≤ q ≤ 𝔓, q ∈ 𝔈, (a, q) = 1, ogni punto t* con |t*| ≤ 4|ν|/S₂ e F′(t*) = 0 (il picco di Lemma W), θ* = a/q + t*/(2π), e ogni T:
  - se 𝒱 = ∅: |R − e(−Ta/q)Ĥ(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + 5e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)};
  - se 𝒱 = {w₀}: |R − e(−Ta/q)w₀Ĥ′(T)| ≤ |G(θ*)|(w₀(|t*| + 1/s̃*)N^{−3/2+2ε}/s̃* + w₀e^{−N^{2ε}/(16384 log N)} + 4e^{−N^{2ε}/(512 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}, dove s̃* = `sV` è la deviazione standard costruita con i cumulanti esatti di G̃ in t*.
- (3) Per q ∉ 𝔈: |R_{a/q}(T)| ≤ 2^n e^{(−log 2 + ℓ*_q + δ)π(N)}, con ℓ*_q = sup_{X≥1/(2q)} A_q(X)/φ(q) (≥ 0).
- Forma relativa (`thmE2_rel`): se 𝒱 = ∅ e z² ≤ log N, con z = (T − Re κ₁*)/s*: |R − 𝒜*| ≤ 12N^{−1+2ε}|𝒜*| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.

### Differenza

- **o(1) negli esponenti**: diventa "+δ per ogni δ > 0, per N ≥ N₀(B, ε, δ)", uniformemente in q, a, T. È equivalente, ma va detto esplicitamente che è uniforme.
- **Costanti esplicite**: gli O(·) di (2) hanno costante 1 (sul termine principale d'errore) e 2 (sul termine dei lobi). Lean tiene **a parte** i termini esponenzialmente piccoli |G(θ*)|e^{−cN^{2ε}/log N} (coda gaussiana e spalle), che il paper assorbe nell'O(Ω|G(θ*)|N^{−3/2+2ε}/s*).
- **Ruolo di B**: B > 40 serve solo per (1). (2), (3) e la forma relativa valgono per ogni B > 0, e (1) in forma esplicita vale per ogni B > 0. Le ipotesi Vinogradov–Vaughan e Jackson servono solo per (1); Siegel–Walfisz serve per tutte e tre.
- **Caso 𝒱(a/q) = {w}**: **allineato al rev1 attuale.** Il paper usa ora s̃* (radice del secondo cumulante di G̃ in t*) in Ĥ, in Ω = w(|t*| + 1/s̃*) e nel termine d'errore, come Lean (`sV`).
- **Picco**: in Lean t* è caratterizzato come zero di F′ con |t*| ≤ 4|ν_{a/q}|/S₂. "θ* stays the peak of |G|" corrisponde a questo.
- **q ∈ 𝔈 in (2)**: è un'ipotesi dell'enunciato Lean, ma la dimostrazione non la usa (docstring di `thmE2`).
- **ℓ*_q in (2) e (3)**: **allineato al rev1 attuale.** Il paper usa ℓ*_q = sup_{X≥1/(2q)} A_q(X)/φ(q) in (2) e (3), e dice ℓ*_q = ℓ_q quando A_q ha un primo minimo locale X_q (q ∉ 𝔈). Dal 3 nov 2026 `thmE` (`ARCS.theoremE`) è enunciato con `ellq q (1/(2q))` = ℓ*_q anche in (3) (prima `ellE` = max(0, ℓ*_q)); il max(0, ·) era ridondante: `ellE_eq` (`EdgeLobes.lean`, da `ellq_nonneg` via `Aq_ge`). `ellE_eq_ellq` (`ARCS.theoremE_lobe_exponent`) dice ora ℓ*_q = ℓ_q per q ∉ 𝔈 e X_q primo minimo locale, come il paper.
- **"In particular"**: costante 12, δ al posto di o(1), condizione |z| ≤ √(log N) con z reale costruito con Re κ₁*.

**Wording suggerito.**
> Fix 0 < ε < 1/8. For every δ > 0 there is N₀ such that for N ≥ N₀, 3 ≤ q ≤ 𝔓, (a, q) = 1 and every T:
> 1. (minor arcs; here B > 40) sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + δ)π(N)); more precisely, for every B > 0, sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + C((log N)^{5−B/8} + M^{−1/2}))π(N)).
> 2. (emerging arcs; every B > 0) […] If 𝒱(a/q) = ∅,
> |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + 5e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> If 𝒱(a/q) = {w}, let s̃* be the square root of the second cumulant of G̃ at t* and Ω = w(|t*| + 1/s̃*); then
> |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ |G(θ*)|(Ω N^{−3/2+2ε}/s̃* + w e^{−N^{2ε}/(16384 log N)} + 4e^{−N^{2ε}/(512 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> In particular, if 𝒱(a/q) = ∅ and |z| ≤ √(log N), |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ 12N^{−1+2ε}|𝒜*_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> 3. (other arcs; every B > 0) For q ∉ 𝔈, |R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ*_q + δ)π(N)) (and ℓ*_q = ℓ_q when A_q has a first local minimum).

Il rev1 attuale corrisponde a questi enunciati salvo la forma (o(1) come δ, costanti esplicite, termini esponenzialmente piccoli tenuti a parte in Lean): sono differenze di esplicitezza, non punti in cui il paper dice più di Lean.

---

## 3. Remark (the formula of Proposition C)

### Paper (riga 311, rev1 attuale)

> **Remark (the formula of Proposition C).** If ν_{a/q} ≪ N^{3/2+ε/2}, as under GRH for the odd characters mod q (for fixed q), the peak lies well inside the core of a/q, and the linear tilt e^{−νσ} on the core is dominated by the Gaussian decay. The same proof, run with the expansion at a/q instead of θ*, then gives (2) with the arc term 𝒜_{a/q} of Proposition C. When 𝒱(a/q) = ∅ the error is relative, O(N^{−1/2+3ε}), uniformly for |Re z| ≤ √(log N); z is now complex, with |Im z| ≍ |ν|/s*. When 𝒱(a/q) = {w} the bound is absolute and centred at a/q: with s̃² the second cumulant of G̃ at a/q, for every T and every δ > 0,
> $$|R_{a/q}(T)-\mathcal A_{a/q}(T)|\le|G(a/q)|\Big(\frac{w\,e^{\nu^2/(2\tilde s^2)}N^{-3/2+7\varepsilon}}{\tilde s^2}+w\,e^{-N^{2\varepsilon}/(16384\log N)}+4e^{4\nu^2/S_2}e^{-N^{2\varepsilon}/(2048\log N)}\Big)+2\cdot2^ne^{(-\log2+\ell^*_q+\delta)\pi(N)}$$
> for N ≥ N₀(δ). The main term w·Ĥ′ ≈ −w·zφ(z)/s² vanishes at z = 0, so no relative bound holds near it. This is the form tested in Table 2. Unconditionally the expansion must be centred at the peak θ*, because ν_{a/q} is only known to be ≪ N²e^{−c√log N}.

### Lean

`ArcsAlgo.Core.thmC2_rel` (`RemarkPropC.lean:133`):

```lean
theorem thmC2_rel (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      (∀ w ∈ WN N, ¬ vanish q a w) → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) →
      ∀ T : ℝ, |(((T : ℂ) - kS N ((a : ℝ) / q) 1) / (sS N ((a : ℝ) / q) : ℂ)).re| ≤ √(Real.log N) →
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ ≤
          12 * (N : ℝ) ^ (-1 + 6 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))
```

`ArcsAlgo.Core.thmC2_paper` (`RemarkPropC.lean:275`): stesse ipotesi e stessi quantificatori di `thmC2_rel`, conclusione

```lean
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ ≤
          (N : ℝ) ^ (-(1 / 2) + 3 * ε) * ‖ee (-(T * ((a : ℝ) / q))) * HhatC N ((a : ℝ) / q) T‖ +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))
```

`ArcsAlgo.Core.thmC2_vanish` (`RemarkPropCV.lean:35`):

```lean
theorem thmC2_vanish (hSW : SiegelWalfisz) {B : ℝ} (hB : 0 < B) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 8)
    {Cν : ℝ} (hCν : 0 < Cν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ PP B N → a.Coprime q →
      ∀ w₀ ∈ WN N, vanish q a w₀ → |nuW (WN N) q a| ≤ Cν * (N : ℝ) ^ ((3 / 2 : ℝ) + ε / 2) → ∀ T : ℝ,
        ‖Rarc B N q a T - ee (-(T * ((a : ℝ) / q))) * (w₀ * deriv (fun T => HhatV N q a w₀ 0 T) T)‖ ≤
          ‖Gw (WN N) q a ((a : ℝ) / q)‖ *
            (w₀ * (Real.exp (nuW (WN N) q a ^ 2 / (2 * sV N q a w₀ 0 ^ 2)) *
                ((N : ℝ) ^ (-(3 / 2 : ℝ) + 7 * ε) / sV N q a w₀ 0 ^ 2)) +
              w₀ * Real.exp (-((N : ℝ) ^ (2 * ε)) / (16384 * Real.log N)) +
              4 * Real.exp (4 * nuW (WN N) q a ^ 2 / S2W (WN N) q a) *
                Real.exp (-((N : ℝ) ^ (2 * ε)) / (2048 * Real.log N))) +
            2 * (2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellq q (1 / (2 * q)) + δ) * Nat.primeCounting N))
```

**Lettura.** Siano B > 0, 0 < ε < 1/8, C_ν > 0, δ > 0. Esiste N₀ = N₀(B, ε, C_ν, δ) tale che per N ≥ N₀, 3 ≤ q ≤ 𝔓, (a, q) = 1 e |ν_{a/q}| ≤ C_νN^{3/2+ε/2} valgono i due casi seguenti.
- Se 𝒱(a/q) = ∅, allora per ogni T con |Re z| ≤ √(log N), dove z = (T − κ₁)/s e κ₁ è il primo cumulante complesso di Proposition C in a/q: |R − 𝒜_{a/q}| ≤ 12N^{−1+6ε}|𝒜_{a/q}| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}. Ne segue la stessa stima con N^{−1/2+3ε} al posto di 12N^{−1+6ε}.
- Se 𝒱(a/q) = {w₀}, allora per ogni T: |R − e(−Ta/q)w₀Ĥ′(T)| ≤ |G(a/q)|(w₀e^{ν²/(2s̃²)}N^{−3/2+7ε}/s̃² + w₀e^{−N^{2ε}/(16384 log N)} + 4e^{4ν²/S₂}e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}. Qui Ĥ è costruito in a/q (t = 0) con i cumulanti di G̃, e s̃ = `sV N q a w₀ 0`.

### Differenza

- **Antecedente**: "ν_{a/q} ≪ N^{3/2+ε/2}" diventa l'ipotesi esplicita |ν_{a/q}| ≤ C_νN^{3/2+ε/2}, con N₀ dipendente da C_ν. GRH non è un'ipotesi Lean: è solo la motivazione dell'antecedente.
- **Esponente relativo**: Lean dimostra 12N^{−1+6ε}, più forte di O(N^{−1/2+3ε}) per ε < 1/6. La forma del paper (`thmC2_paper`) vale con costante 1. Il paper può tenere N^{−1/2+3ε}, ma è corretto, e più informativo, scrivere 12N^{−1+6ε}.
- **q ∈ 𝔈**: "gives (2)" rimanda a una parte enunciata per q ∈ 𝔈, ma gli enunciati Lean del Remark **non richiedono** q ∈ 𝔈 (valgono per ogni 3 ≤ q ≤ 𝔓).
- **Caso 𝒱 = {w}**: **allineato al rev1 attuale.** Il paper dà ora la stima assoluta centrata in a/q, con |G(a/q)|, N^{−3/2+7ε}, s̃², e^{ν²/(2s̃²)} e i termini esponenzialmente piccoli espliciti: è `thmC2_vanish`.
- **"|Im z| ≍ |ν|/s*"**: è una frase descrittiva, non fa parte di un enunciato Lean di questa voce.

**Wording suggerito.**
Nessuno: il Remark del rev1 attuale corrisponde a `thmC2_rel`/`thmC2_paper` (𝒱 = ∅) e `thmC2_vanish` (𝒱 = {w}), con "ν ≪ N^{3/2+ε/2}" come |ν| ≤ C_νN^{3/2+ε/2} e N₀(B, ε, C_ν, δ).

---

## 4. Proposizione B′

### Paper (riga 722, rev1 attuale)

> **Proposition B′ (the constant of the second moment).** Fix M ≥ 2 and g > 0, and put z = (s − mμ)/(σ√m). Uniformly in |z| ≤ g and |u| ≤ M with u ≡ s (mod 2),
> $$\frac{E[Z^2\mid S_E=s]}{\lambda^2}=1+\frac{1+\mathbf1[u=0]}{\lambda}+\frac{\kappa_c}m+\frac{\gamma_M\,z}{m^{3/2}}+O_{M,g}(m^{-2}),$$
> and, conditioning only on the event S_E ≡ u (mod 2), with Z̄_u = E[Z | S_E ≡ u (mod 2)],
> $$\frac{E[Z^2\mid S_E\equiv u\ (\mathrm{mod}\ 2)]}{\bar Z_u^{\,2}}=1+\frac{1+\mathbf1[u=0]}{\bar Z_u}+\frac\kappa m+\frac{c_2(M,u)}{m^2}+O_M(m^{-3}),\qquad c_2(M,u)=c_2(M,0)-\frac{2\kappa u^2}{Ew^2},$$
> with
> $$\kappa=\frac{\operatorname{Var}(w^2)}{4(Ew^2)^2}\to\frac15,\qquad\kappa_c=\frac{\operatorname{Var}(w^2)-\operatorname{Cov}(w^2,w)^2/\operatorname{Var}(w)}{4(Ew^2)^2}\to\frac1{80},$$
> $$\gamma_M=\frac{\sigma\,(B-2\beta A)}{4(Ew^2)^2}\to-\frac{\sqrt3}{80},\quad A=\operatorname{Var}(w^2)-\frac{\operatorname{Cov}(w^2,w)^2}{\operatorname{Var}(w)},\ \beta=\frac{\operatorname{Cov}(w,w^2)}{\operatorname{Var}(w)\,Ew^2},\ B=\frac{E[R^2(w-\mu)]}{\operatorname{Var}(w)},$$
> where R = w² − Ew² − (Cov(w², w)/Var(w))(w − μ).

### Lean

`ArcsAlgo.LLT.propBprime_cond` (`SecondMoment/BPCondT.lean:33`):

```lean
theorem propBprime_cond (hBR : BR22Edge) (hM : 2 ≤ M) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ, |zB M m s| ≤ g → |(u : ℝ)| ≤ M → (2 : ℤ) ∣ u - s →
      |m2B M m s u / lamB M m s u ^ 2 - (1 + (1 + if u = 0 then 1 else 0) / lamB M m s u + kapcB M / m +
        gamB M * zB M m s / (m * √(m : ℝ)))| ≤ C / (m : ℝ) ^ 2
```

`ArcsAlgo.LLT.propBprime_uncond` (`SecondMoment/BPUT.lean:69`):

```lean
theorem propBprime_uncond (hBR : BR22Edge) (hM : 2 ≤ M) :
    ∃ C : ℝ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ u : ℤ, |(u : ℝ)| ≤ M →
      |m2U M m u / lamU M m u ^ 2 - (1 + (1 + if u = 0 then 1 else 0) / lamU M m u + kapB M / m +
        (c2B M - 2 * kapB M * (u : ℝ) ^ 2 / ew2 M) / (m : ℝ) ^ 2)| ≤ C / (m : ℝ) ^ 3
```

Definizioni e identità: `lamB`, `m2B` = E[Z(u) | S_E = s], E[Z(u)² | S_E = s] (`SecondMoment/LemmaB.lean:151`, `:155`); `lamU`, `m2U` = E[Z(u) | S_E ≡ u (mod 2)], E[Z(u)² | S_E ≡ u (mod 2)] (`SecondMoment/BPU1.lean:137`, `:133`); `kapB`, `kapcB`, `gamB` (`SecondMoment/BPConst.lean:33`, `:37`, `:46`) sono le formule del paper per κ, κ_c, γ_M; `c2B M := CCu M 0` (`BPUT.lean:61`), dove `CCu` è il coefficiente di m⁻² dell'espansione (`BPRatio.lean:163`);

```lean
theorem CCu_eq (hM : 2 ≤ M) (u : ℝ) : CCu M u = CCu M 0 - 2 * kapB M * u ^ 2 / mw M 2
```
(`SecondMoment/BPConst.lean:123`). `BR22Edge` (`SecondMoment/BREdge.lean:81`) è [BR, Theorem 22.1] a ogni ordine, come ipotesi citata.

**Lettura.** Fissati M ≥ 2 e g ≥ 0, esistono C e m₀ tali che per m ≥ m₀, |z| ≤ g, |u| ≤ M, u ≡ s (mod 2): |E[Z²|S_E = s]/λ² − (1 + (1 + 1[u=0])/λ + κ_c/m + γ_M z/m^{3/2})| ≤ C/m², con λ = E[Z|S_E = s]. Fissato M ≥ 2, esistono C e m₀ tali che per m ≥ m₀ e |u| ≤ M: |E[Z²|S_E ≡ u]/E[Z|S_E ≡ u]² − (1 + (1 + 1[u=0])/E[Z|S_E ≡ u] + κ/m + (c₂(M,0) − 2κu²/Ew²)/m²)| ≤ C/m³.

### Differenza

- **c₂(M, u)**: già corretto nel rev1, in accordo con Lean.
- **g**: paper g > 0, Lean g ≥ 0 (più generale).
- **Parte condizionata alla parità**: **allineato al rev1 attuale.** Il paper condiziona ora solo sull'evento S_E ≡ u (mod 2), con Z̄_u = E[Z | S_E ≡ u (mod 2)], come `propBprime_uncond` (`lamU`, `m2U`).
- **Denominatore della prima formula**: **allineato al rev1 attuale.** Il paper scrive ora λ (prima 𝒵), come `lamB`; anche nel Lemma B‴ i conteggi sono λ_J(v, t).
- **Limiti per M → ∞** (κ → 1/5, κ_c → 1/80, γ_M → −√3/80): **dimostrati** il 3 nov 2026 in `SecondMoment/BPLimits.lean` (`kapB_tendsto`, `kapcB_tendsto`, `gamB_tendsto`), per w uniforme su {1, …, M}; per simmetria Cov(w², w)/Var(w) = M + 1, R = (w − μ)² − σ² e B = 0 (`BB_eq_zero`).
- **c₂(M, 0)**: in Lean è definito come coefficiente della serie (`CCu M 0`). Il paper non ne dà una formula chiusa; i valori numerici 0.246, 0.274, 0.281 non sono formalizzati.
- **Ipotesi**: [BR, Theorem 22.1] a ogni ordine (`BR22Edge`), come ipotesi.

**Wording suggerito.**
Nessuno: la Proposizione B′ del rev1 attuale corrisponde a `propBprime_cond` e `propBprime_uncond` (g ≥ 0 in Lean, più generale; [BR, Theorem 22.1] come ipotesi `BR22Edge`); i limiti per M → ∞ sono `kapB_tendsto`, `kapcB_tendsto`, `gamB_tendsto`.

---

## 5. Teorema 7.2 (structural collapse)

### Paper (riga 981, rev1 attuale; Definizione 7.1 alla riga 977)

> **Definition 7.1.** T_struct = Eval ∘ Par, where:
> - Par is union-find with parity on C_par [Tarjan]. Every variable is written x = r ⊕ b_x with r the root of its class; there is one domain per class (a shared cell). The shared form is 𝒮 = { W | ∀x ∼ y, W(x) = W(y) ⊕ (b_x ⊕ b_y) }.
> - Eval is one pass over Def in a topological order of the parity classes (the graph of the definitions with the classes of Par contracted, assumed acyclic): W(x) ← W(x) ∩ f_x(∏_{u∈pred(x)} W(u)) (forward image). A topological order of the variables alone is not enough (Remark 7.2′).
>
> **Theorem 7.2 (structural collapse).**
> - (a) T_struct ∘ T_struct = T_struct, and T_struct(W) ∈ 𝒮.
> - (b) For W ∈ 𝒮 closed under Eval, T_struct(W) = W.
> - (c) Injection: if W ∈ 𝒮 and one variable is fixed, its parity class is updated in O(1). If every input in I is fixed and no parity class contains two inputs, one pass of Eval leaves every domain with at most one value, in time O(Σ_x cost(f_x)). If moreover the network has a solution α with α(r) in the initial cell of every class, no domain becomes empty and every domain is exactly {α(x)}. Without such a solution a cell can become empty even when no class contains two inputs: two definitions may write one class inconsistently (x := u, y := ¬u with x = y; Lean: `Eval_blocks_counterexample`). Two inputs in one class may also be fixed inconsistently. In both cases the conflict appears as an empty cell, in O(1).
> - (d) For W ∈ 𝒮 closed under Eval, υ(c, W) = 0 for every c ∈ C_par and every definition read forwards.

### Lean

Namespace `ArcsAlgo.Structural`, file `Structural.lean`; `V` è finito con uguaglianza decidibile, i valori sono `Bool`. Strutture: `Classes` (`:36`, campi `root`, `bit`, `root_root`, `bit_root`), `Def` (`:43`, campi `x`, `pred`, `f`, `local_f`), `dom` (`:55`), `Eval` (`:66`), `Par` (`:70`), `Tstruct` (`:74`), `Shared` (`:78`).

```lean
def RankedDefs (defs : List (Def V)) (rank : V → ℕ) : Prop :=
  (∀ d ∈ defs, ∀ u ∈ d.pred, rank (K.root u) < rank (K.root d.x)) ∧
  defs.Pairwise fun d e => rank (K.root d.x) ≤ rank (K.root e.x)
```
(`:153`)

(a) `Tstruct_idem` (`:244`):
```lean
theorem Tstruct_idem (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (W : V → Finset Bool) :
    Tstruct K defs (Tstruct K defs W) = Tstruct K defs W ∧ Shared K (Tstruct K defs W)
```
(b) `ClosedEval` (`:255`) e `Tstruct_of_closed` (`:259`):
```lean
def ClosedEval (defs : List (Def V)) (W : V → Finset Bool) : Prop :=
  ∀ d ∈ defs, W d.x ⊆ (Fintype.piFinset fun u => if u ∈ d.pred then W u else univ).image d.f
```
```lean
theorem Tstruct_of_closed (defs : List (Def V)) {W : V → Finset Bool} (hW : Shared K W)
    (hc : ClosedEval defs W) : Tstruct K defs W = W
```
(c) `inject_dom` (`:294`) e `Eval_fixes` (`:322`):
```lean
theorem inject_dom (C : Cells V) (x : V) (a : Bool) :
    (∀ r ≠ K.root x, inject K C x a r = C r) ∧
      ∀ y, K.root y = K.root x → dom K (inject K C x a) y ⊆ {xor (K.bit y) (xor (K.bit x) a)}
```
```lean
theorem Eval_fixes (rank : V → ℕ) (defs : List (Def V)) (hR : RankedDefs K defs rank)
    (C : Cells V)
    (hC : ∀ x, (C (K.root x)).card ≤ 1 ∨ ∃ d ∈ defs, K.root d.x = K.root x) :
    ∀ x, (dom K (Eval K defs C) x).card ≤ 1
```
(d) `parity_supported` (`:356`) e `def_supported` (`:406`):
```lean
theorem parity_supported {W : V → Finset Bool} (hW : Shared K W) (x y : V) (b : Bool)
    (hxy : K.root x = K.root y) (hb : b = (K.bit x ^^ K.bit y)) :
    Supported (parityConstraint x y b) W
```
```lean
theorem def_supported (d : Def V) (hx : d.x ∉ d.pred) {W : V → Finset Bool}
    (hc : W d.x ⊆ (Fintype.piFinset fun u => if u ∈ d.pred then W u else univ).image d.f) :
    proj (defConstraint d) W d.x = W d.x
```
Remark 7.2′: `Tstruct_not_idem_counterexample` (`:463`).

**Lettura.** Le variabili sono booleane. Par è dato dal suo risultato: una radice e un bit di parità per ogni variabile, con una cella per classe. Eval percorre la lista delle definizioni nel suo ordine; `RankedDefs` chiede un rango sulle classi tale che ogni genitore stia in una classe di rango strettamente minore e la lista sia ordinata per rango della classe scritta.
- (a) Sotto `RankedDefs`, T_struct(T_struct(W)) = T_struct(W) e T_struct(W) ∈ 𝒮, per ogni W.
- (b) Per W ∈ 𝒮 chiuso sotto Eval, T_struct(W) = W.
- (c) L'iniezione x = a modifica solo la cella della classe di x, e ogni y della classe ha dominio ⊆ {a ⊕ b_x ⊕ b_y}. Se ogni classe ha cella con al più un valore oppure è scritta da una definizione, dopo un passo di Eval (sotto `RankedDefs`) ogni dominio ha **al più** un valore.
- (d) In 𝒮 ogni vincolo di parità x = y ⊕ (b_x ⊕ b_y) tra membri di una stessa classe ha difetto nullo. Se W(x) è contenuto nell'immagine dei genitori e x ∉ pred(x), ogni valore di x ha supporto nella definizione letta in avanti.

### Differenza

- **Ordine di Eval**: "topological order of the parity classes" è già nel rev1. In Lean è reso preciso da `RankedDefs`: rango sulle classi, genitori in classi di rango strettamente minore, lista ordinata per rango.
- **Dominio dei valori**: Lean tratta solo variabili booleane (Val = Bool), il paper un Val generico (§7.1: W : V → 𝒫(Val)); il Teorema 7.3 dice "for Boolean Val". È una differenza documentata, non un punto da allineare: §8, dove i domini sono insiemi di interi (le somme parziali s_i), è formalizzato direttamente in `Chain.lean` (`mem_reach`, `back_eq`, `back_greatest`, `greedy_spec`, …), che non importa `Structural.lean` né `Propagation.lean` e quindi non dipende dalla versione generale del Teorema 7.2.
- **Par**: Lean non formalizza l'algoritmo union-find, ma il suo risultato (struttura `Classes`). Le affermazioni di complessità O(1) e O(Σ_x cost(f_x)) in (c) **non sono formalizzate**.
- **(c)**: **allineato al rev1 attuale** nella forma corretta: il paper dice ora "at most one value", aggiunge la soluzione α nelle celle iniziali ("every domain is exactly {α(x)}") e cita il controesempio `Eval_blocks_counterexample`. Restano, come note:
  - l'ipotesi del paper (ogni input fissato, nessuna classe con due input; I = variabili non definite e non fuse con un input) implica quella Lean, "ogni classe ha cella con ≤ 1 valore, oppure è scritta da una definizione";
  - la conclusione di `Eval_fixes` è "ogni dominio ha **al più** un valore";
  - il controesempio `Eval_blocks_counterexample` (due definizioni che scrivono una stessa classe in modo incoerente) è ora citato dal paper; senza la soluzione α una cella può svuotarsi anche se nessuna classe contiene due input;
  - la forma con α è dimostrata (`Eval_nonempty`: nessun dominio vuoto; `Eval_fixes_exactly`: ogni dominio è esattamente {α(x)});
  - "the conflict appears as an empty cell" è solo nel docstring;
  - l'iniezione è formalizzata (`inject_dom`) senza l'ipotesi W ∈ 𝒮, perché lo stato è per costruzione in forma condivisa.
- **(d)**: per i vincoli di parità basta W ∈ 𝒮, e il risultato riguarda i vincoli x = y ⊕ (b_x ⊕ b_y) tra variabili della stessa classe, cioè quelli assorbiti da Par. Per le definizioni basta la chiusura sotto Eval della singola definizione, più x ∉ pred(x); 𝒮 non serve.

**Wording suggerito.**
Nessuno. Lean ha Val = Bool, il paper Val generico: differenza documentata sopra (§8 è formalizzato direttamente in `Chain.lean`). Il resto del Teorema 7.2 del rev1 attuale corrisponde a `Tstruct_idem`, `Tstruct_of_closed`, `inject_dom`, `Eval_fixes`, `Eval_nonempty`, `Eval_fixes_exactly`, `parity_supported`, `def_supported`; la complessità non è formalizzata.

---

## 6. Teorema 7.4

### Paper (riga 1001, rev1 attuale)

> **Theorem 7.4.** Let V and Val be finite, and assume every T_c, c ∈ C_comp ∪ Def (definitions also read backwards), is the generalized arc consistency filter.
> - (i) T_comp is decreasing and monotone: T_comp(W) ⊑ W and W ⊑ W′ → T_comp(W) ⊑ T_comp(W′).
> - (ii) T_comp(W) = W ⟺ ∀c υ(c, W) = 0.
> - (iii) Let μ(W) = Σ_v(|W(v)| − 1), and let T_fail be T_comp with the state replaced by the failure state as soon as a domain becomes empty. If every domain of W is non-empty, then T_fail^m(W) = T_fail^{μ(W)+1}(W) for every m ≥ μ(W) + 1. μ(W) rounds do not suffice in general: one variable with W = {0} and the assertion x = 1 has μ(W) = 0 but T_comp(W) ≠ W (Lean: `Tcomp_bound_counterexample`).
> - (iv) The limit W* is the largest W′ ⊑ W with υ(c, W′) = 0 for every c, and it does not depend on the order of the filters (chaotic iteration [Apt]).

### Lean

Namespace `ArcsAlgo.Propagation`, file `Propagation.lean`; `V`, `Val` finiti e decidibili; `Constraint` (`:36`, campi `vars`, `sat`), `proj` (`:52`), `filter` (`:57`), `defect` (`:61`), `Tcomp` (`:65`, un giro dei filtri nell'ordine della lista).

```lean
theorem Tcomp_le (cs : List (Constraint V Val)) (W : Dom V Val) : Tcomp cs W ≤ W
```
```lean
theorem Tcomp_mono (cs : List (Constraint V Val)) {W W' : Dom V Val} (h : W ≤ W') :
    Tcomp cs W ≤ Tcomp cs W'
```
```lean
theorem Tcomp_eq_self_iff (cs : List (Constraint V Val)) (W : Dom V Val) :
    Tcomp cs W = W ↔ ∀ c ∈ cs, defect c W = 0
```
(`:126`, `:132`, `:139`)

(iii) `mu` (`:192`), `Tfail` (`:201`), `Tfail_stable` (`:228`), `Tcomp_bound_counterexample` (`:265`):
```lean
def mu (W : Dom V Val) : ℕ := ∑ v, ((W v).card - 1)
def Tfail (cs : List (Constraint V Val)) (W : Dom V Val) : Dom V Val :=
  if ∃ v, Tcomp cs W v = ∅ then failure else Tcomp cs W
```
```lean
theorem Tfail_stable (cs : List (Constraint V Val)) (W : Dom V Val) (hW : ∀ v, (W v).Nonempty) :
    ∀ m ≥ mu W + 1, (Tfail cs)^[m] W = (Tfail cs)^[mu W + 1] W
```
```lean
theorem Tcomp_bound_counterexample :
    let c : Constraint Unit Bool := ⟨{()}, fun α => α ()⟩
    let W : Dom Unit Bool := fun _ => {false}
    mu W = 0 ∧ Tcomp [c] W ≠ W
```

(iv) `limit` (`:278`), `limit_greatest` (`:301`), `limit_supported` (`:313`), `limit_perm` (`:319`), `schedule_eq_limit` (`:343`):
```lean
def limit (cs : List (Constraint V Val)) (W : Dom V Val) : Dom V Val := (Tcomp cs)^[size W] W
```
```lean
theorem limit_greatest (cs : List (Constraint V Val)) (W W' : Dom V Val) (hle : W' ≤ W)
    (hW' : ∀ c ∈ cs, defect c W' = 0) : W' ≤ limit cs W
```
```lean
theorem limit_supported (cs : List (Constraint V Val)) (W : Dom V Val) :
    ∀ c ∈ cs, defect c (limit cs W) = 0
```
```lean
theorem limit_perm {cs cs' : List (Constraint V Val)} (h : cs.Perm cs') (W : Dom V Val) :
    limit cs W = limit cs' W
```
```lean
theorem schedule_eq_limit (cs : List (Constraint V Val)) (W : Dom V Val)
    (sched : List (Constraint V Val)) (hs : ∀ c ∈ sched, c ∈ cs)
    (hfix : ∀ c ∈ cs, defect c (sched.foldl (fun W c => filter c W) W) = 0) :
    sched.foldl (fun W c => filter c W) W = limit cs W
```

**Lettura.** Per una lista finita qualsiasi di vincoli, con filtri GAC (che in Lean sono la definizione di `filter`):
- (i) T_comp(W) ⊑ W ed è monotono.
- (ii) T_comp(W) = W ⟺ υ(c, W) = 0 per ogni c della lista.
- (iii) Sia T_fail l'operatore che manda in "fallimento" (tutti i domini vuoti) appena un dominio si svuota. Se tutti i domini di W sono non vuoti, T_fail^m(W) = T_fail^{μ(W)+1}(W) per ogni m ≥ μ(W) + 1; inoltre esiste un esempio con μ(W) = 0 e T_comp(W) ≠ W.
- (iv) Il limite W* := T_comp^{size W}(W), con size W = Σ_v|W(v)|, ha difetto nullo per ogni c ed è il più grande W′ ⊑ W con difetto nullo. Non cambia permutando la lista, e ogni schedule di filtri di cs che termini in uno stato a difetto nullo arriva a W*.

### Differenza

- **Finitezza**: **allineato al rev1 attuale.** Il paper dice ora "Let V and Val be finite", come Lean.
- **Ipotesi "C_comp ∪ Def (definitions also read backwards)"**: in Lean non c'è distinzione tra famiglie; il teorema vale per una qualsiasi lista finita di vincoli.
- **(iii)**: **allineato al rev1 attuale.** Il paper usa ora T_fail, chiede domini non vuoti e dà il controesempio con μ(W) = 0 e T_comp(W) ≠ W (`Tcomp_bound_counterexample`), come `Tfail_stable`.
- **(iv)**: il limite è definito come iterato `size W` volte di T_comp (senza fallimento). "Does not depend on the order of the filters" è formalizzato in due forme: invarianza per permutazione della lista (`limit_perm`), e uguaglianza col limite per ogni schedule di filtri di cs che raggiunga uno stato a difetto nullo (`schedule_eq_limit`). Lean non contiene un riferimento formale a [Apt].
- La correzione μ(W) + 1 è già nel rev1.

**Wording suggerito.**
Nessuno: il Teorema 7.4 del rev1 attuale corrisponde a `Tcomp_le`, `Tcomp_mono`, `Tcomp_eq_self_iff`, `Tfail_stable`, `Tcomp_bound_counterexample` e, per (iv), a `limit_perm` e `schedule_eq_limit` ([Apt] senza riferimento formale).

---

## 7. Lemma J

### Paper (riga 877, rev1 attuale)

> **Lemma J (averaging over the residues).** For every finitely supported law of the weights and of P,
> $$\Pr(\text{round succeeds})\ \ge\ \frac{(\mathbb E N)^2}{\mathbb E[P\cdot Y_P]} .$$

(Setting, riga 864: N = #{(y,z) ∈ 𝒫 : S_y + S_z = a}, Z_r = #{… , S_y ≡ r (mod P)}, Y_P = Σ_r Z_r²; un round estrae r uniforme in ℤ/P e riesce se e solo se Z_r > 0.)

### Lean

`ArcsAlgo.RandomWeights.roundSuccess_ge` (`RandomWeights.lean:188`):

```lean
theorem roundSuccess_ge {Ω : Type*} (s : Finset Ω) (p : Ω → ℝ) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (P : Ω → ℕ) (hP : ∀ ω ∈ s, 0 < P ω) (Z : Ω → ℕ → ℕ) :
    (∑ ω ∈ s, p ω * ∑ r ∈ range (P ω), (Z ω r : ℝ)) ^ 2 /
        (∑ ω ∈ s, p ω * P ω * ∑ r ∈ range (P ω), (Z ω r : ℝ) ^ 2) ≤
      ∑ ω ∈ s, p ω * ((range (P ω)).filter fun r => 0 < Z ω r).card / P ω
```

**Lettura.** Siano Ω un insieme finito di esiti (pesi e P), p ≥ 0 le masse, P(ω) ≥ 1 e Z_r(ω) ∈ ℕ arbitrari per r ∈ {0, …, P(ω) − 1}. Con N = Σ_r Z_r e Y_P = Σ_r Z_r² vale (Σ_ω p N)² / (Σ_ω p P Y_P) ≤ Σ_ω p·|{r : Z_r > 0}|/P, cioè (E N)²/E[P·Y_P] ≤ E[|R_P|/P] = Pr(round succeeds).

### Differenza

- "Finitely supported law" è già nel rev1, in accordo con Lean.
- Lean è **più generale**: le masse p non devono sommare a 1, e Z_r è un qualsiasi conteggio a valori naturali (nessuna ipotesi sullo schema 𝒫 né sui pesi), coerentemente con "The lemma uses nothing about the scheme or the weights".
- Convenzione: in Lean x/0 = 0, quindi per E[P·Y_P] = 0 l'enunciato è banale. Il paper non tratta il caso.
- Nessuna divergenza sostanziale.

**Wording suggerito.**
> **Lemma J.** For every finitely supported law of (weights, P), with r uniform in ℤ/P given the weights and P, Pr(round succeeds) = E[|{r : Z_r > 0}|/P] ≥ (E N)²/E[P·Y_P] (the right side read as 0 when E[P·Y_P] = 0).

---

## 8. Lemma V

### Paper (riga 907, versione del 3 nov 2026)

> **Lemma V (equal half-sums).** For 𝒫₁, let ψ = 2^{m/2}/M. Uniformly in M ≥ 2 and in the window, for m ≥ m₀(g),
> $$\frac{D_{\rm eq}}{\lambda}\le 0.72\,e^{g^2/2}\,m\,(3\psi+\psi^2)\,\big(1+O(m^{-1/5})\big),\qquad \lambda=E[Z(u)\mid S_E=s].$$

(D_eq, riga 893: D_eq = E #{(τ, τ′) ∈ 𝒫², τ ≠ τ′, both hitting a, S_y = S_{y′}}; window: |s − mμ| ≤ gσ√m, |u| ≤ M, u ≡ s (mod 2), a = (s + u)/2; |A| = h = ⌊m/2⌋.)

### Lean

`ArcsAlgo.LLT.lemmaV` (`Uniform/LemV2.lean:170`):

```lean
theorem lemmaV {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      DeqA M m A a s / lamB M m s u ≤
        0.72 * exp (g ^ 2 / 2) * m * (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2) * (1 + ε)
```

Definizioni (`Uniform/LemV2.lean:105`, `Uniform/LemV1.lean:38`):
```lean
noncomputable def DeqA (M m : ℕ) (A : Finset (Fin m)) (a s : ℤ) : ℝ :=
  (∑ x : Finset (Fin m), ∑ y ∈ (univ : Finset (Finset (Fin m))).erase x, pairPA M m A x y a s) / lawS M m s
noncomputable def pairPA (M m : ℕ) (A x y : Finset (Fin m)) (a s : ℤ) : ℝ :=
  prW M m (fun w => SJ x w = a ∧ SJ y w = a ∧ SJ (x ∩ A) w = SJ (y ∩ A) w ∧ Sw w = s)
```
Bound intermedio `sum_pairPA` (`Uniform/LemV2.lean:110`): Σ_{x≠x′} Pr ≤ 2^m(2^{m−|A|} + 2^{|A|} + 1)M⁻³ + 4^mM⁻⁴.

**Lettura.** Per ogni g ≥ 0 ed ε > 0 esiste m₀ tale che per ogni M ≥ 2, m ≥ m₀, |A| = ⌊m/2⌋, 2a = s + u, |s − mμ| ≤ gσ√m e |u| ≤ M: D_eq/λ ≤ 0.72 e^{g²/2} m(3ψ + ψ²)(1 + ε), con ψ = 2^{m/2}/M, λ = E[Z(u) | S_E = s] e D_eq = Σ_{x≠x′} Pr(S_x = S_{x′} = a, S_{x∩A} = S_{x′∩A}, S_E = s)/Pr(S_E = s).

### Differenza

- e^{g²/2} (al posto di e^{λ²/2}) è già nel rev1, in accordo con Lean.
- **Allineato al rev1 attuale (enunciato e prova).** Il paper dice ora (1 + O(m^{−1/5})) con m ≥ m₀(g) e λ = E[Z(u) | S_E = s], e la prova usa λ = λ_m(1 + O(m^{−1/5})) (Lemma B(1) con il tasso, `lemmaB1_rate`): è l'enunciato di `lemmaV_rate` (sotto), con O(m^{−1/5}) reso come C(g) m^{−1/5}. La forma con ε (`lemmaV`: (1 + ε) per ogni ε > 0, m ≥ m₀(g, ε)) resta nella libreria ed è implicata da quella con il tasso.
- Dal 3 nov 2026 anche con il tasso: `lemmaV_rate` (`Uniform/RppRate.lean`) dà D_eq/λ ≤ 0.72e^{g²/2}m(3ψ + ψ²)(1 + C(g) m^{−1/5}) per m ≥ m₀(g), uniformemente in M ≥ 2 e nella finestra. La dimostrazione è quella di `lemmaV`, resa generale in `lemmaV_core` (gli errori relativi su λ e su Pr(S_E = s) come ipotesi), con Lemma B(1) con il tasso e del2 = O(1/m) ≤ O(m^{−1/5}). Serve al Teorema R″ con il tasso (voce 9); non è confrontato da solo.
- g ≥ 0 invece di g > 0.
- Il denominatore è λ = E[Z | S_E = s] (`lamB`), ora anche nel paper (prima 𝒵).
- La parità u ≡ s (mod 2) è implicita nell'ipotesi 2a = s + u.

**Wording suggerito.**
Nessuno: l'enunciato del 3 nov 2026 corrisponde a `lemmaV_rate` (O(m^{−1/5}) letto come C(g) m^{−1/5}, uniformemente in M ≥ 2 e nella finestra).

---

## 9. Teorema R″ (filtered endgame)

### Paper (riga 930, versione del 3 nov 2026)

> **Theorem R″ (filtered endgame).** Take the setting of Theorem R′ with R disjoint blocks in place of r, so that |T − S/2| ≤ S_G/2 − RmM, and fix g ≥ 0 with 2e^{−g²/6} < 1 (say g = 3). In round j replace the meet-in-the-middle by the filtered endgame of §5.6 on E_j. The prime P_j is uniform among the primes of [P₀, 2P₀), and r_j is uniform in ℤ/P_j, both drawn independently of everything else. Assume P₀ ≥ 100.
>
> Then, given the weights of G and the block sums, the rounds fail independently. A round whose block sum lies in the window fails with probability at most 1 − p, where
> $$p=\Big[\frac{2P_0}{\lambda_m}\big(1+0.72\,e^{g^2/2}m(3\psi+\psi^2)\big)+6\ln(mM)\Big(1+\frac2{\lambda_m}+O(m^{-1/5})\Big)\Big]^{-1}\big(1-O(m^{-1/5})\big).$$
> The expected cost of a round is O(m·2^{m/4} + m·2^{m/2}/P₀).
>
> A round whose block sum leaves the window counts as failed; this happens with probability at most 2e^{−g²/6}, independently across blocks.
>
> Now choose P₀ = ⌊λ_m/2⌋ and m the least positive integer with 2^m ≥ (σ√m)^{4/3} (by minimality also 2^m ≤ 2(σ√m)^{4/3}), so m = (4/3)b + (2/3)log₂ b + O(1). Then:
> - p ≥ (1 − o(1))/(6 ln(mM)), and 2^{m/4} ≍ 2^{m/2}/P₀ ≍ (σ√m)^{1/3};
> - with R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p)⌉ rounds, the probability that |T − S/2| ≤ S_G/2 − RmM and the algorithm fails is at most δ, provided n ≥ |G| + Rm;
> - it runs in time O(log(1/δ)·log(nM)·(n log n + M^{1/3}·poly(b))). For log n = o(b) and log(1/δ) = 2^{o(b)} this is 2^{b/3+o(b)}.

### Lean

Un round — `ArcsAlgo.LLT.pRpp` (`Uniform/RppRound.lean:289`) e `ArcsAlgo.LLT.succB_unif` (`Uniform/RppRound.lean:302`):

```lean
noncomputable def pRpp (g : ℝ) (M m P₀ : ℕ) : ℝ :=
  1 / (2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) + 6 * log (m * M) * (1 + 2 / lamM M m))
```
```lean
theorem succB_unif (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      (2 : ℤ) ∣ u - s → pRpp g M m P₀ / (1 + ε) ≤ succB M m P₀ A s a
```
(Base: `succB_ge` (`:140`), Pr(success | S_E = s) ≥ λ²/(2P₀(λ + D_eq) + 6 ln(mM)·E[Z²]).)

R round — `ArcsAlgo.LLT.thmRpp_gen` (`Uniform/RppRounds.lean:217`):

```lean
theorem thmRpp_gen (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M h m R P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ → ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤
        (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * (pRpp g M m P₀ / (1 + ε))) ^ R
```
con (`ThmRp.lean:62`)
```lean
def condRp {h M r : ℕ} (m : ℕ) (wG : Fin h → Fin M) (b : Fin r → ℤ) (T : ℤ) : Prop :=
  |2 * T - (((wsOf wG).sum : ℤ) + ∑ k, b k)| ≤ ((wsOf wG).sum : ℤ) - 2 * r * m * M
```

Parametri — `Hm` (`Uniform/RppAsymp.lean:31`), `exists_Hm` (`:50`), `params_Rpp` (`:192`), `thmRpp` (`:292`):

```lean
def Hm (M m : ℕ) : Prop :=
  sig2 M ^ 2 * (m : ℝ) ^ 2 ≤ (8 : ℝ) ^ m ∧ (8 : ℝ) ^ m ≤ 8 * sig2 M ^ 2 * (m : ℝ) ^ 2
```
```lean
theorem exists_Hm {M : ℕ} (hM : 4 ≤ M) : ∃ m : ℕ, 1 ≤ m ∧ Hm M m
```
```lean
theorem params_Rpp (g : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (m₀ : ℕ) :
    ∃ M₀ : ℕ, ∀ M m : ℕ, M₀ ≤ M → 1 ≤ m → Hm M m →
      m₀ ≤ m ∧ 100 ≤ ⌊lamM M m / 2⌋₊ ∧
        (1 - ε) / (6 * log (m * M)) ≤ pRpp g M m ⌊lamM M m / 2⌋₊
```
```lean
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
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤ δ
```

Con il tasso (dal 3 nov 2026) — `Uniform/RppRate.lean`: `lemmaV_rate` (`:194`), `pRate` (`:236`), `succB_rate` (`:325`), `thmRpp_rate` (`:386`, confrontato come `ARCS.theoremR''_rate`):

```lean
noncomputable def pRate (g C : ℝ) (M m P₀ : ℕ) : ℝ :=
  (2 * P₀ / lamM M m * (1 + 0.72 * exp (g ^ 2 / 2) * m *
      (3 * (√((2 : ℝ) ^ m) / M) + (√((2 : ℝ) ^ m) / M) ^ 2)) +
    6 * log (m * M) * (1 + 2 / lamM M m + C * (m : ℝ) ^ (-(1 / 5 : ℝ))))⁻¹ *
    (1 - C * (m : ℝ) ^ (-(1 / 5 : ℝ)))
```
```lean
theorem succB_rate (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M m P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ →
      ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ s u a : ℤ, 2 * a = s + u → |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M →
      (2 : ℤ) ∣ u - s → pRate g C M m P₀ ≤ succB M m P₀ A s a
```
```lean
theorem thmRpp_rate (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ M h m R P₀ : ℕ, 2 ≤ M → m₀ ≤ m → 100 ≤ P₀ →
      ∀ A : Finset (Fin m), A.card = m / 2 →
      ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
      (∀ j b, j ∉ K j b) →
      (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
          (if condRp m wG (bsum wB) (T wG (bsum wB)) then
            ∏ j, (1 - sPr P₀ A (wB j) (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
        ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤
        (1 - (1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m P₀) ^ R
```

Parte asintotica con il tasso (dal 3 nov 2026) — `ArcsAlgo.LLT.thmRpp_asymp` (`Uniform/RppRate.lean`, confrontato come **`ARCS.theoremR''`** al posto della forma con ε `thmRpp`, che resta nella libreria), con `Hm_of_isLeast`, `pRate_ge`, `rate_le`:

```lean
theorem thmRpp_asymp (hRS : RosserSchoenfeld) {g : ℝ} (hg : 0 ≤ g) (hge : 2 * exp (-(g ^ 2 / 6)) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M m : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        (1 - ε) / (6 * log (m * M)) ≤ pRate g C M m ⌊lamM M m / 2⌋₊) ∧
      ∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M h m R : ℕ, M₀ ≤ M →
        IsLeast {k : ℕ | 1 ≤ k ∧ sig2 M ^ 2 * (k : ℝ) ^ 2 ≤ (8 : ℝ) ^ k} m →
        R = ⌈log (1 / δ) / ((1 - 2 * exp (-(g ^ 2 / 6))) * pRate g C M m ⌊lamM M m / 2⌋₊)⌉₊ →
        ∀ A : Finset (Fin m), A.card = m / 2 →
        ∀ (T : (Fin h → Fin M) → (Fin R → ℤ) → ℤ) (K : Fin R → (Fin R → ℤ) → Finset (Fin R)),
        (∀ j b, j ∉ K j b) →
        (∑ wG : Fin h → Fin M, ∑ wB : Fin R → Fin m → Fin M,
            (if condRp m wG (bsum wB) (T wG (bsum wB)) then
              ∏ j, (1 - sPr ⌊lamM M m / 2⌋₊ A (wB j)
                (aRp wG (T wG (bsum wB)) (bsum wB) (K j (bsum wB)) j)) else 0)) /
          ((M : ℝ) ^ h * ((M : ℝ) ^ m) ^ R) ≤ δ
```

**Lettura.**
- *Un round.* Sia g ≥ 0. Per ogni ε > 0 esiste m₀ tale che per M ≥ 2, m ≥ m₀, P₀ ≥ 100, |A| = ⌊m/2⌋ e s, u nella finestra: Pr(round riesce | S_E = s) ≥ p/(1 + ε), dove p⁻¹ = (2P₀/λ_m)(1 + 0.72e^{g²/2}m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m).
- *R round.* I pesi sono w_G ∈ {1..M}^h e R blocchi di m pesi, tutti uniformi e indipendenti. Il target T può dipendere da w_G e dalle somme dei blocchi; il round j include i blocchi K_j ∌ j, secondo una regola che guarda solo le somme dei blocchi. Allora Pr(|T − S/2| ≤ S_G/2 − RmM e tutti i round falliscono) ≤ (1 − (1 − 2e^{−g²/6})p/(1 + ε))^R.
- *Con il tasso.* Esiste C(g) ≥ 0 tale che per m ≥ m₀(g), M ≥ 2, P₀ ≥ 100, |A| = ⌊m/2⌋ e s, u nella finestra un round riesce con probabilità ≥ p_rate = [(2P₀/λ_m)(1 + 0.72e^{g²/2}m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C m^{−1/5})]⁻¹(1 − C m^{−1/5}) (`succB_rate`), e la probabilità che l'evento valga e tutti gli R round falliscano è ≤ (1 − (1 − 2e^{−g²/6})p_rate)^R (`thmRpp_rate`).
- *Parte asintotica (`thmRpp_asymp`, confrontato come `ARCS.theoremR''`).* Sia g ≥ 0 con 2e^{−g²/6} < 1, m il minimo intero ≥ 1 con σ⁴m² ≤ 8^m (cioè 2^m ≥ (σ√m)^{4/3}), P₀ = ⌊λ_m/2⌋. Con la stessa C: (1) per ogni ε > 0 e M ≥ M₀(g, ε), p_rate ≥ (1 − ε)/(6 ln(mM)); (2) per ogni δ > 0, M ≥ M₀ e R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p_rate)⌉, la probabilità che |T − S/2| ≤ S_G/2 − RmM e tutti i round falliscano è ≤ δ. La dimostrazione usa (1 − x)^R ≤ e^{−Rx} (`pow_le_delta`).
- *Forma con ε (nella libreria, non più confrontata).* `succB_unif`, `thmRpp_gen` con p/(1 + ε); `thmRpp` con m in `Hm`, R dato dal bound (1 − ε)/((1 + ε)6 ln(mM)) e M ≥ M₀(g, ε, δ).

### Differenza

- e^{g²/2} e λ_m (al posto di e^{λ²/2} e ρ_m) sono già nel rev1; lo è anche la caduta dell'ipotesi λ_m ≥ 2P₀ ("Assume P₀ ≥ 100").
- **p**: **allineato al rev1 attuale.** Il paper scrive ora p = […]^{−1}(1 − O(m^{−1/5})), con O(m^{−1/5}) anche dentro la parentesi, ed E N = λ_m(1 + O(m^{−1/5})) nella dimostrazione. È la forma con il tasso di Lean (`succB_rate`, `thmRpp_rate`, confrontato come `ARCS.theoremR''_rate`): esiste C(g) ≥ 0 tale che per m ≥ m₀(g), uniformemente in M ≥ 2, P₀ ≥ 100 e nella finestra, un round riesce con probabilità ≥ p_rate = [(2P₀/λ_m)(1 + 0.72e^{g²/2}m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m + C m^{−1/5})]⁻¹(1 − C m^{−1/5}), e la probabilità che l'evento valga e tutti gli R round falliscano è ≤ (1 − (1 − 2e^{−g²/6})p_rate)^R. Lean rende i due O(m^{−1/5}) con la stessa costante C. La dimostrazione usa B(1), B(2) e V con il tasso (`lemmaB1_rate`, `lemmaB2_rate`, `lemmaV_rate`), come il paper. La forma con ε (`succB_unif`, `thmRpp_gen`: p senza O(m^{−1/5}) e fattore 1/(1 + ε), m ≥ m₀(g, ε)) resta nella libreria; la parte asintotica confrontata (`ARCS.theoremR''` = `thmRpp_asymp`) è costruita sulla forma con il tasso.
- **Indipendenza**: "the rounds fail independently" non è enunciato come tale. Lean dimostra la stima risultante sulla probabilità congiunta "evento ∧ tutti i round falliscono", che è ora anche la forma del paper ("the probability that |T − S/2| ≤ S_G/2 − RmM and the algorithm fails") (fattorizzazione condizionale nella dimostrazione, `ThmRp.lean`). Lean ammette inoltre una regola generale K_j di inclusione dei blocchi e un target T dipendente da w_G e dalle somme dei blocchi.
- **Scelta di m**: **allineato al rev1 attuale.** `ARCS.theoremR''` prende il minimo intero m ≥ 1 con 2^m ≥ (σ√m)^{4/3}, scritto senza radici come σ⁴m² ≤ 8^m (`IsLeast`); `Hm_of_isLeast` dà anche 2^m ≤ 2(σ√m)^{4/3}, come il paper ("by minimality"). Il paper dice ora "the least positive integer", come Lean (m ≥ 1). L'asintotica m = (4/3)b + (2/3)log₂ b + O(1) e le relazioni 2^{m/4} ≍ 2^{m/2}/P₀ ≍ (σ√m)^{1/3} non sono formalizzate: servono solo al costo.
- **Scelta di R**: **allineato al rev1 attuale.** R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p_rate)⌉ con p_rate effettivo, come il paper. La forma con ε (`thmRpp`) chiedeva invece R·(1 − 2e^{−g²/6})(1 − ε)/((1 + ε)6 ln(mM)) ≥ ln(1/δ).
- **Ipotesi**: **allineato al rev1 attuale.** g ≥ 0 con 2e^{−g²/6} < 1 (say g = 3), come il paper. "For M large" diventa M ≥ M₀ (per M₀ si ha P₀ ≥ 100 e m ≥ m₀(g)); p_rate ≥ (1 − o(1))/(6 ln(mM)) è letto come "per ogni ε > 0, per M ≥ M₀(g, ε)". `thmRpp_rate` non chiede 2e^{−g²/6} < 1.
- **"provided n ≥ |G| + Rm"**: in Lean n = h + Rm per costruzione (i pesi sono G più i blocchi).
- **Costo e tempo** (O(m·2^{m/4} + m·2^{m/2}/P₀) per round, O(log(1/δ)·log(nM)·(n log n + M^{1/3}poly(b))), 2^{b/3+o(b)}): **non formalizzati**.
- Ipotesi: Rosser–Schoenfeld (Lemma K) soltanto.

**Wording suggerito.**
Nessuno: il Teorema R″ del rev1 attuale (p con O(m^{−1/5}) e fattore 1 − O(m^{−1/5}); m minimo, P₀ = ⌊λ_m/2⌋, R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p)⌉) corrisponde a `ARCS.theoremR''_rate` e `ARCS.theoremR''`, con O(m^{−1/5}) letto come C(g) m^{−1/5}, o(1) come ε con M ≥ M₀(g, ε) e "M large" come M ≥ M₀. Costo e tempo di esecuzione restano non formalizzati.

---

## 10. Lemma B

### Paper (riga 696, rev1)

> **Lemma B.** Let the weights of E be independent and uniform in {1, …, M}, |E| = m, let Z(u) = #{ε ∈ {±1}^E : Σε_iw_i = u}, and
> $$\lambda_m=\frac{2^{m+1}}{M\sqrt{2\pi m\,c_M}},\qquad c_M=\tfrac13+\tfrac1{2M}+\tfrac1{6M^2}.$$
> Fix g > 0 and set η = 1/10. Uniformly in M ≥ 2, in s with |s − mμ| ≤ gσ√m and in u with |u| ≤ M, u ≡ s (mod 2):
> 1. λ := E[Z(u) | S_E = s] = λ_m(1 + o(1)) (the expected number of solutions of the block; F always denotes a generating function);
> 2. E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + O(m^{−1/5}));
> 3. Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + O(m^{−1/5}).

Versione precedente (`paper_subset_arcs_propagation.md`, riga 459), per confronto:

> Fix λ > 0 and η ∈ (0, 1/6). Uniformly in M ≥ 2, in s with |s − mμ| ≤ λσ√m and in u with |u| ≤ M, u ≡ s (mod 2):
> 1. F := E[Z(u) | S_E = s] = ρ_m(1 + o(1));
> 2. E[Z(u)² | S_E = s] ≤ F + F·1[u = 0] + F²(1 + O(m^{−1/2+3η}));
> 3. P(Z(u) = 0 | S_E = s) ≤ 2/F + O(m^{−1/2+3η}).

### Lean

Uniformi in M — `ArcsAlgo.LLT.lemmaB1_unif` (`Uniform/LemmaB1.lean:190`), `lemmaB2_unif` (`Uniform/LemmaB2.lean:155`), `lemmaB3_unif` (`Uniform/LemmaB2.lean:210`):

```lean
theorem lemmaB1_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      |lamB M m s u / lamM M m - 1| ≤ ε
```
```lean
theorem lemmaB2_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      m2B M m s u ≤ lamB M m s u * (1 + if u = 0 then 1 else 0) + lamB M m s u ^ 2 * (1 + ε)
```
```lean
theorem lemmaB3_unif {g : ℝ} (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ M m : ℕ, 2 ≤ M → m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      p0B M m s u ≤ 2 / lamB M m s u + ε
```

Per M fissato — `ArcsAlgo.LLT.lemmaB_fixedM` (`SecondMoment/LemmaB.lean:408`):

```lean
theorem lemmaB_fixedM (hBR : BR22) {M : ℕ} (hM : 2 ≤ M) (g : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s u : ℤ,
      |(s : ℝ) - m * muW M| ≤ g * √(sig2 M) * √(m : ℝ) → |u| ≤ M → (2 : ℤ) ∣ u - s →
      0 < lamB M m s u ∧ |lamB M m s u / lamM M m - 1| ≤ K / √(m : ℝ) ∧
      m2B M m s u ≤ lamB M m s u ^ 2 * (1 + K / √(m : ℝ)) ∧ p0B M m s u ≤ K / √(m : ℝ)
```

Definizioni: `lamM M m = 2^{m+1}/(M√(2πm c_M))`, `cMB` = c_M (`SecondMoment/LemmaB.lean:166`, `:163`); `lamB`, `m2B`, `p0B` = E[Z | S_E = s], E[Z² | S_E = s], Pr(Z = 0 | S_E = s) (`:151`, `:155`, `:159`).

**Lettura.** Per ogni g ≥ 0 ed ε > 0 esiste m₀(g, ε) tale che per ogni M ≥ 2, m ≥ m₀, |s − mμ| ≤ gσ√m, |u| ≤ M, u ≡ s (mod 2) valgono le tre stime seguenti.
- (1) |λ/λ_m − 1| ≤ ε.
- (2) E[Z² | S_E = s] ≤ λ(1 + 1[u = 0]) + λ²(1 + ε).
- (3) Pr(Z = 0 | S_E = s) ≤ 2/λ + ε.

Per M **fissato**, con [BR, §22] come ipotesi (`BR22`), le stime valgono con il tasso K/√m, dove K = K(M, g): |λ/λ_m − 1| ≤ K/√m, E[Z²|S_E = s] ≤ λ²(1 + K/√m) e Pr(Z = 0|S_E = s) ≤ K/√m.

### Differenza

- **(1)**: il rev1 (λ_m(1 + o(1))) coincide con Lean, letto come "∀ε ∃m₀, uniformemente in M ≥ 2 e nella finestra".
- **(2), (3)**: il rev1 afferma il tasso **O(m^{−1/5})** (cioè m^{−1/2+3η} con η = 1/10); la versione precedente afferma **O(m^{−1/2+3η}) per ogni η ∈ (0, 1/6)**. Lean dimostra la forma o(1) (`lemmaB2_unif`, `lemmaB3_unif`) e, dal 2 nov 2026, **il tasso O(m^{−1/5}) uniforme in M ≥ 2** (`lemmaB2_rate`, `lemmaB3_rate`, `Uniform/LemmaB2.lean`, via `Phi2_le_rate`): esiste C(g) ≥ 0 tale che per m ≥ m₀(g) E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + C m^{−1/5}) e Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + C m^{−1/5}. Il rev1 è quindi coperto per (2) e (3); la forma "per ogni η ∈ (0, 1/6)" della versione precedente no. Dal 3 nov 2026 anche (1) ha il tasso: `lemmaB1_rate` (|λ/λ_m − 1| ≤ C(g) m^{−1/5}), e il Teorema R ha la forma con il tasso, `thmR_rate` (2/λ* + C m^{−1/5} + 2e^{−g²/6}).
- **Tasso per M fissato**: per M fissato, Lean dà il tasso O_{M,g}(m^{−1/2}), ma con ipotesi [BR, §22] e senza i termini λ + λ·1[u = 0]. Lì il bound su Pr(Z = 0) è K/√m, non 2/λ + O(·).
- **g**: paper g > 0, Lean g ≥ 0. "Set η = 1/10" diventa superfluo nell'enunciato se si passa alla forma o(1).
- **Conseguenze nel paper**: il termine O(m^{−1/5}) compare anche nella p del Teorema R″ (voce 9) e nella sua dimostrazione ("6 ln(mM)·O(m^{−1/5}) = o(ln mM)"). In Lean è sostituito dal fattore (1 + ε) nella forma con ε, ed è esplicito (C m^{−1/5}) nella forma con il tasso `thmRpp_rate` (voce 9).

**Wording suggerito.**
> Fix g ≥ 0. For every ε > 0 there is m₀(g, ε) such that, for all M ≥ 2, m ≥ m₀, s with |s − mμ| ≤ gσ√m and u with |u| ≤ M, u ≡ s (mod 2):
> 1. |λ/λ_m − 1| ≤ ε, where λ := E[Z(u) | S_E = s];
> 2. E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + ε);
> 3. Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + ε.
> Moreover there is C(g) such that, for m ≥ m₀(g), the ε in (2) and (3) can be taken equal to C m^{−1/5}, uniformly in M ≥ 2 and in the window (formalized). For fixed M, the error terms are O_{M,g}(m^{−1/2}).
