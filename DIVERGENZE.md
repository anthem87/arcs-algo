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
| 1 | Lemma Q | 171 | `LemmaQ.lean`: `lemmaQ1`, `lemmaQ1_avg`, `lemmaQ2`, `rhsQ_anti`, `lemmaQ2_Rq`, `Rq_bound`, `Rq_bound_tau`, `lemmaQ3`; `RemarkLobe.lean`: `anti_first_min` | (1): intervallo semiaperto e disuguaglianza stretta; (2), (3): q ≥ 1 invece di q ≥ 3; (3): 2^{ω(q)} invece di τ(q); ℓ_q ≤ R_q non enunciato a sé; β corretta già nel rev1 |
| 2 | Teorema E | 280 | `EdgeE2.lean`: `thmE`, `thmE2`; `ThmE1.lean`: `thmE1`, `thmE1_B40`; `ThmE3.lean`: `thmE3`; `EdgeRel.lean`: `thmE2_rel` | o(1) sostituito da δ > 0 con N₀(δ); costanti esplicite e termini esponenzialmente piccoli tenuti a parte; B > 40 serve solo per (1); nel caso 𝒱 = {w} compare s̃* al posto di s*; in (3) ℓ_q è preso nella forma ℓ*_q (estremo inferiore 1/(2q)) |
| 3 | Remark (the formula of Proposition C) | 311 | `RemarkPropC.lean`: `thmC2_rel`, `thmC2_paper`; `RemarkPropCV.lean`: `thmC2_vanish` | antecedente esplicito \|ν\| ≤ C_νN^{3/2+ε/2}; esponente relativo più forte (−1 + 6ε, costante 12); q ∈ 𝔈 non richiesto; nel caso 𝒱 = {w} la forma assoluta è diversa da quella di (2) |
| 4 | Proposizione B′ | 720 | `SecondMoment/BPCondT.lean`: `propBprime_cond`; `SecondMoment/BPUT.lean`: `propBprime_uncond`; `SecondMoment/BPConst.lean`: `CCu_eq` | g ≥ 0; la forma "senza condizionamento" è in Lean condizionata all'evento di parità (anche al denominatore); i limiti per M → ∞ (1/5, 1/80, −√3/80) non sono formalizzati |
| 5 | Teorema 7.2 | 978 | `Structural.lean`: `Tstruct_idem`, `Tstruct_of_closed`, `inject_dom`, `Eval_fixes`, `Eval_nonempty`, `Eval_fixes_exactly`, `Eval_blocks_counterexample`, `parity_supported`, `def_supported`, `Tstruct_not_idem_counterexample` | variabili booleane; Par dato dal suo risultato; in (c) ipotesi diversa e conclusione più debole ("al più un valore", senza "without blocking"); costi O(·) non formalizzati |
| 6 | Teorema 7.4 | 998 | `Propagation.lean`: `Tcomp_le`, `Tcomp_mono`, `Tcomp_eq_self_iff`, `Tfail_stable`, `Tcomp_bound_counterexample`, `limit_greatest`, `limit_supported`, `limit_perm`, `schedule_eq_limit` | (iii) per l'operatore con fallimento assorbente `Tfail` e con domini iniziali non vuoti; (iv) con il limite definito come iterato `size W` volte, e l'indipendenza dall'ordine enunciata come permutazione o schedule; constraint generici, Val finito |
| 7 | Lemma J | 874 | `RandomWeights.lean`: `roundSuccess_ge` | forma astratta (misura finita, masse non normalizzate, Z_r arbitrari); convenzione 0/0 = 0; nessuna divergenza sostanziale rispetto al rev1 |
| 8 | Lemma V | 904 | `Uniform/LemV2.lean`: `lemmaV`, `sum_pairPA`, `DeqA` | (1 + o(1)) sostituito da (1 + ε) con m₀(g, ε); g ≥ 0; il denominatore è λ = E[Z \| S_E = s] (nel paper è 𝒵); e^{g²/2} già nel rev1 |
| 9 | Teorema R″ | 927 | `Uniform/RppRound.lean`: `succB_ge`, `succB_unif`, `pRpp`; `Uniform/RppRounds.lean`: `thmRpp_gen`; `Uniform/RppAsymp.lean`: `Hm`, `exists_Hm`, `params_Rpp`, `thmRpp` | p senza il termine O(m^{−1/5}) e con /(1 + ε); scelta di R diversa; m dato da `Hm` (intervallo a due lati); serve 2e^{−g²/6} < 1 e M ≥ M₀; forma "probabilità congiunta"; costo e tempo di esecuzione non formalizzati |
| 10 | Lemma B | 696 | `Uniform/LemmaB1.lean`: `lemmaB1_unif`; `Uniform/LemmaB2.lean`: `lemmaB2_unif`, `lemmaB3_unif`, `lemmaB2_rate`, `lemmaB3_rate`; `SecondMoment/LemmaB.lean`: `lemmaB_fixedM` | (2), (3): tasso O(m^{−1/5}) uniforme in M dimostrato (rev1 coperto); non coperto O(m^{−1/2+3η}) per ogni η (versione precedente); (1) in forma o(1); g ≥ 0 |

---

## 1. Lemma Q

### Paper (riga 171)

> **Lemma Q (lobes of every arc).** Let q ≥ 3, h_q(x) = log|Φ_q(−e(x))| and κ = Cl₂(π/3)/π = 0.32307…
> 1. h_q is non-increasing on [0, 1/(2q)], so A_q(X) ≤ φ(q)c_q for X ≤ 1/(2q), and X_q ≥ 1/(2q).
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
- **(1)**: il paper dice "non-increasing on [0, 1/(2q)]" (intervallo chiuso). Lean dimostra "strettamente decrescente" su [0, 1/(2q)), intervallo semiaperto. Nel punto x = 1/(2q) il polinomio Φ_q(−e(x)) si annulla per q dispari, e in Lean log 0 = 0, quindi l'estremo va escluso. Anche "A_q(X) ≤ φ(q)c_q for X ≤ 1/(2q)" diventa in Lean una disuguaglianza **stretta** per 0 < X < 1/(2q): l'estremo X = 1/(2q) non è nell'enunciato Lean, e X = 0 è escluso perché in Lean A_q(0) = 0/0 = 0, non log|Φ_q(−1)|. "X_q ≥ 1/(2q)" sta in `anti_first_min` (RemarkLobe), con X_q definito come in `firstLocalMin`.
- **(2)**: Lean vale per ogni X > 0 e q ≥ 1, il paper per X ≥ 1/(2q) e q ≥ 3 (Lean è più generale). La catena "ℓ_q ≤ R_q" **non è enunciata come teorema Lean a sé**. Lean ha A_q(X) ≤ φ(q)R_q per X ≥ 1/(2q) (`lemmaQ2_Rq`), da cui ℓ_q ≤ R_q segue con X_q ≥ 1/(2q) (`anti_first_min`). Le due stime di R_q valgono in Lean per q ≥ 2.
- **(3)**: Lean dimostra A_q(X) ≤ κ·2^{ω(q)} per q ≥ 1, che è più forte di κτ(q) perché 2^{ω(q)} ≤ τ(q). La forma con τ(q) non è un enunciato Lean separato (compare solo nel docstring).

**Wording suggerito.**
> 1. For q ≥ 3, h_q is strictly decreasing on [0, 1/(2q)); hence A_q(X) < φ(q)c_q and A_q is strictly decreasing for 0 < X < 1/(2q), and every first local minimum X_q of A_q satisfies X_q ≥ 1/(2q), with A_q non-increasing on (0, X_q].
> 2. For q ≥ 1 and every X > 0, A_q(X) ≤ Σ_{μ(q/d)=1} min(log 2, κ/(dX)) + Σ_{μ(q/d)=−1} β(dX), with β as above, and the right side is non-increasing in X. Writing R_q for its value at X = 1/(2q) divided by φ(q), A_q(X) ≤ φ(q)R_q for every X ≥ 1/(2q), hence ℓ_q ≤ R_q; for q ≥ 2, φ(q)R_q ≤ 2^{ω(q)−1}(1 + log 2 + log rad q) ≤ τ(q) log(2eq)/2.
> 3. For q ≥ 1 and X ≥ 1, A_q(X) ≤ κ·2^{ω(q)} ≤ κτ(q).

---

## 2. Teorema E (arc expansion)

### Paper (riga 280)

> **Theorem E (arc expansion).** Fix B > 40 (B = 48 makes the error in (1) O(1/log N)) and 0 < ε < 1/8 (the statements for larger ε follow). As N → ∞, for 3 ≤ q ≤ 𝔓:
> 1. (minor arcs) sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + O((log N)^{5−B/8}) + O(M^{−1/2}))π(N)).
> 2. (emerging arcs) Let q ∈ 𝔈. With the cumulants κ_j* of Lemma W(3), s* = √κ₂* and z = (T − κ₁*)/s*, put
> $$\widehat H(T)=e^{-iTt^*}\,G(\theta^*)\,\frac{\varphi(z)}{s^*}\Big(1+\frac{\kappa_3^*}{6s^{*3}}He_3(z)+\frac{\kappa_4^*}{24s^{*4}}He_4(z)+\frac{\kappa_3^{*2}}{72s^{*6}}He_6(z)\Big).$$
> If 𝒱(a/q) = ∅, put 𝒜*_{a/q}(T) = e(−Ta/q)Ĥ(T) and Ω = 1. If 𝒱(a/q) = {w}, write 1 + e(wθ) = −iwt·e^{iwt/2}sinc(wt/2) and replace G by G̃ = G·e^{iwt/2}sinc(wt/2) in Ĥ: its value G̃(θ*) = G(θ*)e^{iwt*/2}sinc(wt*/2) replaces G(θ*), and the cumulants of G̃ at t*, those of G plus those of e^{iwt/2}sinc(wt/2) at t* (see the note after the theorem), replace the κ_j*. Put 𝒜*_{a/q}(T) = e(−Ta/q)·w·(d/dT)Ĥ(T) and Ω = w(|t*| + 1/s*); θ* stays the peak of |G|. Then, for every T,
> $$R_{a/q}(T)=\mathcal A^*_{a/q}(T)+O\Big(\Omega\,|G(\theta^*)|\,\frac{N^{-3/2+2\varepsilon}}{s^*}\Big)+O\big(2^ne^{(-\log2+\ell^*_q+o(1))\pi(N)}\big),\qquad \ell^*_q=\sup_{X\ge1/(2q)}\frac{A_q(X)}{\varphi(q)} .$$
> In particular, if 𝒱(a/q) = ∅, then R_{a/q}(T) = 𝒜*_{a/q}(T)(1 + O(N^{−1+2ε})) + O(2^n e^{(−log 2 + ℓ*_q + o(1))π(N)}) uniformly for |z| ≤ √(log N).
> 3. (other arcs) For q ∉ 𝔈, |R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ_q + o(1))π(N)).

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
        ‖Rarc B N q a T‖ ≤ 2 ^ (WN N).card * Real.exp ((-Real.log 2 + ellE q + δ) * Nat.primeCounting N))
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
- **Caso 𝒱(a/q) = {w}**: nel paper il termine d'errore è Ω|G(θ*)|N^{−3/2+2ε}/s* con Ω = w(|t*| + 1/s*). In Lean **s* è sostituito da s̃***, la radice del secondo cumulante esatto di G̃ in t*, sia in Ω sia al denominatore. I cumulanti sono quelli esatti di G̃ in t*, come già dice il rev1.
- **Picco**: in Lean t* è caratterizzato come zero di F′ con |t*| ≤ 4|ν_{a/q}|/S₂. "θ* stays the peak of |G|" corrisponde a questo.
- **q ∈ 𝔈 in (2)**: è un'ipotesi dell'enunciato Lean, ma la dimostrazione non la usa (docstring di `thmE2`).
- **(3)**: il paper scrive ℓ_q (sup per X ≥ X_q), Lean usa ℓ*_q = max(0, sup per X ≥ 1/(2q)) (`ellE`). Per q ∉ 𝔈 e X_q primo minimo locale di A_q le due quantità coincidono: **dimostrato** in `ArcsAlgo.Core.ellE_eq_ellq` (`RemarkLobe.lean`, 2 nov 2026; da `remark_lobe_max`, `remark_lobe_other`, `lemmaQ1_avg` e `hq_zero`: A_q(1/(2q)) ≤ h_q(0) = 0 ≤ ℓ_q). L'enunciato (3) di `thmE` resta scritto con `ellE`; insieme a `ellE_eq_ellq` dà la forma del paper.
- **"In particular"**: costante 12, δ al posto di o(1), condizione |z| ≤ √(log N) con z reale costruito con Re κ₁*.

**Wording suggerito.**
> Fix 0 < ε < 1/8. For every δ > 0 there is N₀ such that for N ≥ N₀, 3 ≤ q ≤ 𝔓, (a, q) = 1 and every T:
> 1. (minor arcs; here B > 40) sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + δ)π(N)); more precisely, for every B > 0, sup_{θ∈𝔪}|F_N(e(θ))| ≤ 2^n exp((−log 2 + C((log N)^{5−B/8} + M^{−1/2}))π(N)).
> 2. (emerging arcs; every B > 0) […] If 𝒱(a/q) = ∅,
> |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ |G(θ*)|(N^{−3/2+2ε}/s* + 5e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> If 𝒱(a/q) = {w}, let s̃* be the square root of the second cumulant of G̃ at t* and Ω = w(|t*| + 1/s̃*); then
> |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ |G(θ*)|(Ω N^{−3/2+2ε}/s̃* + w e^{−N^{2ε}/(16384 log N)} + 4e^{−N^{2ε}/(512 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> In particular, if 𝒱(a/q) = ∅ and |z| ≤ √(log N), |R_{a/q}(T) − 𝒜*_{a/q}(T)| ≤ 12N^{−1+2ε}|𝒜*_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)}.
> 3. (other arcs; every B > 0) For q ∉ 𝔈, |R_{a/q}(T)| ≤ 2^n exp((−log 2 + ℓ*_q + δ)π(N)) (and ℓ*_q = ℓ_q for q ∉ 𝔈).

---

## 3. Remark (the formula of Proposition C)

### Paper (riga 311)

> **Remark (the formula of Proposition C).** If ν_{a/q} ≪ N^{3/2+ε/2}, as under GRH for the odd characters mod q (for fixed q), the peak lies well inside the core of a/q, and the linear tilt e^{−νσ} on the core is dominated by the Gaussian decay. The same proof, run with the expansion at a/q instead of θ*, then gives (2) with the arc term 𝒜_{a/q} of Proposition C. When 𝒱(a/q) = ∅ the error is relative, O(N^{−1/2+3ε}), uniformly for |Re z| ≤ √(log N); z is now complex, with |Im z| ≍ |ν|/s*. When 𝒱(a/q) = {w} the bound keeps the absolute form of (2): the main term w·Ĥ′ ≈ −w·zφ(z)/s² vanishes at z = 0, so no relative bound holds near it. This is the form tested in Table 2. Unconditionally the expansion must be centred at the peak θ*, because ν_{a/q} is only known to be ≪ N²e^{−c√log N}.

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
- **Caso 𝒱 = {w}**: il paper dice "keeps the absolute form of (2)". La forma assoluta dimostrata in Lean **non** è quella di (2) (Ω|G(θ*)|N^{−3/2+2ε}/s*): è centrata in a/q, con |G(a/q)|, esponente N^{−3/2+7ε}, denominatore s̃², fattore e^{ν²/(2s̃²)} e termini esponenzialmente piccoli espliciti.
- **"|Im z| ≍ |ν|/s*"**: è una frase descrittiva, non fa parte di un enunciato Lean di questa voce.

**Wording suggerito.**
> **Remark (the formula of Proposition C).** Fix C_ν > 0 and assume |ν_{a/q}| ≤ C_νN^{3/2+ε/2} (true under GRH for the odd characters mod q, for fixed q). Then, for every δ > 0 and N ≥ N₀(B, ε, C_ν, δ), uniformly in 3 ≤ q ≤ 𝔓 and (a, q) = 1, with the arc term 𝒜_{a/q} of Proposition C expanded at a/q:
> if 𝒱(a/q) = ∅, |R_{a/q}(T) − 𝒜_{a/q}(T)| ≤ 12N^{−1+6ε}|𝒜_{a/q}(T)| + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)} uniformly for |Re z| ≤ √(log N) (in particular the relative error is ≤ N^{−1/2+3ε});
> if 𝒱(a/q) = {w}, |R_{a/q}(T) − 𝒜_{a/q}(T)| ≤ |G(a/q)|(w e^{ν²/(2s̃²)}N^{−3/2+7ε}/s̃² + w e^{−N^{2ε}/(16384 log N)} + 4e^{4ν²/S₂}e^{−N^{2ε}/(2048 log N)}) + 2·2^n e^{(−log 2 + ℓ*_q + δ)π(N)} for every T; no relative bound is claimed, since the main term ≈ −w zφ(z)/s̃² vanishes at z = 0.

---

## 4. Proposizione B′

### Paper (riga 720)

> **Proposition B′ (the constant of the second moment).** Fix M ≥ 2 and g > 0, and put z = (s − mμ)/(σ√m). Uniformly in |z| ≤ g and |u| ≤ M with u ≡ s (mod 2),
> $$\frac{E[Z^2\mid S_E=s]}{\mathcal Z^2}=1+\frac{1+\mathbf1[u=0]}{\mathcal Z}+\frac{\kappa_c}m+\frac{\gamma_M\,z}{m^{3/2}}+O_{M,g}(m^{-2}),$$
> and, without conditioning but on the event S_E ≡ u (mod 2),
> $$\frac{E[Z^2]}{(EZ)^2}=1+\frac{1+\mathbf1[u=0]}{EZ}+\frac\kappa m+\frac{c_2(M,u)}{m^2}+O_M(m^{-3}),\qquad c_2(M,u)=c_2(M,0)-\frac{2\kappa u^2}{Ew^2},$$
> with
> $$\kappa=\frac{\operatorname{Var}(w^2)}{4(Ew^2)^2}\to\frac15,\qquad\kappa_c=\frac{\operatorname{Var}(w^2)-\operatorname{Cov}(w^2,w)^2/\operatorname{Var}(w)}{4(Ew^2)^2}\to\frac1{80},$$
> $$\gamma_M=\frac{\sigma\,(B-2\beta A)}{4(Ew^2)^2}\to-\frac{\sqrt3}{80},\quad A=[…],\ \beta=[…],\ B=\frac{E[R^2(w-\mu)]}{\operatorname{Var}(w)},$$
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
- **Parte "without conditioning"**: in Lean **entrambi** i momenti, e quindi anche il termine 1/EZ, sono condizionati all'evento S_E ≡ u (mod 2): E[Z²|S_E ≡ u]/E[Z|S_E ≡ u]². Letto alla lettera, "E[Z²]/(EZ)²" con medie non condizionate differisce dalla versione Lean per il fattore 1/Pr(S_E ≡ u (mod 2)) ≈ 2, perché Z(u) = 0 fuori dall'evento. Conviene scrivere esplicitamente le medie condizionate.
- **Limiti per M → ∞** (κ → 1/5, κ_c → 1/80, γ_M → −√3/80): **dimostrati** il 3 nov 2026 in `SecondMoment/BPLimits.lean` (`kapB_tendsto`, `kapcB_tendsto`, `gamB_tendsto`), per w uniforme su {1, …, M}; per simmetria Cov(w², w)/Var(w) = M + 1, R = (w − μ)² − σ² e B = 0 (`BB_eq_zero`).
- **c₂(M, 0)**: in Lean è definito come coefficiente della serie (`CCu M 0`). Il paper non ne dà una formula chiusa; i valori numerici 0.246, 0.274, 0.281 non sono formalizzati.
- **Ipotesi**: [BR, Theorem 22.1] a ogni ordine (`BR22Edge`), come ipotesi.

**Wording suggerito.**
> Fix M ≥ 2 and g ≥ 0 […] Uniformly in |z| ≤ g and |u| ≤ M with u ≡ s (mod 2), […] + O_{M,g}(m^{−2}), and, conditioning only on the event S_E ≡ u (mod 2), with Z̄_u = E[Z | S_E ≡ u (mod 2)],
> E[Z² | S_E ≡ u (mod 2)]/Z̄_u² = 1 + (1 + 1[u = 0])/Z̄_u + κ/m + c₂(M, u)/m² + O_M(m^{−3}), c₂(M, u) = c₂(M, 0) − 2κu²/Ew²,
> with κ, κ_c, γ_M as above; as M → ∞, κ → 1/5, κ_c → 1/80 and γ_M → −√3/80 (formalized).

---

## 5. Teorema 7.2 (structural collapse)

### Paper (riga 978; Definizione 7.1 alla riga 974)

> **Definition 7.1.** T_struct = Eval ∘ Par, where:
> - Par is union-find with parity on C_par [Tarjan]. Every variable is written x = r ⊕ b_x with r the root of its class; there is one domain per class (a shared cell). The shared form is 𝒮 = { W | ∀x ∼ y, W(x) = W(y) ⊕ (b_x ⊕ b_y) }.
> - Eval is one pass over Def in a topological order of the parity classes (the graph of the definitions with the classes of Par contracted, assumed acyclic): W(x) ← W(x) ∩ f_x(∏_{u∈pred(x)} W(u)) (forward image). A topological order of the variables alone is not enough (Remark 7.2′).
>
> **Theorem 7.2 (structural collapse).**
> - (a) T_struct ∘ T_struct = T_struct, and T_struct(W) ∈ 𝒮.
> - (b) For W ∈ 𝒮 closed under Eval, T_struct(W) = W.
> - (c) Injection: if W ∈ 𝒮 and one variable is fixed, its parity class is updated in O(1). If every input in I is fixed and no parity class contains two inputs, one pass of Eval fixes every defined variable, in time O(Σ_x cost(f_x)), without blocking; two inputs in one class may be fixed inconsistently, and the conflict appears as an empty cell, in O(1).
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
- **Dominio dei valori**: Lean tratta solo variabili **booleane** (Val = Bool). Il paper non lo dice in 7.1–7.2, anche se la parità lo suggerisce.
- **Par**: Lean non formalizza l'algoritmo union-find, ma il suo risultato (struttura `Classes`). Le affermazioni di complessità O(1) e O(Σ_x cost(f_x)) in (c) **non sono formalizzate**.
- **(c)**:
  - l'ipotesi Lean non è "every input in I is fixed and no parity class contains two inputs", ma "ogni classe ha cella con ≤ 1 valore, oppure è scritta da una definizione";
  - la conclusione di `Eval_fixes` è "ogni dominio ha **al più** un valore";
  - **"without blocking" è falso sotto le sole ipotesi del paper** (controesempio `Eval_blocks_counterexample`, `Structural.lean`): u input fissato a 0, classe di parità {x, y} con x = y, definizioni x := u e y := ¬u, ordine topologico sulle classi; nessuna classe contiene due input, eppure dopo una passata la cella di {x, y} è vuota, perché le due definizioni che scrivono la stessa classe sono in conflitto. Il paper attribuisce il blocco solo a due input nella stessa classe; qui il conflitto viene da due definizioni;
  - **forma corretta, dimostrata** (2 nov 2026): se la rete (parità e definizioni) ha una soluzione α con α(r) nella cella iniziale di ogni classe (stato iniziale coerente con le definizioni), Eval conserva α (`Eval_nonempty`: α(x) ∈ dominio, quindi nessun dominio vuoto), e sotto le ipotesi di `Eval_fixes` ogni dominio è **esattamente** {α(x)} (`Eval_fixes_exactly`);
  - "the conflict appears as an empty cell" è solo nel docstring;
  - l'iniezione è formalizzata (`inject_dom`) senza l'ipotesi W ∈ 𝒮, perché lo stato è per costruzione in forma condivisa.
- **(d)**: per i vincoli di parità basta W ∈ 𝒮, e il risultato riguarda i vincoli x = y ⊕ (b_x ⊕ b_y) tra variabili della stessa classe, cioè quelli assorbiti da Par. Per le definizioni basta la chiusura sotto Eval della singola definizione, più x ∉ pred(x); 𝒮 non serve.

**Wording suggerito.**
> Let Val = {0, 1}. Par is given by its result: a root r and a parity bit b_x for every variable. Assume the definitions are listed in an order topological on the parity classes: there is a rank on the classes such that every parent of a definition lies in a class of strictly smaller rank, and the list is sorted by the rank of the class it writes.
> (a) T_struct ∘ T_struct = T_struct and T_struct(W) ∈ 𝒮. (b) For W ∈ 𝒮 closed under Eval, T_struct(W) = W.
> (c) Injecting x = a changes only the cell of the class of x, and gives every y in that class a domain contained in {a ⊕ b_x ⊕ b_y}. If every class either has a cell with at most one value or is written by a definition, one pass of Eval leaves every domain with at most one value. If moreover the network (parity classes and definitions) has a solution α whose values lie in the initial cells, no domain becomes empty: every domain is exactly {α(x)}. Without such a solution the pass may block even when no class contains two inputs (two definitions writing one parity class may disagree). [Complexity claims: informal.]
> (d) For W ∈ 𝒮, υ(c, W) = 0 for every parity constraint between members of one class; for W closed under a definition x := f_x(pred x) with x ∉ pred x, that definition read forwards has zero defect at x.

---

## 6. Teorema 7.4

### Paper (riga 998)

> **Theorem 7.4.** Assume every T_c, c ∈ C_comp ∪ Def (definitions also read backwards), is the generalized arc consistency filter.
> - (i) T_comp is decreasing and monotone: T_comp(W) ⊑ W and W ⊑ W′ → T_comp(W) ⊑ T_comp(W′).
> - (ii) T_comp(W) = W ⟺ ∀c υ(c, W) = 0.
> - (iii) With μ(W) = Σ_v(|W(v)| − 1), and the empty domain counted as failure, T_comp^m(W) = T_comp^{μ(W)+1}(W) for every m ≥ μ(W) + 1. The extra step is the one that empties a domain: one variable with W = {0} and the assertion x = 1 has μ(W) = 0 and needs one step (Lean: `Tcomp_bound_counterexample`).
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

- **Ipotesi "C_comp ∪ Def (definitions also read backwards)"**: in Lean non c'è distinzione tra famiglie. Il teorema vale per una qualsiasi lista finita di vincoli; Val e V sono finiti.
- **(iii)**:
  - l'operatore iterato in Lean è T_fail (fallimento assorbente), non T_comp: "the empty domain counted as failure" va letto come "T_comp^m sostituito da T_fail^m";
  - Lean richiede in più che **tutti i domini iniziali siano non vuoti**;
  - il controesempio dimostra μ(W) = 0 e T_comp(W) ≠ W (servono μ(W) + 1 passi), non che "needs one step" esattamente.
- **(iv)**: il limite è definito come iterato `size W` volte di T_comp (senza fallimento). "Does not depend on the order of the filters" è formalizzato in due forme: invarianza per permutazione della lista (`limit_perm`), e uguaglianza col limite per ogni schedule di filtri di cs che raggiunga uno stato a difetto nullo (`schedule_eq_limit`). Lean non contiene un riferimento formale a [Apt].
- La correzione μ(W) + 1 è già nel rev1.

**Wording suggerito.**
> **Theorem 7.4.** Let C be a finite list of constraints over finite V and Val, and let every T_c be the generalized arc consistency filter. (i) […] (ii) […] (iii) Let T_fail be T_comp with the state replaced by the failure state as soon as a domain becomes empty. If every domain of W is non-empty, then T_fail^m(W) = T_fail^{μ(W)+1}(W) for every m ≥ μ(W) + 1; μ(W) rounds do not suffice in general (one variable with W = {0} and the assertion x = 1: μ(W) = 0 but T_comp(W) ≠ W). (iv) The limit W* = T_comp^{Σ_v|W(v)|}(W) has υ(c, W*) = 0 for every c and is the largest W′ ⊑ W with this property; it is unchanged under any permutation of C, and every schedule of filters from C that ends in a state with υ = 0 for all c ends in W*.

---

## 7. Lemma J

### Paper (riga 874)

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

### Paper (riga 904)

> **Lemma V (equal half-sums).** For 𝒫₁, let ψ = 2^{m/2}/M. Uniformly in M ≥ 2 and in the window, for m ≥ m₀(g),
> $$\frac{D_{\rm eq}}{\mathcal Z }\le 0.72\,e^{g^2/2}\,m\,(3\psi+\psi^2)\,(1+o(1)).$$

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
- "(1 + o(1)) for m ≥ m₀(g)" diventa in Lean "(1 + ε) per ogni ε > 0, per m ≥ m₀(g, ε)", uniformemente in M ≥ 2 e nella finestra (equivalente, ma è la forma esatta).
- g ≥ 0 invece di g > 0.
- Il denominatore è λ = E[Z | S_E = s] (`lamB`); il paper scrive 𝒵. Conviene unificare la notazione (λ, come nel Lemma B).
- La parità u ≡ s (mod 2) è implicita nell'ipotesi 2a = s + u.

**Wording suggerito.**
> **Lemma V.** For 𝒫₁ with |A| = ⌊m/2⌋, let ψ = 2^{m/2}/M. For every g ≥ 0 and ε > 0 there is m₀(g, ε) such that, for all M ≥ 2, m ≥ m₀ and s, u in the window, D_eq/λ ≤ 0.72 e^{g²/2} m(3ψ + ψ²)(1 + ε), where λ = E[Z(u) | S_E = s].

---

## 9. Teorema R″ (filtered endgame)

### Paper (riga 927)

> **Theorem R″ (filtered endgame).** Take the setting of Theorem R′ with R disjoint blocks in place of r, so that |T − S/2| ≤ S_G/2 − RmM, and fix g (say g = 3). In round j replace the meet-in-the-middle by the filtered endgame of §5.6 on E_j. The prime P_j is uniform among the primes of [P₀, 2P₀), and r_j is uniform in ℤ/P_j, both drawn independently of everything else. Assume P₀ ≥ 100.
>
> Then, given the weights of G and the block sums, the rounds fail independently. A round whose block sum lies in the window fails with probability at most 1 − p, where
> $$p=\Big[\frac{2P_0}{\lambda_m}\big(1+0.72\,e^{g^2/2}m(3\psi+\psi^2)\big)+6\ln(mM)\Big(1+\frac2{\lambda_m}+O(m^{-1/5})\Big)\Big]^{-1}(1+o(1)).$$
> The expected cost of a round is O(m·2^{m/4} + m·2^{m/2}/P₀).
>
> A round whose block sum leaves the window counts as failed; this happens with probability at most 2e^{−g²/6}, independently across blocks.
>
> Now choose P₀ = ⌊λ_m/2⌋ and m the least integer with 2^m ≥ (σ√m)^{4/3}, so m = (4/3)b + (2/3)log₂ b + O(1). Then:
> - p ≥ (1 − o(1))/(6 ln(mM)), and 2^{m/4} ≍ 2^{m/2}/P₀ ≍ (σ√m)^{1/3};
> - with R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})·p)⌉ rounds the algorithm fails with probability at most δ, provided n ≥ |G| + Rm;
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

**Lettura.**
- *Un round.* Sia g ≥ 0. Per ogni ε > 0 esiste m₀ tale che per M ≥ 2, m ≥ m₀, P₀ ≥ 100, |A| = ⌊m/2⌋ e s, u nella finestra: Pr(round riesce | S_E = s) ≥ p/(1 + ε), dove p⁻¹ = (2P₀/λ_m)(1 + 0.72e^{g²/2}m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m).
- *R round.* I pesi sono w_G ∈ {1..M}^h e R blocchi di m pesi, tutti uniformi e indipendenti. Il target T può dipendere da w_G e dalle somme dei blocchi; il round j include i blocchi K_j ∌ j, secondo una regola che guarda solo le somme dei blocchi. Allora Pr(|T − S/2| ≤ S_G/2 − RmM e tutti i round falliscono) ≤ (1 − (1 − 2e^{−g²/6})p/(1 + ε))^R.
- *Parametri.* Sia m con (σ√m)^{4/3} ≤ 2^m ≤ 2(σ√m)^{4/3} (`Hm`, che esiste per M ≥ 4) e P₀ = ⌊λ_m/2⌋. Per M ≥ M₀(g, ε, m₀) si ha m ≥ m₀, P₀ ≥ 100 e p ≥ (1 − ε)/(6 ln(mM)).
- *Teorema.* Se 2e^{−g²/6} < 1, ε ∈ (0, 1), δ > 0 e R(1 − 2e^{−g²/6})(1 − ε)/((1 + ε)6 ln(mM)) ≥ ln(1/δ), allora per M ≥ M₀ la probabilità che l'evento valga e tutti i round falliscano è ≤ δ.

### Differenza

- e^{g²/2} e λ_m (al posto di e^{λ²/2} e ρ_m) sono già nel rev1; lo è anche la caduta dell'ipotesi λ_m ≥ 2P₀ ("Assume P₀ ≥ 100").
- **p**: in Lean p **non contiene** il termine O(m^{−1/5}) dentro la parentesi, e il fattore (1 + o(1)) è sostituito da 1/(1 + ε) con m ≥ m₀(g, ε), uniformemente in M ≥ 2, P₀ ≥ 100 e nella finestra. Il termine O(m^{−1/5}) va tolto dalla formula di p, oppure dichiarato assorbito dal fattore (1 + ε).
- **Indipendenza**: "the rounds fail independently" non è enunciato come tale. Lean dimostra la stima risultante sulla probabilità congiunta "evento ∧ tutti i round falliscono" (fattorizzazione condizionale nella dimostrazione, `ThmRp.lean`). Lean ammette inoltre una regola generale K_j di inclusione dei blocchi e un target T dipendente da w_G e dalle somme dei blocchi.
- **Scelta di m**: il paper prende "the least integer with 2^m ≥ (σ√m)^{4/3}", Lean accetta ogni m con (σ√m)^{4/3} ≤ 2^m ≤ 2(σ√m)^{4/3}. `exists_Hm` mostra che il minimo m ≥ 1 con σ⁴m² ≤ 8^m soddisfa `Hm` (per M ≥ 4). L'asintotica m = (4/3)b + (2/3)log₂ b + O(1) e le relazioni 2^{m/4} ≍ 2^{m/2}/P₀ ≍ (σ√m)^{1/3} **non sono formalizzate**.
- **Scelta di R**: il paper prende R = ⌈ln(1/δ)/((1 − 2e^{−g²/6})p)⌉ con il p effettivo. Lean chiede R·(1 − 2e^{−g²/6})·(1 − ε)/((1 + ε)·6 ln(mM)) ≥ ln(1/δ), cioè usa il bound inferiore su p e un fattore (1 + ε)/(1 − ε) in più.
- **Ipotesi aggiuntive in `thmRpp`**: 2e^{−g²/6} < 1 (vero per g = 3, falso per g piccolo), ε ∈ (0, 1), M ≥ M₀(g, ε, δ). Il paper dice "fix g (say g = 3)" senza la condizione.
- **"provided n ≥ |G| + Rm"**: in Lean n = h + Rm per costruzione (i pesi sono G più i blocchi).
- **Costo e tempo** (O(m·2^{m/4} + m·2^{m/2}/P₀) per round, O(log(1/δ)·log(nM)·(n log n + M^{1/3}poly(b))), 2^{b/3+o(b)}): **non formalizzati**.
- Ipotesi: Rosser–Schoenfeld (Lemma K) soltanto.

**Wording suggerito.**
> **Theorem R″.** […] Assume P₀ ≥ 100 and fix g ≥ 0. For every ε > 0 there is m₀(g, ε) such that for M ≥ 2, m ≥ m₀ and every s, u in the window, a round succeeds, given S_E = s, with probability at least p/(1 + ε), where
> p = [(2P₀/λ_m)(1 + 0.72 e^{g²/2} m(3ψ + ψ²)) + 6 ln(mM)(1 + 2/λ_m)]^{−1}.
> Consequently the probability that |T − S/2| ≤ S_G/2 − RmM and all R rounds fail is at most (1 − (1 − 2e^{−g²/6}) p/(1 + ε))^R.
> Now let 2e^{−g²/6} < 1 (e.g. g = 3), ε ∈ (0, 1), choose m with (σ√m)^{4/3} ≤ 2^m ≤ 2(σ√m)^{4/3} (the least m with 2^m ≥ (σ√m)^{4/3} qualifies) and P₀ = ⌊λ_m/2⌋. For M ≥ M₀(g, ε): P₀ ≥ 100 and p ≥ (1 − ε)/(6 ln(mM)); and if R(1 − 2e^{−g²/6})(1 − ε)/((1 + ε)·6 ln(mM)) ≥ ln(1/δ), the algorithm fails with probability at most δ. [Cost and running time: informal, not part of the formalized statement.]

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
- **Conseguenze nel paper**: il termine O(m^{−1/5}) compare anche nella p del Teorema R″ (voce 9) e nella sua dimostrazione ("6 ln(mM)·O(m^{−1/5}) = o(ln mM)"). In Lean è sostituito dal fattore (1 + ε).

**Wording suggerito.**
> Fix g ≥ 0. For every ε > 0 there is m₀(g, ε) such that, for all M ≥ 2, m ≥ m₀, s with |s − mμ| ≤ gσ√m and u with |u| ≤ M, u ≡ s (mod 2):
> 1. |λ/λ_m − 1| ≤ ε, where λ := E[Z(u) | S_E = s];
> 2. E[Z(u)² | S_E = s] ≤ λ + λ·1[u = 0] + λ²(1 + ε);
> 3. Pr(Z(u) = 0 | S_E = s) ≤ 2/λ + ε.
> Moreover there is C(g) such that, for m ≥ m₀(g), the ε in (2) and (3) can be taken equal to C m^{−1/5}, uniformly in M ≥ 2 and in the window (formalized). For fixed M, the error terms are O_{M,g}(m^{−1/2}).
