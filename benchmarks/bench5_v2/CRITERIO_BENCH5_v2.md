# CRITERIO_BENCH5 v2 — benchmark non progressivo dei cinque problemi (preregistrato, 28/10/2026)

Regole: questo file è congelato prima di generare qualsiasi istanza. Il suo sha256 è il seme di tutte le istanze
(seed_base = int(sha256[:16], 16); istanza i del problema P: seed = seed_base + 1000·P + i). Un solo run.
Nessun parametro di nessun metodo viene cambiato dopo aver visto un risultato; qualsiasi modifica di codice o di
criterio dà una v2 con un nuovo hash e un nuovo run, e il run v1 resta pubblicato così com'è.
Ogni risposta passa da un checker indipendente (checker5.py), che non importa il codice dei solver.
Macchina: container cloud, un processo, un thread per metodo, misure di tempo a parete.

## Differenze dalla v1 (solo codice di ARCS; problemi, metodi avversari e criteri identici)
La v1 resta pubblicata così com'è. La v2 cambia solo questo, deciso dopo la revisione del codice e prima di questo run:
1. endgame filtrato: il primo P è uniforme fra i primi di [P₀, 2P₀), estratto per rigetto con il generatore
   seminato del solver (v1: sympy.randprime, non uniforme e non seminato);
2. endgame: la guardia m ≤ 44 sul MITM completo vale anche nel ramo 𝒵 < 8 (v1: solo dopo i round);
3. endgame: un round isolato in una funzione (nessun cambio di comportamento); controllo m·max(W) < 2⁶³;
4. ArcsDyn: nessuna coppia gcd se n < 2 (nessun effetto sulle istanze di questo benchmark).
Il seme cambia perché cambia questo file: le istanze della v2 sono nuove.

## Metodi
- ARCS: solver ad archi con Q dinamico (arcs_dyn.ArcsDyn: Q0 = 24, DCAP = 2000, PAIRS = 64, C_EPS = 1, seed 0)
  e endgame filtrato (endgame_fast.endgame_mod, primo uniforme sui primi di [P₀, 2P₀), 6 round, MITM completo solo se m ≤ 44);
  ρ* = 5·10⁴, CAP = 60. Se al suffisso 0 una classe è vuota per un modulo selezionato, ARCS risponde NO con il
  certificato (q, c); altrimenti risponde con un sottoinsieme oppure FAIL (nessuna affermazione).
- CPSAT: OR-Tools CP-SAT 9.15, una variabile booleana per peso, vincolo Σ w_i x_i = T, 1 worker, limite 60 s.
  Risposte: sottoinsieme (FEASIBLE/OPTIMAL), NO (INFEASIBLE, prova del solver), FAIL (limite di tempo).
- BNB: reimplementazione della branch-and-bound di Bitcoin Core (ordinamento decrescente, DFS include/escludi,
  potatura su somma corrente > T e su somma corrente + residuo < T, tetto 100 000 tentativi, finestra esatta).
- KK: differenziazione di Karmarkar–Karp (riporta la differenza ottenuta).
- CKK: Karmarkar–Karp completo (Korf), ricerca di differenza 0 (o 1 se S dispari), limite 60 s.
- DP: programmazione dinamica a bitset. Si esegue solo se n·S ≤ 10¹¹ bit; altrimenti si registra la memoria
  richiesta (n·S bit) come N/A.
- QFIX: ARCS con moduli fissi q = 2..24 (solo P5). NOARC: ARCS senza moduli (solo P5).

## Problemi e istanze
- P1 riconciliazione (Maria). n = 800 importi in centesimi, uniformi in [10³, 10⁹]. Target = somma di un
  sottoinsieme piantato di taglia uniforme in [n/4, 3n/4]. 6 istanze. Controllo C1: 2 istanze con importi
  multipli di 50 centesimi e target ≡ 37 (mod 50): la risposta corretta è NO.
  Metodi: ARCS, CPSAT, DP (N/A atteso).
- P2 wallet senza resto (Luca). n = 1000 importi uniformi in [1, R], R ∈ {10⁸, 10¹⁰}, 3 istanze per R. Target =
  somma di un sottoinsieme piantato di 500 elementi (parametri del benchmark CRISP). Metodi: ARCS, BNB, CPSAT, DP.
- P3 eredità (due fratelli). n = 200 valori in centesimi uniformi in [10⁴, 10¹⁰], ultimo valore aggiustato di
  +1 se serve per avere S pari; target S/2 (partizione perfetta). 6 istanze. Metodi: ARCS, KK, CKK, CPSAT, DP.
- P4 primi distinti. Pesi {1} ∪ {p ≤ N}, N ∈ {2000, 8000, 16000}; target T = ⌊S/2 + kσ⌋, k ∈ {0, 1, 2, 3},
  σ² = Σw²/4. Grandezza: r_N(T), numero di sottoinsiemi con somma T. Riferimento: DP in virgola mobile con
  riscalatura a potenze di 2 (somme di non negativi: errore relativo ≤ n·2⁻⁵², a meno dei contributi sotto 2⁻¹⁰²²
  volte il massimo corrente, che vanno persi per underflow). Metodo ARCS-COUNT: densità gaussiana alla scala
  reticolare 1 con la serie di Edgeworth ottenuta sviluppando exp(Σ_{j=4,6,8} κ_j (it)^j/j!) e tenendo tutti i
  termini di ordine ≤ 3 in 1/n (κ₄; κ₆, κ₄²; κ₈, κ₄κ₆, κ₄³); cumulanti di w·Bernoulli(½): κ₂ = w²/4, κ₄ = −w⁴/8,
  κ₆ = w⁶/4, κ₈ = −17w⁸/16, sommati sui pesi; i cumulanti dispari sono nulli.
- P5 grossista. n = 200 pesi in grammi: 195 multipli di 1009 (1009·u, u uniforme in [1, 10⁹]) e 5 uniformi in
  [1, 1009·10⁹]. 6 target piantati (sottoinsieme casuale con probabilità ½ per elemento) e 6 target impossibili
  (residuo mod 1009 fuori dai 32 residui raggiungibili dai 5 pesi non divisibili, valore vicino a S/2).
  Metodi: ARCS, QFIX, NOARC, CPSAT.

## Criteri (decisi prima del run)
- Correttezza (tutti i metodi, tutti i problemi): 0 risposte sbagliate. Un sottoinsieme è giusto se il checker
  verifica somma e multinsieme; un NO di ARCS è giusto se il checker ricalcola in aritmetica intera N_c(q) = 0;
  un NO di CPSAT conta come prova del solver.
- P1, P2, P3, P5 (piantati): «ARCS vince» se risolve più istanze del migliore avversario, oppure lo stesso
  numero in tempo mediano almeno 10 volte minore.
- P5 (impossibili): «ARCS vince» se certifica più NO del migliore avversario.
- P3: un metodo risolve un'istanza solo con differenza 0 (S pari per costruzione).
- P4: ARCS-COUNT è valido se l'errore relativo è ≤ 10⁻⁶ in ogni cella; «vince» se è valido ed è almeno 100 volte
  più rapido del riferimento DP.
- Controlli che devono fallire (sanità della catena): K1 il checker deve rifiutare una soluzione corrotta
  (un peso sostituito); K2 il checker deve rifiutare un certificato NO falso (classe non vuota); K3 su pesi tutti
  pari con target dispari ARCS deve rispondere NO (q = 2), non con un sottoinsieme.
- Esito pubblicato per intero, anche dove ARCS non vince.
