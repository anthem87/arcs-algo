# CRITERION_BENCH7 v1 — ARCS driven by the instance (mode "rho"), alone (preregistered, 29/10/2026)

Rules: this file is frozen before any instance is generated. Its sha256 is the seed of all instances
(seed_base = int(sha256[:16], 16); instance i of problem P: seed = seed_base + 1000·P + i). One run.
No parameter is changed after seeing a result; any change of code or criterion gives a new version with a new hash and
a new run, and this run stays published as it is. Every answer goes through an independent checker (checker7.py),
which does not import the solver's code. Machine: cloud container, one process, one thread, wall-clock times.
No other method is run: this benchmark measures ARCS-ρ against the ground truth and against its own predictions.

## Method
ARCS-ρ: arcs_rho.arcs_solve_rho(W, T, delta = 1e-3, max_ops = 2**34, memory = 2**30). The steps are those of ARCS
(sort; preprocessing with class counts and the selection ε_k = min(1, 1/m); range NO; modular NO; descent by the arc
score; handover below 𝒵*; filtered endgame with a uniform prime; exhaustive meet-in-the-middle or residue scan;
declared FAIL). Every parameter is derived from the instance before the descent (R1–R8 in the docstring): the density
ρ = n/log₂ D, the handover density 𝒵* from delta, the predicted block m* from the suffix variances, the predicted cost
and the choice of endgame from m* and the memory, the moduli from n, delta and the predicted cost. If the predicted
cost exceeds max_ops or the memory, ARCS-ρ answers FAIL with the prediction, after its NO certificates.
Randomness from the operating system; every draw is in the certificate.

## Problems and instances
- P1 reconciliation: n = 800 amounts uniform in [10³, 10⁹]; 6 planted (subset of size uniform in [n/4, 3n/4]);
  2 controls C1 (multiples of 50, target ≡ 37 mod 50: NO).
- P2 wallet: n = 1000 uniform in [1, R], R ∈ {10⁸, 10¹⁰}, 3 per R, planted subset of 500.
- P3 partition: n = 200 uniform in [10⁴, 10¹⁰], S made even, target S/2. 6 instances.
- P5 wholesaler: n = 200, 195 multiples of 1009 and 5 uniform in [1, 1009·10⁹]; 6 planted, 6 impossible.
- P6 critical block: n = 50 uniform in [1, 2⁵⁰] (ρ ≈ 1); 6 planted (subset of 25), 6 random targets in [0, S].
- P7 beyond int64: n = 40 uniform in [1, 2⁷⁰]; 6 planted (subset of 20).
- P8 sparse, small: n = 40 uniform in [1, 2⁶⁰] (ρ ≈ 0.67); 6 planted (subset of 20), 6 random targets in [0, S].
- P9 sparse, large: n = 100 uniform in [1, 2¹¹⁰] (ρ ≈ 0.91); 3 planted (subset of 50).

## Criteria (decided before the run)
- Correctness: 0 wrong answers. A subset is right if the checker verifies indices, multiset and sum; a NO (q, c) with
  q ≥ 2 if the reachable residues mod q, recomputed in integer arithmetic, exclude c; a NO (0, 0) if T < 0 or T > S;
  a NO (−3, −3) ("exhaustive") if the checker's own meet-in-the-middle (independent code, exact integers) finds no subset.
- P1, P2, P3, P5: every instance answered correctly (planted: YES; impossible: NO with a valid certificate).
- P6: 12/12 answered correctly (YES or exhaustive NO). P7: 6/6. P8: 12/12.
- P9: 3/3 answered FAIL with a predicted cost or memory above the limits, each in less than 1 s.
- Prediction: on every record with a handover, report m_pred − m (predicted minus actual block). Pass if
  |m_pred − m| ≤ 2 on at least 90% of them.
- Speed (reported, not a criterion): median time per problem.
- Every FAIL must carry one of the declared reasons: "predicted …", budget, scored-out, both-out, end, endgame, n>1020.
- Controls that must fail: K1 the checker rejects a corrupted solution; K2 the checker rejects a false NO certificate;
  K3 all-even weights with an odd target: NO (q = 2); K4 max_ops = 2²⁰ on P6 #0: FAIL with a predicted cost, no answer.
- Outcome published in full.
