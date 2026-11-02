# arcs-algo

Code of the paper *Arcs of Π(1+z^p): prime races, the Gaussian core, Dirichlet L-functions and a certified solver for Subset Sum*
(A. Mennillo, 2026).

**ARCS** (Arc-guided, Residue-Certified Search) decides and solves Subset Sum: given positive integers W and a target T it answers

- `("YES", indices)`: a subset of the indices with sum T, always verified;
- `("NO", q, c)`: a certificate. q ≥ 2: no subset sum is ≡ T (mod q), checkable in integer arithmetic; q = 0: T outside [0, ΣW];
  q = −3: an exhaustive endgame ran on the whole instance;
- `("FAIL", reason)`: no claim, with the reason.

```python
import sys; sys.path.insert(0, "python/algorithm")
from arcs import solve
solve(W, T)                                   # default: parameters derived from the instance (§5.7)
solve(W, T, delta=1e-3, max_ops=2**34, memory=2**30)
solve(W, T, mode="fixed")                     # the fixed constants of the reference run BENCH5 v2
```

In the default form the user gives only `delta` (accepted probability of FAIL on a YES instance), `max_ops` (operations to wait
for) and `memory` (bytes). The density ρ = n/log₂ D, the handover threshold λ*, the predicted final block m* and its cost, the
endgame and the moduli are computed from the instance before the descent; if the predicted cost exceeds the limits the answer is
FAIL with the prediction. The certificate returned with each answer holds these values and every random draw.
Limits: n ≤ 1020 and positive weights.

## Layout

| Folder | Content |
|---|---|
| `python/algorithm/` | the solver: `arcs.py` (entry point), `arcs_rho.py` (default), `arcs_solver.py` (fixed constants), `arcs_dyn.py`, `endgame_fast.py`, `arcs_adaptive.py` (shared helpers), `theorem_mode.py` (the algorithm of Theorem R″); the first version and its tests |
| `python/arcs_theory/` | the arcs of the prime product, lobes, Edgeworth core, prime races on the arcs (§2–4) |
| `python/random_weights/` | Section 6: local limit theorem, moments, conditioned counts |
| `python/certification/` | interval-arithmetic certifications (Arb): lobes (Corollary Q′), the real segment (R) and a zero on the critical line of the cubic character mod 7 (Theorem S at q = 14) |
| `python/propagation/` | Sections 7–8: constraint propagation and the solver as propagation |
| `python/figures/` | one script per figure (Figure 5: `python/arcs_theory/arcs_fig.py`); `arcs_trace.py` is a shared helper that records one run of ARCS for `fig_take_skip.py` and `fig_join.py`; output next to the script |
| `pseudocode/` | `ARCS_pseudocode.md`: ARCS (default) and ARCS-FIXED, CLRS style |
| `lean/` | Lean 4: the certified answer checker (`checkYes`, `checkNo`, `checkRange`, proved sound; the exhaustive certificate (−3, −3), proved sound and complete) and `verify_bench`, an executable that runs these checkers on every answer of `benchmarks/bench5_v2` and `benchmarks/arcs_rho` (compiled code, outside the kernel: Lean proves the checkers sound, not the individual benchmark runs); the combinatorial and algebraic statements of the paper: Brown's lemma and Proposition 2.3 with Richert's theorem (§2), the Fourier and cumulant identities of Remark 3.1 and Propositions C and C′ (§3), the dummies, the blur identity, Lemma 5.1, Remark 5.2, Lemma 5.3 and the handover known in advance (§5), the centre rule, Corollary C″ and the finite parts of Lemmas B‴, C and J and of Theorem LV (§6), the propagation theory of §7 (Theorems 7.2–7.13, Propositions 7.8–7.10′, with corrected statements where the paper's are false) and Propositions 8.1–8.5 (§8). The analytic results are formalized as well: the arcs and their Edgeworth core (Theorem E, Propositions C, C′ and the Remarks of §3), the lobes (Lemmas L, W, Q, Corollary Q′), the prime races of §4 (Propositions 3, 3₀, Theorem S in general form and at q = 14), the local limit theorems and the second moments of §6 (Lemmas B0′, B with the rate m^{−1/5}, B‴, V, Proposition B′ with the limits of κ, κ_c, γ as M → ∞, Theorems R, R′, R″, LV). Published theorems enter as explicit, cited hypotheses (`def … : Prop`, never `axiom`): `SiegelWalfisz`, `VinogradovVaughan`, `JacksonThm`, `RosserSchoenfeld`, `PNTcons`, `VonKoch`, `BWThm` (Bringmann–Wellnitz) `BR22Edge` ([BR, Theorem 22.1] at every order) and, for Proposition 3, the GRH bound for π(x, χ) [Davenport]; the numerical certificates likewise: `ArbLobes`, `Arb3` (`python/certification/certify_lobes_arb.py`), (R) and `R14` (`certify_L_real_segment.py`), `CubicZero14` (`certify_zero_cubic7.py`) and `LVRhoCert` (`python/random_weights/lv_rate_certified.py`). Not formalized: Proposition B⁗ (a table of exact convolutions, numerical only: not reproducible in the kernel without `native_decide`) and the running times O(…) of Theorems R, R′, R″, Corollary C″ and Theorem 7.2 (analysis on paper). No `sorry`; only the standard axioms. |
| `benchmarks/` | preregistered runs (below) |

## Benchmarks

Each folder is frozen by its `*.sha256` files (criterion, code, results) and is run from inside the folder.
The criterion is hashed before any instance is generated, its hash seeds the instances, there is one run, and every answer goes
through an independent checker that does not import the solver.

| Folder | Run |
|---|---|
| `benchmarks/bench5_v2/` | reference run of the fixed constants (§5.7, Figure 9), with a plain-text export of every instance and answer; the criterion `CRITERIO_BENCH5_v2.md` was written in Italian before the run and its sha256 seeds the instances, so it is kept unchanged, with the English translation `CRITERION_BENCH5_v2.en.txt` |
| `benchmarks/arcs_rho/` | the default solver alone (§5.7, *Parameters derived from the instance*) |

The copies of the solver inside a benchmark folder are the code that ran. The files in `python/algorithm/` have the same code and
may differ only in comments (`arcs_rho.py`, `arcs_adaptive.py` against `benchmarks/arcs_rho/`; `arcs_dyn.py`, `endgame_fast.py`
against `benchmarks/bench5_v2/`). In the code, the constant `RHO` is the threshold λ* of the paper.

## Requirements

Python 3 with NumPy, SymPy, mpmath, SciPy and matplotlib; python-flint (Arb) for the certifications; OR-Tools for the CP-SAT method of BENCH5 only. The versions are listed in `requirements.txt`.
Lean 4 with the toolchain pinned in `lean/lean-toolchain`; Mathlib as pinned in `lean/lake-manifest.json` (do not run `lake update`).

## Reproduce

From a fresh copy of the repository:

```sh
pip install -r requirements.txt
pip install ortools          # optional: only for the CP-SAT method of BENCH5

cd lean
lake exe cache get          # prebuilt Mathlib
lake build                  # about 46 min on an 8 GB laptop, Mathlib prebuilt
B=../benchmarks
lake exe verify_bench $B/bench5_v2/results_v2.json $B/bench5_v2/results_v2_check.txt
lake exe verify_bench $B/arcs_rho/results_v1.json  $B/arcs_rho/results_v1_check.txt
cd ..

cd python/certification
python certify_lobes_arb.py         # ArbLobes, Arb3: 144/144 moduli certified (about 1 min); compare with lobes_arb.txt
python certify_L_real_segment.py    # (R), R14: chi5, chi7, chi8 CERTIFIED on [1/2, 1] (seconds); compare with out128.txt
python certify_zero_cubic7.py       # CubicZero14: Z(t) of chi7 changes sign on [4.35546875, 4.3564453125]; compare with zero_cubic7_out128.txt
cd ../random_weights
python lv_rate_certified.py         # LVRhoCert: "certified for all M >= 2: rho <= 0.44495"
python b_prime_exact.py             # Proposition B': exact second moments against the formula
```

Each `verify_bench` run ends with `RESULT: all ARCS answers verified` (a run of the proved checkers as compiled code, not a kernel proof). The comment after each script names the Lean hypothesis it certifies. To list the axioms of a theorem, e.g. `#print axioms ArcsAlgo.LLT.propBprime_uncond` in a file that imports `ArcsAlgo`: only `propext`, `Classical.choice` and `Quot.sound` appear.

## Building and checking the Lean part

Install `elan` (the Lean version manager); it reads `lean/lean-toolchain` and installs that toolchain. The Mathlib revision is
pinned in `lean/lake-manifest.json`; do not run `lake update`.

```sh
cd lean
lake exe cache get        # prebuilt Mathlib for the pinned revision (a few GB)
lake build                # the library and verify_bench; no sorry, only the standard axioms
lake exe verify_bench ../benchmarks/bench5_v2/results_v2.json ../benchmarks/bench5_v2/results_v2_check.txt
lake exe verify_bench ../benchmarks/arcs_rho/results_v1.json ../benchmarks/arcs_rho/results_v1_check.txt
```

## Figures

The figures are not stored in the repository. Each script in `python/figures/` (and `python/arcs_theory/arcs_fig.py` for
Figure 5) writes its PNG and PDF next to itself.
