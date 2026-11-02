"""ARCS (Arc-guided, Residue-Certified Search): the entry point.

    solve(W, T)                          the default form: every parameter derived from the instance (arcs_rho.py, §5.7)
    solve(W, T, delta=1e-3, max_ops=2**34, memory=2**30)
    solve(W, T, mode="fixed")            the fixed constants of the reference run BENCH5 v2 (arcs_solver.py)

Answers: ("YES", indices) | ("NO", q, c) | ("FAIL", reason). In the default form a fourth element, the certificate
(derived parameters, predicted block and cost, random draws), is returned as well. Every YES is a subset of the indices with
sum T; every NO is certified by a class count (q >= 2), by the range (q = 0) or by an exhaustive endgame on the whole
instance (q = -3); FAIL asserts nothing."""
def solve(W, T, mode="rho", **kw):
    if mode == "rho":
        from arcs_rho import arcs_solve_rho
        return arcs_solve_rho(W, T, **kw)
    if mode == "fixed":
        from arcs_solver import arcs_solve
        return arcs_solve(W, T)
    raise ValueError('mode must be "rho" or "fixed"')
