"""Certification in ball arithmetic (Arb, via python-flint) of Corollary Q' of the subset-arcs paper:
       sup_{q not emerging} l_q = l_3.
   (a) l_3: lower bound from point values (after certifying that A_3 has a local minimum before them),
       upper bound by the interval method below.
   (b) the non-emerging q <= 20000 whose Lemma-Q bound R_q is not certified below l_3 (the "145 moduli"):
       certified upper bound U_q >= sup_{X >= 1/(2q)} A_q(X)/phi(q), and U_q < l_3.
   (c) all other non-emerging q <= 20000: R_q < l_3 certified.
   (d) q > 20000: 2^{w(q)}/phi(q) <= M_theta q^{-theta}, with M_theta certified, and the Lemma-Q(2) bound < l_3.
   Interval method on [a, b] (a, b rational):
       H(X) = int_0^X log|Phi_q(-e(x))| dx = sum_{d|q} mu(q/d)/d * [C(dX+d/2) - C(d/2)],  C(u) = -Cl2(2 pi u)/(2 pi),
       Cl2(t) = Im Li2(e^{it})  (exact closed form, evaluated in Arb at rational points);
       for X in [a, b]:  H(X) <= H(a) + (X-a) * S,  S >= sup_{[a,b]} log|Phi_q(-e(x))| from the product form
       sum_{(r,q)=1} log|2cos(pi(r/q+x))|, each term maximised exactly on the interval;
       hence A(X) = H(X)/X <= (H(a) + (b-a) S^+)/a  if the numerator is >= 0, else  .../b.
   Tail: |C| <= Cl2(pi/3)/(2 pi), so |H(X)| <= kappa * sum_{d|q, mu(q/d)!=0} 1/d for all X (kappa = Cl2(pi/3)/pi)."""
import sys, time
from fractions import Fraction as Fr
from math import gcd
from flint import arb, acb, ctx
from sympy import divisors, mobius, totient, factorint, primerange
ctx.prec = 128
PI = arb.pi()
def A_(x): return arb(x) if not isinstance(x, Fr) else arb(x.numerator) / arb(x.denominator)
def cl2(u):                       # Cl2(2 pi u) for rational u, reduced mod 1
    u = u - (u.numerator // u.denominator)
    if u == 0: return arb(0)
    z = (acb(0, 1) * (2 * PI * A_(u))).exp()
    return z.polylog(2).imag
def C(u): return -cl2(u) / (2 * PI)
KAPPA = cl2(Fr(1, 6)) / PI       # Cl2(pi/3)/pi
def emerging(q):
    if q == 1: return True
    if q % 2: return False
    return len(factorint(q // 2)) == 1
def mu_divs(q): return [(d, int(mobius(q // d))) for d in divisors(q) if mobius(q // d) != 0]
def H(q, X, md):
    s = arb(0)
    for d, m in md:
        s += m * (C(d * X + Fr(d, 2)) - C(Fr(d, 2))) / d
    return s
def ub(x): return x.mid() + x.rad()        # exact arb equal to the upper end of the ball
def sup_term(y0, y1):             # sup of log(2|cos(pi y)|) on [y0, y1], rational
    if y0.numerator // y0.denominator != y1.numerator // y1.denominator or y0.denominator == 1:
        return arb(2).log()       # contains an integer: |cos| = 1
    c0 = abs((PI * A_(y0)).cos()); c1 = abs((PI * A_(y1)).cos())
    c = ub(c0) if ub(c0) >= ub(c1) else ub(c1)
    if c > 1: c = arb(1)
    return ub((2 * c).log())
def interval_bound(q, a, b, md, res):
    S = arb(0)
    for r in res:
        S += sup_term(Fr(r, q) + a, Fr(r, q) + b)
    Sp = S if S > 0 else arb(0)
    num = ub(H(q, a, md) + A_(b - a) * ub(Sp))
    return ub(num / A_(a)) if num >= 0 else ub(num / A_(b))
def certify_sup(q, threshold, M=8, maxdepth=14):
    """returns (ok, U): U >= sup_{X >= 1/(2q)} A_q(X)/phi(q); ok iff U < threshold (certified)"""
    phi = int(totient(q)); md = mu_divs(q); res = [r for r in range(1, q + 1) if gcd(r, q) == 1]
    sig = sum(Fr(1, d) for d, _ in md)
    tail = KAPPA * A_(sig) / phi             # A/phi <= tail / X
    Xlo = Fr(1, 2 * q)
    # X* with tail/X* < threshold
    Xs = Fr(int(float((tail / threshold).mid()) * 1.01 * 8 * q) + 1, 8 * q)
    assert ub(tail / A_(Xs)) < threshold
    U = ub(tail / A_(Xs)); Uint = arb(-10)
    stack = []
    k = 0
    while True:
        a = Xlo + Fr(k, M * q); b = Xlo + Fr(k + 1, M * q)
        if a >= Xs: break
        stack.append((a, min(b, Xs), 0)); k += 1
    nint = 0
    while stack:
        a, b, dep = stack.pop(); nint += 1
        u = interval_bound(q, a, b, md, res) / phi
        if u < threshold:
            if ub(u) > U: U = ub(u)
            if ub(u) > Uint: Uint = ub(u)
        elif dep < maxdepth:
            m = (a + b) / 2; stack += [(a, m, dep + 1), (m, b, dep + 1)]
        else:
            return False, ub(u), nint, ub(u)
    return True, U, nint, Uint
def R_q(q):                       # Lemma Q(2) bound at X = 1/(2q), upper end, divided by phi(q)
    s = arb(0)
    for d, m in mu_divs(q):
        if m == 1:
            a = arb(2).log(); b = KAPPA * 2 * q / d
            s += ub(a) if ub(a) <= ub(b) else ub(b)
        else:
            L = Fr(d, 2 * q)
            if L > 1: s += ub(KAPPA / A_(L))
            else:
                a = KAPPA / A_(L); b = 1 - (2 * A_(L)).log()
                s += ub(a) if ub(a) <= ub(b) else ub(b)
    return ub(s / int(totient(q)))
def A_point(q, X): return H(q, X, mu_divs(q)) / A_(X) / int(totient(q))
if __name__ == "__main__":
    t0 = time.time(); out = []
    def say(s): print(s, flush=True); out.append(s)
    say(f"Arb precision {ctx.prec} bits; kappa = {KAPPA.str(12)}")
    # sanity: closed form vs product form at a point (numerical quadrature, float)
    import math
    qq, XX = 15, Fr(3, 7); n = 200000
    quad = sum(sum(math.log(abs(2 * math.cos(math.pi * (r / qq + (i + .5) / n * float(XX))))) for r in range(1, qq + 1) if gcd(r, qq) == 1) for i in range(n)) * float(XX) / n
    say(f"check H_15(3/7): closed form {H(qq, XX, mu_divs(qq)).str(10)} vs midpoint quadrature {quad:.6f}")
    # (a) l_3 lower bound: local minimum of A_3, then max of point values beyond it
    pts = [Fr(k, 200) for k in range(1, 400)]
    vals = [A_point(3, X) for X in pts]
    imin = None
    for i in range(1, len(vals) - 1):
        if vals[i] < vals[i - 1] and vals[i] < vals[i + 1]: imin = i; break
    assert imin is not None
    L3 = max((vals[i] for i in range(imin + 1, len(vals))), key=lambda v: float(v.mid()))
    L3lo = L3.mid() - L3.rad()
    jmax = max(range(imin + 1, len(vals)), key=lambda i: float(vals[i].mid()))
    say(f"l_3 >= {L3lo.str(10)} (A_3/phi at X = {pts[jmax]}, after a certified local minimum in ({pts[imin-1]}, {pts[imin+1]}))")
    ok3, U3, n3, _ = certify_sup(3, L3lo + arb("0.001"))
    assert ok3
    say(f"l_3 <= {U3.str(10)}  ({n3} intervals)  =>  l_3 in [{L3lo.str(6)}, {U3.str(6)}]")
    thr = L3lo
    # (c) R_q for all non-emerging q <= 20000; collect those not certified below l_3
    bad = []
    for q in range(3, 20001):
        if emerging(q): continue
        if not (R_q(q) < thr): bad.append(q)
    say(f"non-emerging q <= 20000 with R_q not certified < l_3: {len(bad)} moduli, largest {max(bad)}")
    say(f"  {bad[:40]} ...")
    # (b) direct certification for those (q = 3 is the maximiser itself)
    worst = (arb(-1), None); fails = []
    for q in bad:
        if q == 3: continue
        ok, U, ni, Ui = certify_sup(q, thr)
        if not ok: fails.append((q, U.str(6)))
        if float(Ui.mid()) > float(worst[0].mid()): worst = (Ui, q)
    say(f"direct certification: {len(bad) - 1 - len(fails)} / {len(bad) - 1} moduli certified with sup_{{X>=1/(2q)}} A_q/phi < l_3; failures {fails}")
    say(f"  largest interval bound on [1/(2q), X*] {worst[0].str(6)} at q = {worst[1]} (beyond X* the tail bound is used)")
    # (d) q > 20000
    th = Fr(7, 10); M = arb(1); used = []
    for p in primerange(2, 1000):
        f = 2 * arb(p) ** A_(th) / (p - 1)
        if not (f < 1):
            M *= ub(f) if ub(f) >= 1 else arb(1); used.append(p)
    Mup = ub(M)
    def g(qv): return ub(Mup * arb(qv) ** (-A_(th)) * (1 + arb(2).log() + arb(qv).log()) / 2)
    say(f"M_0.7 <= {Mup.str(8)} (primes {used}); bound at q = 20001: {g(20001).str(8)} < l_3: {g(20001) < thr}; decreasing in q for q >= 1")
    say(f"total time {time.time() - t0:.0f} s")
    open(sys.argv[1] if len(sys.argv) > 1 else "lobes_arb.txt", "w").write("\n".join(out) + "\n")
