#!/usr/bin/env python3
"""
Rigorous interval-arithmetic certificate (Arb via python-flint) of a zero of
L(s, chi) on the critical line Re s = 1/2, for chi = the cubic character mod 7
with chi(3) = omega = e^{2 pi i/3}  (even: chi(-1) = chi(6) = 1).

This is the input `CubicZero14` of Theorem S at q = 14 (Lean:
`ArcsAlgo.Classical.CubicZero14`): the characters of X(a/14) are the two cubic
characters mod 14, induced by chi and its conjugate, and
    L(s, chi_14) = L(s, chi) * (1 - chi(2) 2^{-s}),
so every zero of L(s, chi) is a zero of L(s, chi_14) (the Euler factor at 2 is
entire; only its own zeros, on Re s = 0, are added).

Method.  For primitive even chi mod q with Gauss sum tau(chi) and root number
eps = tau(chi)/sqrt(q), the Hardy function
    Z(t) = eps^{-1/2} (q/pi)^{i t/2} Gamma(1/4 + i t/2)/|Gamma(1/4 + i t/2)| L(1/2 + i t, chi)
is real for real t (functional equation; any fixed branch of eps^{-1/2}) and
continuous.  We evaluate Z with Arb balls at two exact rational points t1 < t2;
if the real balls Z(t1), Z(t2) have opposite strict signs (and the imaginary
parts are balls containing 0, as a consistency check), Z vanishes in (t1, t2)
by the intermediate value theorem, hence L(1/2 + i t0, chi) = 0 for some
t0 in (t1, t2).  L is evaluated exactly as q^{-s} sum_a chi(a) zeta(s, a/q)
(Hurwitz zeta, s != 1).

Usage: certify_zero_cubic7.py [prec_bits]
"""
import sys
from flint import arb, acb, ctx

PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 128
ctx.prec = PREC

Q = 7
half = arb(1) / 2
sqrt3h = arb(3).sqrt() / 2
omega = acb(-half, sqrt3h)
omega2 = acb(-half, -sqrt3h)
# chi(3) = omega; 3 generates (Z/7)^*: 3^1=3, 3^2=2, 3^3=6, 3^4=4, 3^5=5, 3^6=1
CHI = {1: acb(1), 3: omega, 2: omega2, 6: acb(1), 4: omega, 5: omega2}


def L(s):
    tot = acb(0)
    for a, v in CHI.items():
        tot += v * acb.zeta(s, acb(arb(a) / Q))
    return (-s * acb(Q).log()).exp() * tot


def gauss_sum():
    tau = acb(0)
    for a, v in CHI.items():
        tau += v * (acb(0, 2 * arb.pi() * a / Q)).exp()
    return tau


TAU = gauss_sum()
EPS = TAU / arb(Q).sqrt()
EPS_MHALF = EPS.sqrt() ** -1          # a fixed branch of eps^{-1/2}


def Z(t):
    t = arb(t)
    s = acb(half, t)
    g = acb(arb(1) / 4, t / 2).gamma()
    phase = (acb(0, t / 2) * (arb(Q) / arb.pi()).log()).exp() * g / abs(g)
    return EPS_MHALF * phase * L(s)


def scan(t_hi=30, step=arb(1) / 8):
    """Locate sign changes of Re Z on a grid (exploratory, not part of the proof)."""
    out, t, prev = [], arb(step), None
    while t < t_hi:
        z = Z(t).real.mid()
        if prev is not None and (prev > 0) != (z > 0):
            out.append((t - step, t))
        prev, t = z, t + step
    return out


def certify(t1, t2):
    z1, z2 = Z(t1), Z(t2)
    ok_imag = z1.imag.contains(0) and z2.imag.contains(0)
    opp = (z1.real > 0 and z2.real < 0) or (z1.real < 0 and z2.real > 0)
    return z1, z2, ok_imag, opp


if __name__ == "__main__":
    print(f"Arb working precision: {PREC} bits")
    print(f"|eps| = {abs(EPS)} (must contain 1)")
    assert abs(EPS).contains(1), "root number of modulus 1 expected"
    changes = scan()
    print("grid sign changes of Re Z(t) on (0, 30), step 1/8:", [(float(a.mid()), float(b.mid())) for a, b in changes])
    t1, t2 = changes[0]
    # refine to an exact rational bracket of width 1/1024 by bisection on midpoints, then certify the ends
    lo, hi = arb(t1.mid()), arb(t2.mid())
    for _ in range(7):
        mid = (lo + hi) / 2
        if (Z(mid).real.mid() > 0) == (Z(lo).real.mid() > 0):
            lo = mid
        else:
            hi = mid
    z1, z2, ok_imag, opp = certify(lo, hi)
    print(f"t1 = {lo.mid().str(20)}  Z(t1) = {z1}")
    print(f"t2 = {hi.mid().str(20)}  Z(t2) = {z2}")
    print(f"imaginary parts contain 0: {ok_imag};  real parts of strictly opposite sign: {opp}")
    assert ok_imag and opp, "certificate failed"
    print("CERTIFIED: L(1/2 + i t, chi) = 0 for some t in (t1, t2), chi cubic mod 7, chi(3) = omega.")
    print("Lean hypothesis CubicZero14 uses the closed interval [t1, t2] above, rounded outward.")
