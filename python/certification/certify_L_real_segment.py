#!/usr/bin/env python3
"""
Rigorous interval-arithmetic certification (Arb via python-flint) that
L(sigma, chi) != 0 for all real sigma in [1/2, 1], for
  (1) chi_5  = Legendre symbol mod 5          (real, even)   -> L > 0
  (2) chi_7  = cubic character mod 7, chi(3) = omega = e^{2 pi i/3}
  (3) chi_8  = even real character mod 8 (chi(1)=chi(7)=1, chi(3)=chi(5)=-1) -> L > 0

Representation (exact, pole-free):
  L(s,chi) = q^{-s} * sum_{a=1}^{q} chi(a) * Z(s, a/q),
  Z(s,x) := zeta(s,x) - 1/(s-1)   (Arb "deflated" Hurwitz zeta, entire in s).
Because sum_a chi(a) = 0 for non-principal chi, the 1/(s-1) terms cancel
identically, so this is exactly L(s,chi) for every s including s = 1, and
Arb can evaluate it on balls containing 1.

Enclosure on a box I = [c-r, c+r] (mean-value form):
  L(I) subset L(c) + L'(I) * [-r, r],
where L(c) is evaluated at the exact dyadic point c and L'(I) is an Arb
enclosure of the derivative over the whole ball I (via acb_series, order 2).
Box is accepted if the resulting complex rectangle excludes 0; otherwise
bisect.  Character values are exact algebraic numbers entered as Arb balls
(omega = -1/2 + i sqrt(3)/2).
"""
import sys
from flint import arb, acb, acb_series, ctx

PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 128
TIGHT = arb(sys.argv[2]) if len(sys.argv) > 2 else arb('0.99')
ctx.prec = PREC

half = arb(1) / 2
sqrt3h = arb(3).sqrt() / 2
omega = acb(-half, sqrt3h)        # e^{2 pi i / 3}
omega2 = acb(-half, -sqrt3h)      # omega^2

CHARS = {
    "chi5 (Legendre mod 5)": (5, {1: acb(1), 2: acb(-1), 3: acb(-1), 4: acb(1)}, True),
    "chi7 (cubic mod 7, chi(3)=omega)": (7, {1: acb(1), 3: omega, 2: omega2, 6: acb(1),
                                              4: omega, 5: omega2}, False),
    "chi8 (even real mod 8)": (8, {1: acb(1), 3: acb(-1), 5: acb(-1), 7: acb(1)}, True),
}


def L_series(sball, q, chi, deflate=1):
    """Return (L(s), L'(s)) enclosures for s an acb ball (series in x, order 2).
    deflate=1: uses Z(s,x)=zeta(s,x)-1/(s-1) (valid at exact points incl. s=1);
    deflate=0: plain Hurwitz zeta (valid on any ball not containing s=1)."""
    S = acb_series([sball, 1], prec=2)
    logq = acb(q).log()
    F = acb_series([0], prec=2)
    for a, v in chi.items():
        F += v * acb_series.zeta(S, acb(arb(a) / q), deflate=deflate)
    Lser = (-S * logq).exp() * F
    return Lser[0], Lser[1]


def L_value(s, q, chi):
    return L_series(acb(s), q, chi)[0]


def rect_min_modulus(z):
    """Rigorous lower bound for |w| over the rectangle enclosed by acb z."""
    def dist(x):
        lo, hi = x.lower(), x.upper()
        if lo > 0:
            return lo
        if hi < 0:
            return -hi
        return arb(0)
    dx, dy = dist(z.real), dist(z.imag)
    m = (dx * dx + dy * dy).sqrt()
    return arb(m.lower())  # lower endpoint


def cauchy_end_box(q, chi, real_char, R=arb(1) / 4, rho=arb(2) ** -8, N=256):
    """Treat the end box [1-rho, 1] rigorously.
    M := sup_{|s-1|=R} |L(s,chi)| is enclosed by covering the circle with N
    complex balls (centers on the circle, radius >= half arc length) and using
    the plain Hurwitz zeta (the circle stays at distance R from the pole).
    Cauchy: for |z-1| <= rho < R, |L'(z)| <= M R / (R - rho)^2.
    Mean value: L([1-rho,1]) subset L(1) + [-rho, 0] * sup|L'|  (as a disc
    of radius rho*B around L(1) in the complex case).
    L(1) is computed at the exact point s=1 with the deflated zeta."""
    pi = arb.pi()
    M = arb(0)
    rad = (R * pi / N) * 2  # generous ball radius covering each arc
    for k in range(N):
        th = 2 * pi * k / N
        center = acb(1 + R * th.cos(), R * th.sin())
        sball = acb(arb(center.real.mid(), rad.upper()), arb(center.imag.mid(), rad.upper()))
        val = acb(0)
        for a, v in chi.items():
            val += v * acb.zeta(sball, acb(arb(a) / q))
        val *= (-sball * acb(q).log()).exp()
        u = arb(abs(val).upper())
        assert u.is_finite()
        if u > M:
            M = u
    B = M * R / ((R - rho) ** 2)
    L1 = L_value(arb(1), q, chi)
    if real_char:
        lowb = arb((L1.real - rho * B).lower())
    else:
        lowb = arb((abs(L1) - rho * B).lower())
    return lowb, M, B, L1


def certify(name, q, chi, real_char, lo=arb(1) / 2, hi=arb(1), min_rad=arb(2) ** -40):
    stack = [(lo, hi)]
    boxes = 0
    minbound = None
    minbox = None
    while stack:
        a, b = stack.pop()
        c = (a + b) / 2
        r = (b - a) / 2
        Ic = acb(arb(c.mid(), r.upper()))
        Lc = L_value(c, q, chi)
        _, dL = L_series(Ic, q, chi, deflate=0)
        enc = Lc + dL * acb(arb(0, r.upper()))
        if real_char:
            # imaginary part is identically 0; certify real part > 0
            ok = enc.real.lower() > 0
            bound = arb(enc.real.lower()) if ok else None
        else:
            bound = rect_min_modulus(enc)
            ok = bound > 0
        # tightness: also demand the box bound be >= TIGHT * |L(c)|, so the
        # reported minimum is close to the true minimum of |L| on [1/2,1]
        if ok and r > min_rad * 2 ** 20:
            ok = bound > TIGHT * arb(abs(Lc).lower())
        if ok:
            boxes += 1
            if minbound is None or bound < minbound:
                minbound, minbox = bound, (a, b)
        else:
            if r < min_rad:
                raise RuntimeError(f"{name}: failed to certify near {c}")
            stack.append((c, b))
            stack.append((a, c))
    return boxes, minbound, minbox


if __name__ == "__main__":
    print(f"Arb working precision: {PREC} bits")
    for name, (q, chi, real_char) in CHARS.items():
        assert len(chi) == len([a for a in range(1, q) if __import__('math').gcd(a, q) == 1])
        rho = arb(2) ** -8
        endb, M, B, L1 = cauchy_end_box(q, chi, real_char, rho=rho)
        assert endb > 0, (name, endb)
        boxes, mb, (a, b) = certify(name, q, chi, real_char, hi=1 - rho)
        print(f"\n{name}: end box [1-2^-8, 1] via Cauchy: M=sup|L| on |s-1|=1/4 <= "
              f"{M.mid().str(6, radius=False)}, |L'| <= {B.mid().str(6, radius=False)}, "
              f"lower bound {endb.mid().str(10, radius=False)}")
        boxes += 1
        if endb < mb:
            mb, a, b = endb, 1 - rho, arb(1)
        what = "L(sigma) >" if real_char else "|L(sigma)| >="
        print(f"\n{name}: CERTIFIED on [1/2, 1] with {boxes} boxes")
        print(f"  min certified lower bound: {what} {mb.mid().str(10, radius=False)}"
              f"  (attained on box [{a.str(8, radius=False)}, {b.str(8, radius=False)}])")
        for s in ["0.5", "0.75", "1"]:
            print(f"  L({s}) = {L_value(arb(s), q, chi).str(20)}")
